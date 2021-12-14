(*
  This file is part of scilla.

  Copyright (c) 2020 - present Zilliqa Research Pvt. Ltd.
  
  scilla is free software: you can redistribute it and/or modify it under the
  terms of the GNU General Public License as published by the Free Software
  Foundation, either version 3 of the License, or (at your option) any later
  version.
 
  scilla is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
  A PARTICULAR PURPOSE.  See the GNU General Public License for more details.
 
  You should have received a copy of the GNU General Public License along with
*)

open Core_kernel
open Result.Let_syntax
open LoweringUtils
open Scilla_base
open MonadUtil
module PrimType = Type.PrimType
module Literal = Literal.GlobalLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier

open GasCharge.ScillaGasCharge (Identifier.Name)

(* Given a resolver that tries to resolve a string into
 * an identifier (with type annotation), and a gas charge,
 * generate code in builder to provide a final i64 LLVM value
 * that totals the gas charge. 
 * We use try resolver because some identifiers may no longer
 * exist (after optimization) and in such cases, we use 0 for it. *)
let gen_gas_charge llmod builder td_resolver id_resolver try_resolver g =
  let ctx = Llvm.module_context llmod in
  let i64_ty = Llvm.i64_type ctx in
  let i64_zero = Llvm.const_int i64_ty 0 in
  let i64_one = Llvm.const_int i64_ty 1 in
  let rec recurser g =
    match g with
    | StaticCost i -> pure @@ Llvm.const_int i64_ty i
    | SizeOf v -> (
        match try_resolver v with
        | Some vid ->
            SRTL.build_literal_cost builder td_resolver id_resolver llmod vid
        | None -> pure @@ i64_zero)
    | ValueOf v -> (
        match try_resolver v with
        | Some vid -> (
            match%bind LoweringUtils.id_typ vid with
            | PrimType (PrimType.Uint_typ PrimType.Bits32) ->
                (* Uint32 values may be directly used in gas computations.
                 * Since gas computations (almost all) work on i64, upcast. *)
                let%bind v_ll = id_resolver (Some builder) vid in
                (* Extarct the integer component from the wrapper type { iX }. *)
                let%bind v_int =
                  LLGenUtils.build_extractvalue v_ll 0 (tempname "valueof")
                    builder
                in
                pure
                @@ Llvm.build_zext v_int i64_ty (tempname "valueof") builder
            | PrimType (PrimType.Uint_typ PrimType.Bits64)
            | PrimType (PrimType.Uint_typ PrimType.Bits128)
            | PrimType (PrimType.Uint_typ PrimType.Bits256) ->
                (* These values can only be used in a LogOf computation.
                 * Let's just pass them on as it is to be extracted there.
                 * If used else where, we'll have an LLVM type error. *)
                id_resolver (Some builder) vid
            | _ ->
                fail0
                  "GenLlvm: GasChargeGen: ValueOf supported only on integer \
                   types")
        | None -> pure @@ i64_zero)
    | LengthOf v -> (
        match try_resolver v with
        | Some vid ->
            SRTL.build_lengthof builder td_resolver id_resolver llmod vid
        | None -> pure @@ i64_zero)
    | MapSortCost m -> (
        let rec type_contains_map = function
          | UncurriedSyntax.Uncurried_Syntax.MapType _ -> true
          | ADT (_, ts) -> List.exists ts ~f:type_contains_map
          | _ -> false
        in
        match try_resolver m with
        | Some (Identifier.Ident (_, { ea_tp = Some t; _ }) as mid)
          when type_contains_map t ->
            SRTL.build_mapsortcost builder td_resolver id_resolver llmod mid
        | _ -> pure @@ i64_zero)
    | SumOf (g1, g2) ->
        let%bind g1_ll = recurser g1 in
        let%bind g2_ll = recurser g2 in
        pure @@ Llvm.build_add g1_ll g2_ll (tempname "gasadd") builder
    | ProdOf (g1, g2) ->
        let%bind g1_ll = recurser g1 in
        let%bind g2_ll = recurser g2 in
        pure @@ Llvm.build_mul g1_ll g2_ll (tempname "gasmul") builder
    | MinOf (g1, g2) ->
        let%bind g1_ll = recurser g1 in
        let%bind g2_ll = recurser g2 in
        let%bind min_ll = LLGenUtils.decl_uint64_min llmod in
        pure
        @@ Llvm.build_call min_ll [| g1_ll; g2_ll |] (tempname "gasmin") builder
    | DivCeil (g1, g2) ->
        let%bind g1_ll = recurser g1 in
        let g2_ll = Llvm.const_int i64_ty (GasCharge.PositiveInt.get g2) in
        let rem = Llvm.build_urem g1_ll g2_ll (tempname "gasdivceil") builder in
        let div = Llvm.build_udiv g1_ll g2_ll (tempname "gasdivceil") builder in
        let rem_is_zero =
          Llvm.build_icmp Llvm.Icmp.Eq rem i64_zero (tempname "gasdivceil")
            builder
        in
        let div_plus_1 =
          Llvm.build_add div i64_one (tempname "gasdivceil") builder
        in
        pure
        @@ Llvm.build_select rem_is_zero div div_plus_1 (tempname "gasdivceil")
             builder
    | LogOf g ->
        let%bind g_ll = recurser g in
        let i32_ty = Llvm.integer_type ctx 32 in
        let i128_ty = Llvm.integer_type ctx 128 in
        let i256_ty = Llvm.integer_type ctx 256 in
        let f64_ty = Llvm.double_type ctx in
        (* Implements: static_cast<uint64_t>(log(v_f64 +. 1.0)) + 1 *)
        let gen_log v_f64 =
          let%bind () =
            LLGenUtils.ensure
              Poly.(Llvm.type_of v_f64 = f64_ty)
              "GenLlvm: GasChargeGen: LogOf: gen_log: Argument must f64"
          in
          let v_f64_1 =
            Llvm.build_fadd v_f64
              (Llvm.const_float f64_ty 1.0)
              (tempname "gaslogof") builder
          in
          let%bind logf = LLGenUtils.decl_f64_log llmod in
          let v_f64_1_log =
            Llvm.build_call logf [| v_f64_1 |] (tempname "gaslogof") builder
          in
          let ui =
            Llvm.build_fptoui v_f64_1_log i64_ty (tempname "gaslogof") builder
          in
          pure @@ Llvm.build_add ui i64_one (tempname "gaslogof") builder
        in
        let ui256_to_fp32 v_ui256 =
          let%bind () =
            LLGenUtils.ensure
              Poly.(Llvm.type_of v_ui256 = i256_ty)
              "GenLlvm: GasChargeGen: LogOf: ui256_to_fp32: Argument must be \
               of type i256"
          in
          let vmem = Llvm.build_alloca i256_ty (tempname "gaslogof") builder in
          let _tmp_store = Llvm.build_store v_ui256 vmem builder in
          (* Cast vmem to i128* to access lower and upper halfs separately.
           * (Assume little-endian target). *)
          let v128_lower_p =
            Llvm.build_bitcast vmem
              (Llvm.pointer_type i128_ty)
              (tempname "gaslogof") builder
          in
          let v128_higher_p =
            Llvm.build_gep v128_lower_p
              [| Llvm.const_int i32_ty 1 |]
              (tempname "gaslogof") builder
          in
          (* Mimic the below definition used in Integer256.ml for to_float:
               let to_double ui =
                 Uint128.to_double ui.high *. (2.0 ** 128.0)) +. Uint128.to_double ui.low
          *)
          let v128_higher =
            Llvm.build_load v128_higher_p (tempname "gaslogof") builder
          in
          let v128_lower =
            Llvm.build_load v128_lower_p (tempname "gaslogof") builder
          in
          let v128_higher_f64 =
            Llvm.build_uitofp v128_higher f64_ty (tempname "gaslogof") builder
          in
          let v128_lower_f64 =
            Llvm.build_uitofp v128_lower f64_ty (tempname "gaslogof") builder
          in
          let%bind powf = LLGenUtils.decl_f64_pow llmod in
          let pow_2_128 =
            Llvm.build_call powf
              [| Llvm.const_float f64_ty 2.0; Llvm.const_float f64_ty 128.0 |]
              (tempname "gaslogf") builder
          in
          let mulr =
            Llvm.build_fmul v128_higher_f64 pow_2_128 (tempname "gaslogof")
              builder
          in
          pure
          @@ Llvm.build_fadd mulr v128_lower_f64 (tempname "gaslogof") builder
        in
        let gty = Llvm.type_of g_ll in
        let%bind ui32_sty_ll =
          TypeLLConv.genllvm_typ_fst llmod (PrimType (PrimType.Uint_typ Bits32))
        in
        let%bind ui64_sty_ll =
          TypeLLConv.genllvm_typ_fst llmod (PrimType (PrimType.Uint_typ Bits64))
        in
        let%bind ui128_sty_ll =
          TypeLLConv.genllvm_typ_fst llmod
            (PrimType (PrimType.Uint_typ Bits128))
        in
        let%bind ui256_sty_ll =
          TypeLLConv.genllvm_typ_fst llmod
            (PrimType (PrimType.Uint_typ Bits256))
        in
        let%bind by256_sty_ll =
          TypeLLConv.genllvm_typ_fst llmod
            (PrimType (PrimType.Bystrx_typ Scilla_crypto.Snark.scalar_len))
        in
        (* Act based on the type of value we need to take LogOf. *)
        if
          Poly.equal gty ui32_sty_ll || Poly.equal gty ui64_sty_ll
          || Poly.equal gty ui128_sty_ll
          || Poly.equal gty i64_ty
        then
          let%bind v_int =
            if Poly.equal gty i64_ty then pure g_ll
            else
              (* Extract the integer component from the wrapper type { iX }. *)
              LLGenUtils.build_extractvalue g_ll 0 (tempname "gaslogof") builder
          in
          let v_f64 =
            Llvm.build_uitofp v_int (Llvm.double_type ctx) (tempname "gaslogof")
              builder
          in
          gen_log v_f64
        else if Poly.equal gty ui256_sty_ll then
          (* Extract the integer component from the wrapper type { iX }. *)
          let%bind v_int =
            LLGenUtils.build_extractvalue g_ll 0 (tempname "gaslogof") builder
          in
          let%bind v_f64 = ui256_to_fp32 v_int in
          gen_log v_f64
        else if Poly.equal gty by256_sty_ll then
          (* Cast the [i8 * 32] into i256 for processing it as i256. *)
          let v_i256 =
            Llvm.build_bitcast g_ll i256_ty (tempname "gaslogof") builder
          in
          (* Byte strings in Scilla are expected to encode a
           * big-endian integer, so reverse that. *)
          let%bind bswapf = LLGenUtils.decl_i256_bswap llmod in
          let v_i256_end =
            Llvm.build_call bswapf [| v_i256 |] (tempname "gaslogof") builder
          in
          let%bind v_f64 = ui256_to_fp32 v_i256_end in
          gen_log v_f64
        else
          fail0
            ("GenLlvm: GasChargeGen: LogOf supported only on unsigned integer \
              compatible types. Got " ^ Llvm.string_of_lltype gty)
  in
  recurser g
