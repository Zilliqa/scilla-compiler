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
  let i64_zero = Llvm.const_int (Llvm.i64_type ctx) 0 in
  let i64_one = Llvm.const_int (Llvm.i64_type ctx) 1 in
  let rec recurser g =
    match g with
    | StaticCost i -> pure @@ Llvm.const_int (Llvm.i64_type ctx) i
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
                let%bind v_ll = id_resolver (Some builder) vid in
                (* Extarct the integer component from the wrapper type { iX }. *)
                let%bind v_int =
                  LLGenUtils.build_extractvalue v_ll 0 (tempname "valueof")
                    builder
                in
                pure
                @@ Llvm.build_zext v_int (Llvm.i64_type ctx)
                     (tempname "valueof") builder
            | _ ->
                fail0
                  "GenLlvm: GasChargeGen: ValueOf supported only on Uint32 \
                   types")
        | None -> pure @@ i64_zero)
    | LengthOf v -> (
        match try_resolver v with
        | Some vid ->
            SRTL.build_lengthof builder td_resolver id_resolver llmod vid
        | None -> pure @@ i64_zero)
    | MapSortCost m -> (
        match try_resolver m with
        | Some (Identifier.Ident (_, { ea_tp = Some (MapType _); _ }) as mid) ->
            SRTL.build_mapsortcost builder id_resolver llmod mid
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
        let%bind g2_ll = recurser g2 in
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
    | LogOf v -> (
        let i32_ty = Llvm.integer_type ctx 32 in
        let i128_ty = Llvm.integer_type ctx 128 in
        let i256_ty = Llvm.integer_type ctx 256 in
        let f32_ty = Llvm.float_type ctx in
        match try_resolver v with
        | Some vid -> (
            (* Implements: static_cast<uint64_t>(log(v_f32 +. 1.0)) *)
            let gen_log v_f32 =
              let%bind () =
                LLGenUtils.ensure
                  Poly.(Llvm.type_of v_f32 = f32_ty)
                  "GenLlvm: GasChargeGen: LogOf: gen_log: Argument must f32"
              in
              let v_f32_1 =
                Llvm.build_fadd v_f32
                  (Llvm.const_float f32_ty 1.0)
                  (tempname "gaslogof") builder
              in
              let%bind logf = LLGenUtils.decl_f32_log llmod in
              let v_f32_1_log =
                Llvm.build_call logf [| v_f32_1 |] (tempname "gaslogof") builder
              in
              pure
              @@ Llvm.build_fptoui v_f32_1_log (Llvm.i64_type ctx)
                   (tempname "gaslogof") builder
            in
            let ui256_to_fp32 v_ui256 =
              let%bind () =
                LLGenUtils.ensure
                  Poly.(Llvm.type_of v_ui256 = i256_ty)
                  "GenLlvm: GasChargeGen: LogOf: ui256_to_fp32: Argument must \
                   be of type i256"
              in
              let vmem =
                Llvm.build_alloca i256_ty (tempname "gaslogof") builder
              in
              let _tmp_store = Llvm.build_store v_ui256 vmem builder in
              (* Cast vmem to i128* to access lower and upper halfs separately. *)
              let v128_higher_p =
                Llvm.build_bitcast vmem
                  (Llvm.pointer_type i128_ty)
                  (tempname "gaslogof") builder
              in
              let v128_lower_p =
                Llvm.build_gep v128_higher_p
                  [| Llvm.const_int i32_ty 1 |]
                  (tempname "gaslogof") builder
              in
              (* Mimic the below definition used in Integer256.ml for to_float:
                   let to_float ui =
                     Uint128.to_float ui.high *. (2.0 ** 128.0)) +. Uint128.to_float ui.low
              *)
              let v128_higher =
                Llvm.build_load v128_higher_p (tempname "gaslogof") builder
              in
              let v128_lower =
                Llvm.build_load v128_lower_p (tempname "gaslogof") builder
              in
              let v128_higher_f32 =
                Llvm.build_uitofp v128_higher f32_ty (tempname "gaslogof")
                  builder
              in
              let v128_lower_f32 =
                Llvm.build_uitofp v128_lower f32_ty (tempname "gaslogof")
                  builder
              in
              let%bind powf = LLGenUtils.decl_f32_pow llmod in
              let pow_2_128 =
                Llvm.build_call powf
                  [|
                    Llvm.const_float f32_ty 2.0; Llvm.const_float f32_ty 128.0;
                  |]
                  (tempname "gaslogf") builder
              in
              let mulr =
                Llvm.build_fmul v128_higher_f32 pow_2_128 (tempname "gaslogof")
                  builder
              in
              pure
              @@ Llvm.build_fadd mulr v128_lower_f32 (tempname "gaslogof")
                   builder
            in
            let%bind v_ll = id_resolver (Some builder) vid in
            match%bind LoweringUtils.id_typ vid with
            | PrimType (PrimType.Uint_typ Bits32)
            | PrimType (PrimType.Uint_typ Bits64)
            | PrimType (PrimType.Uint_typ Bits128) ->
                (* Extract the integer component from the wrapper type { iX }. *)
                let%bind v_int =
                  LLGenUtils.build_extractvalue v_ll 0 (tempname "gaslogof")
                    builder
                in
                let v_f32 =
                  Llvm.build_uitofp v_int (Llvm.float_type ctx)
                    (tempname "gaslogof") builder
                in
                gen_log v_f32
            | PrimType (PrimType.Uint_typ Bits256) ->
                (* Extract the integer component from the wrapper type { iX }. *)
                let%bind v_int =
                  LLGenUtils.build_extractvalue v_ll 0 (tempname "gaslogof")
                    builder
                in
                let%bind v_f32 = ui256_to_fp32 v_int in
                gen_log v_f32
            | PrimType (PrimType.Bystrx_typ w)
              when w = Scilla_crypto.Snark.scalar_len ->
                (* Cast the [i8 * 32] into i256 for processing it as i256. *)
                let v_i256 =
                  Llvm.build_bitcast v_ll i256_ty (tempname "gaslogof") builder
                in
                (* Byte strings in Scilla are expected to encode a
                 * big-endian integer, so reverse that. *)
                let%bind bswapf = LLGenUtils.decl_i256_bswap llmod in
                let v_i256_end =
                  Llvm.build_call bswapf [| v_i256 |] (tempname "gaslogof")
                    builder
                in
                let%bind v_f32 = ui256_to_fp32 v_i256_end in
                gen_log v_f32
            | _ ->
                fail0
                  "GenLlvm: GasChargeGen: LogOf supported only on unsigned \
                   integer compatible types")
        | None -> pure @@ i64_zero)
  in
  recurser g
