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
        match try_resolver v with
        | Some vid -> (
            match%bind LoweringUtils.id_typ vid with
            | PrimType (PrimType.Uint_typ _) ->
                (* Implements the OCaml operation
                   Float.to_int @@ Float.log (v +. 1.0) *)
                let%bind logf = LLGenUtils.decl_f32_log llmod in
                let%bind v_ll = id_resolver (Some builder) vid in
                (* Extarct the integer component from the wrapper type { iX }. *)
                let%bind v_int =
                  LLGenUtils.build_extractvalue v_ll 0 (tempname "gaslogof")
                    builder
                in
                let v_f32 =
                  Llvm.build_uitofp v_int (Llvm.float_type ctx)
                    (tempname "gaslogof") builder
                in
                let v_log =
                  Llvm.build_call logf [| v_f32 |] (tempname "gaslogof") builder
                in
                let v_log_1 =
                  Llvm.build_fadd v_log
                    (Llvm.const_float (Llvm.float_type ctx) 1.0)
                    (tempname "gaslogof") builder
                in
                pure
                @@ Llvm.build_fptoui v_log_1 (Llvm.i64_type ctx)
                     (tempname "gaslogof") builder
            | PrimType (PrimType.Bystrx_typ w)
              when w = Scilla_crypto.Snark.scalar_len ->
                fail0 "Unimplemented"
            | _ ->
                fail0
                  "GenLlvm: GasChargeGen: LogOf supported only on unsigned \
                   integer compatible types")
        | None -> pure @@ i64_zero)
  in
  recurser g
