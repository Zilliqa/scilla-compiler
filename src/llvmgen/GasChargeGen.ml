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
  let rec recurser g =
    match g with
    | StaticCost i -> pure @@ Llvm.const_int (Llvm.i64_type ctx) i
    | SizeOf v -> (
        match try_resolver v with
        | Some vid ->
            SRTL.build_literal_cost builder td_resolver id_resolver llmod vid
        | None -> pure @@ Llvm.const_int (Llvm.i64_type ctx) 0)
    | ValueOf v -> (
        match try_resolver v with
        | Some vid -> (
            match%bind LoweringUtils.id_typ vid with
            | PrimType (PrimType.Uint_typ PrimType.Bits32) ->
                let%bind v_ll = id_resolver (Some builder) vid in
                pure
                @@ Llvm.build_zext v_ll (Llvm.i64_type ctx) (tempname "valueof")
                     builder
            | _ ->
                fail0
                  "GenLlvm: GasChargeGen: ValueOf supported only on Uint32 \
                   types")
        | None -> pure @@ Llvm.const_int (Llvm.i64_type ctx) 0)
    | LengthOf v -> (
        match try_resolver v with
        | Some vid ->
            SRTL.build_lengthof builder td_resolver id_resolver llmod vid
        | None -> pure @@ Llvm.const_int (Llvm.i64_type ctx) 0)
    | MapSortCost m -> (
        match try_resolver m with
        | Some (Identifier.Ident (_, { ea_tp = Some (MapType _); _ }) as mid) ->
            SRTL.build_mapsortcost builder id_resolver llmod mid
        | _ -> pure @@ Llvm.const_int (Llvm.i64_type ctx) 0)
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
    | DivCeil _ | LogOf _ -> fail0 "Unimplemented"
  in
  recurser g
