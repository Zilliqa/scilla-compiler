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

(* open Result.Let_syntax *)
open Scilla_base.MonadUtil
open Scilla_base.GasCharge

(* Given a resolver that tries to resolve a string into
 * an identifier (with type annotation), and a gas charge,
 * generate code in builder to provide a final i64 LLVM value
 * that totals the gas charge. 
 * We use try resolver because some identifiers may no longer
 * exist (after optimization) and in such cases, we use 0 for it. *)
let gen_gas_charge llmod builder td_resolver id_resolver try_resolver g =
  let ctx = Llvm.module_context llmod in
  let recurser g =
    match g with
    | StaticCost i -> pure @@ Llvm.const_int (Llvm.i64_type ctx) i
    | SizeOf v -> (
        match try_resolver v with
        | Some vid ->
            SRTL.build_sizeof builder td_resolver id_resolver llmod vid
        | None -> pure @@ Llvm.const_int (Llvm.i64_type ctx) 0 )
    | ValueOf _ | LengthOf _ | MapSortCost _ | SumOf _ | ProdOf _ | MinOf _
    | DivCeil _ | LogOf _ ->
        fail0 "Unimplemented"
  in
  recurser g
