(*
  This file is part of scilla.

  Copyright (c) 2021 - present Zilliqa Research Pvt. Ltd.
  
  scilla is free software: you can redistribute it and/or modify it under the
  terms of the GNU General Public License as published by the Free Software
  Foundation, either version 3 of the License, or (at your option) any later
  version.
 
  scilla is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
  A PARTICULAR PURPOSE.  See the GNU General Public License for more details.
 
  You should have received a copy of the GNU General Public License along with
*)

(* Evaluate library entries to the extent possible, so that we have less to
 * do during an actual execution. Returns evaluated library with entries
 * replaced by their evaluated literal. 
 *)

open Scilla_base
open Core_kernel
open Result.Let_syntax
open MonadUtil
open Scilla_eval
open EvalUtil
open EvalIdentifier
open EvalLiteral


(* Does a literal contain runtime closure?
 * if so then it can't be part of the rewritten AST. *)
let rec has_runtime_clo l =
  match l with
  | IntLit _ | UintLit _ | StringLit _ | BNum _ | ByStr _ | ByStrX _ | Msg _ ->
      false
  | Map (_, m) ->
      Caml.Hashtbl.fold (fun _k v accb -> accb || has_runtime_clo v) m false
  | ADTValue (_, _, ls) -> List.exists ls ~f:has_runtime_clo
  | Clo _ -> true
  | TAbs _ -> true

let eval_lib_entry env id e remaining_gas =
  let%bind (res, _), remaining_gas =
    Eval.exp_eval_wrapper_no_cps e env Eval.init_gas_kont remaining_gas
  in
  pure (res, Env.bind env (get_id id) res, remaining_gas)

let eval_lib_entries env libs remaining_gas =
  let open EvalGas.GasSyntax in
  let open Stdint in
  let%bind (env', remaining_gas'), lentries' =
    fold_mapM
      ~f:(fun (accenv, acc_remaining_gas) lentry ->
        match lentry with
        | LibTyp _ -> pure ((accenv, acc_remaining_gas), lentry)
        | LibVar (lname, ltopt, ((le, lrep) as lexp)) ->
            let%bind llit, env', remaining_gas' =
              eval_lib_entry accenv lname lexp acc_remaining_gas
            in
            let consumed_gas =
              Uint64.to_int (Uint64.sub acc_remaining_gas remaining_gas')
            in
            let llit' =
              if has_runtime_clo llit then le
              else GasExpr (StaticCost consumed_gas, (Literal llit, lrep))
            in
            pure ((env', remaining_gas'), LibVar (lname, ltopt, (llit', lrep))))
      ~init:(env, remaining_gas) libs.lentries
  in
  pure (env', { libs with lentries = lentries' }, remaining_gas')

(* let init_libraries rlibs elibs clibs = *)
