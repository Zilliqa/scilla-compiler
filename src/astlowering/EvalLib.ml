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
open ErrorUtils
open EvalUtil
open EvalIdentifier
open EvalLiteral
open EvalTypeUtilities
open EvalSyntax

type libeval_env = (Name.t * libeval_res) list

and libeval_res =
  | ELLiteral of EvalLiteral.t
  | ELClo of expr_annot * libeval_env
  | ELTAbs of expr_annot * libeval_env

let rec exp_eval erep env =
  let open EvalSyntax in
  let open PatternMatching in
  let e, loc = erep in
  let translate_env leenv =
    mapM leenv ~f:(fun (name, l) ->
        (* TODO: This function shouldn't be used,
         * It's use is unnecessarily inefficient. *)
        match l with
        | ELLiteral l -> pure (name, l)
        | _ -> fail0 "Unexpected closure")
  in
  match e with
  | Literal l -> pure (ELLiteral (Eval.replace_address_types l), env)
  | Var i ->
      let%bind v = Env.lookup env i in
      pure @@ (v, env)
  | Let (i, _, lhs, rhs) ->
      let%bind lval, _ = exp_eval lhs env in
      let env' = Env.bind env (get_id i) lval in
      exp_eval rhs env'
  | Message bs ->
      (* Resolve all message payload *)
      let resolve pld =
        match pld with
        | MLit l -> Eval.sanitize_literal l
        | MVar i -> (
            let open Result.Let_syntax in
            match%bind Env.lookup env i with
            | ELLiteral v -> Eval.sanitize_literal v
            | _ -> fail0 "Message cannot have closures.")
      in
      let%bind payload_resolved =
        (* Make sure we resolve all the payload *)
        mapM bs ~f:(fun (s, pld) ->
            let%bind sanitized_lit = resolve pld in
            (* Messages should contain simplified types, so use literal_type *)
            let%bind t = literal_type sanitized_lit in
            pure (s, t, sanitized_lit))
      in
      pure (ELLiteral (Msg payload_resolved), env)
  | App (f, actuals) ->
      (* Resolve the actuals *)
      let%bind args = mapM actuals ~f:(fun arg -> Env.lookup env arg) in
      let%bind ff = Env.lookup env f in
      (* Apply iteratively, also evaluating curried lambdas *)
      let%bind fully_applied =
        List.fold_left args ~init:(pure ff) ~f:(fun res arg ->
            let%bind v = res in
            try_apply_as_closure v arg)
      in
      pure (fully_applied, env)
  | Constr (cname, ts, actuals) ->
      let open Datatypes.DataTypeDictionary in
      let%bind _, constr =
        lookup_constructor ~sloc:(SR.get_loc (get_rep cname)) (get_id cname)
      in
      let alen = List.length actuals in
      if constr.arity <> alen then
        fail1
          (sprintf "Constructor %s expects %d arguments, but got %d."
             (as_error_string cname) constr.arity alen)
          (SR.get_loc (get_rep cname))
      else
        (* Resolve the actuals *)
        let%bind args =
          mapM actuals ~f:(fun arg ->
              match%bind Env.lookup env arg with
              | ELLiteral l -> pure l
              | _ -> fail0 "Unexpected closure.")
        in
        (* Make sure we only pass "pure" literals, not closures *)
        let lit = ADTValue (get_id cname, ts, args) in
        pure (ELLiteral (Eval.replace_address_types lit), env)
  | MatchExpr (x, clauses) -> (
      match%bind Env.lookup env x with
      | ELLiteral v ->
          (* Get the branch and the bindings *)
          let%bind (_, e_branch), bnds =
            tryM clauses
              ~msg:(fun () ->
                mk_error1
                  (sprintf "Match expression failed. No clause matched.")
                  loc)
              ~f:(fun (p, _) -> match_with_pattern v p)
          in
          (* Update the environment for the branch *)
          let env' =
            List.fold_left bnds ~init:env ~f:(fun z (i, w) ->
                Env.bind z (get_id i) (ELLiteral w))
          in
          exp_eval e_branch env'
      | _ -> fail0 "Unexpected closure.")
  | Builtin (i, targs, actuals) ->
      let%bind env' = translate_env env in
      let%bind res, _cost = Eval.builtin_executor env' i targs actuals in
      let%bind res' = res () in
      pure (ELLiteral res', env)
  | TApp (tf, arg_types) ->
      let%bind ff = Env.lookup env tf in
      let%bind fully_applied =
        List.fold_left arg_types ~init:(pure ff) ~f:(fun res arg_type ->
            let%bind v = res in
            try_apply_as_type_closure v arg_type)
      in
      pure (fully_applied, env)
  | GasExpr (g, e') ->
      let%bind env' = translate_env env in
      let%bind _cost = Eval.eval_gas_charge env' g in
      let%bind res, _ = exp_eval e' env in
      pure (res, env)
  | Fun _ | Fixpoint _ -> pure (ELClo (erep, env), env)
  | TFun _ -> pure (ELTAbs (erep, env), env)

(* Applying a function *)
and try_apply_as_closure v arg =
  match v with
  | ELClo ((Fun (formal, _, body), _), env) ->
      let env1 = Env.bind env (get_id formal) arg in
      fstM @@ exp_eval body env1
  | ELClo ((Fixpoint (g, _, body), _), env) ->
      let env1 = Env.bind env (get_id g) v in
      fstM @@ exp_eval body env1
  | _ -> fail0 "Not a functional value."

and try_apply_as_type_closure v arg_type =
  match v with
  | ELTAbs ((TFun (tv, body), _), env) ->
      let body_subst = subst_type_in_expr tv arg_type body in
      fstM @@ exp_eval body_subst env
  | _ -> fail0 "Not a type closure."

let rec rewrite_runtime_closures = function
  | ELLiteral l -> pure (Literal l)
  | _ -> fail0 ""

let eval_lib_entry env id e remaining_gas =
  let%bind res, _ = exp_eval e env in
  pure (res, Env.bind env (get_id id) res, remaining_gas)

let eval_lib_entries env libs remaining_gas =
  let open EvalGas.GasSyntax in
  let open Stdint in
  let%bind (env', remaining_gas'), lentries' =
    fold_mapM
      ~f:(fun (accenv, acc_remaining_gas) lentry ->
        match lentry with
        | LibTyp _ -> pure ((accenv, acc_remaining_gas), lentry)
        | LibVar (lname, ltopt, ((_, lrep) as lexp)) ->
            let%bind llit, env', remaining_gas' =
              eval_lib_entry accenv lname lexp acc_remaining_gas
            in
            let consumed_gas =
              Uint64.to_int (Uint64.sub acc_remaining_gas remaining_gas')
            in
            let%bind lexp' = rewrite_runtime_closures llit in
            pure
              ( (env', remaining_gas'),
                LibVar
                  ( lname,
                    ltopt,
                    (GasExpr (StaticCost consumed_gas, (lexp', lrep)), lrep) )
              ))
      ~init:(env, remaining_gas) libs.lentries
  in
  pure (env', { libs with lentries = lentries' }, remaining_gas')

(* let init_libraries rlibs elibs clibs = *)
