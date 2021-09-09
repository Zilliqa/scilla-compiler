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

type libeval_literal =
  | StringLit of string
  (* Cannot have different integer literals here directly as Stdint does not derive sexp. *)
  | IntLit of int_lit
  | UintLit of uint_lit
  | BNum of string
  (* Byte string with a statically known length. *)
  | ByStrX of Bystrx.t
  (* Byte string without a statically known length. *)
  | ByStr of Bystr.t
  (* Message: an associative array *)
  | Msg of (string * LType.t * libeval_literal) list
  (* A dynamic map of literals *)
  | Map of mtype * (libeval_literal, libeval_literal) Caml.Hashtbl.t
  (* A constructor in HNF *)
  | ADTValue of LType.TIdentifier.Name.t * LType.t list * libeval_literal list
  (* An embedded closure *)
  | Clo of (expr_annot * libeval_env)
  (* A type abstraction *)
  | TAbs of (expr_annot * libeval_env)

and libeval_env = (Name.t * libeval_literal) list

(* This is a copy of the one in PatternMatching.ml
 * but works on libeval_literal instead. *)
let rec match_with_pattern v p =
  let open Datatypes in
  match p with
  | Wildcard -> pure []
  | Binder x -> pure @@ [ (x, v) ]
  | Constructor (cn, ps) -> (
      let%bind _, ctr =
        DataTypeDictionary.lookup_constructor
          ~sloc:(SR.get_loc (get_rep cn))
          (get_id cn)
      in
      (* Check that the pattern is well-formed *)
      if ctr.arity <> List.length ps then
        fail0
        @@ sprintf "Constructor %s requires %d parameters, but %d are provided."
             (EvalName.as_error_string ctr.cname)
             ctr.arity (List.length ps)
      else
        (* Pattern is well-formed, processing the value *)
        (* In this branch ctr.arity = List.length ps *)
        match v with
        | ADTValue (cn', _, ls')
          when [%equal: EvalName.t] cn' ctr.cname && List.length ls' = ctr.arity
          ->
            (* The value structure matches the pattern *)
            (* In this branch ctr.arity = List.length ps = List.length ls', so we can use zip_exn *)
            let%bind res_list =
              map2M ls' ps ~f:match_with_pattern ~msg:(fun () -> assert false)
            in
            (* Careful: there might be duplicate bindings! *)
            (* We will need to catch this statically. *)
            pure @@ List.concat res_list
        | _ -> fail0 "Cannot match value againts pattern.")

let rec to_libeval_literal = function
  | SLiteral.StringLit s -> pure @@ StringLit s
  | IntLit i -> pure @@ IntLit i
  | UintLit i -> pure @@ UintLit i
  | BNum b -> pure @@ BNum b
  | ByStrX b -> pure @@ ByStrX b
  | ByStr b -> pure @@ ByStr b
  | Msg mlist ->
      let%bind mlist' =
        mapM mlist ~f:(fun (m, t, l) ->
            let%bind l' = to_libeval_literal l in
            pure (m, t, l'))
      in
      pure @@ Msg mlist'
  | Map (mt, t) ->
      let open Caml in
      let t' = Hashtbl.create (Hashtbl.length t) in
      let tlist = Hashtbl.to_seq t |> List.of_seq in
      let%bind () =
        forallM tlist ~f:(fun (k, v) ->
            let%bind k' = to_libeval_literal k in
            let%bind v' = to_libeval_literal v in
            let () = Hashtbl.replace t' k' v' in
            pure ())
      in
      pure @@ Map (mt, t')
  | ADTValue (name, types, args) ->
      let%bind args' = mapM args ~f:to_libeval_literal in
      pure @@ ADTValue (name, types, args')
  | Clo _ -> fail0 "Cannot convert OCaml closures to Scilla closures"
  | TAbs _ -> fail0 "Cannot convert OCaml closures to Scilla type closures"

let rec from_libeval_literal = function
  | StringLit s -> pure @@ SLiteral.StringLit s
  | IntLit i -> pure @@ SLiteral.IntLit i
  | UintLit i -> pure @@ SLiteral.UintLit i
  | BNum b -> pure @@ SLiteral.BNum b
  | ByStrX b -> pure @@ SLiteral.ByStrX b
  | ByStr b -> pure @@ SLiteral.ByStr b
  | Msg mlist ->
      let%bind mlist' =
        mapM mlist ~f:(fun (m, t, l) ->
            let%bind l' = from_libeval_literal l in
            pure (m, t, l'))
      in
      pure @@ SLiteral.Msg mlist'
  | Map (mt, t) ->
      let open Caml in
      let t' = Hashtbl.create (Hashtbl.length t) in
      let tlist = Hashtbl.to_seq t |> List.of_seq in
      let%bind () =
        forallM tlist ~f:(fun (k, v) ->
            let%bind k' = from_libeval_literal k in
            let%bind v' = from_libeval_literal v in
            let () = Hashtbl.replace t' k' v' in
            pure ())
      in
      pure @@ SLiteral.Map (mt, t')
  | ADTValue (name, types, args) ->
      let%bind args' = mapM args ~f:from_libeval_literal in
      pure @@ SLiteral.ADTValue (name, types, args')
  | Clo _ ->
      let noexec _ = EvalMonad.fail0 "Unexpected evaluation of closure" in
      pure @@ SLiteral.Clo noexec
  | TAbs _ ->
      let noexec _ = EvalMonad.fail0 "Unexpected evaluation of type closure" in
      pure @@ SLiteral.TAbs noexec

(* Translate environment literals to Scilla_base type. *)
let translate_env env =
  mapM env ~f:(fun (name, lit) ->
      let%bind lit' = from_libeval_literal lit in
      pure (name, lit'))

let rec exp_eval erep env =
  let open EvalSyntax in
  let e, loc = erep in
  match e with
  | Literal l ->
      let%bind l' = to_libeval_literal l in
      pure (l', env)
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
        | MLit l -> to_libeval_literal l
        | MVar i -> Env.lookup env i
      in
      let%bind payload_resolved =
        (* Make sure we resolve all the payload *)
        mapM bs ~f:(fun (s, pld) ->
            let%bind lit = resolve pld in
            let%bind lit' = from_libeval_literal lit in
            (* Messages should contain simplified types, so use literal_type *)
            let%bind t = literal_type lit' in
            pure (s, t, lit))
      in
      pure (Msg payload_resolved, env)
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
        let%bind args = mapM actuals ~f:(Env.lookup env) in
        (* Make sure we only pass "pure" literals, not closures *)
        let lit = ADTValue (get_id cname, ts, args) in
        pure (lit, env)
  | MatchExpr (x, clauses) ->
      let%bind v = Env.lookup env x in
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
            Env.bind z (get_id i) w)
      in
      exp_eval e_branch env'
  | Builtin (i, targs, actuals) ->
      let%bind env' = translate_env env in
      let%bind res, _cost = Eval.builtin_executor env' i targs actuals in
      let%bind res' = res () in
      let%bind res'' = to_libeval_literal res' in
      pure (res'', env)
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
  | Fun _ | Fixpoint _ -> pure (Clo (erep, env), env)
  | TFun _ -> pure (TAbs (erep, env), env)

(* Applying a function *)
and try_apply_as_closure v arg =
  match v with
  | Clo ((Fun (formal, _, body), _), env) ->
      let env1 = Env.bind env (get_id formal) arg in
      fstM @@ exp_eval body env1
  | Clo ((Fixpoint (g, _, body), _), env) ->
      let env1 = Env.bind env (get_id g) v in
      fstM @@ exp_eval body env1
  | _ -> fail0 "Not a functional value."

and try_apply_as_type_closure v arg_type =
  match v with
  | TAbs ((TFun (tv, body), _), env) ->
      let body_subst = subst_type_in_expr tv arg_type body in
      fstM @@ exp_eval body_subst env
  | _ -> fail0 "Not a type closure."

let rec rewrite_runtime_closures _f = fail0 ""

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
