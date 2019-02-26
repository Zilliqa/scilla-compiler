(*
  This file is part of scilla.

  Copyright (c) 2019 - present Zilliqa Research Pvt. Ltd.
  
  scilla is free software: you can redistribute it and/or modify it under the
  terms of the GNU General Public License as published by the Free Software
  Foundation, either version 3 of the License, or (at your option) any later
  version.
 
  scilla is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
  A PARTICULAR PURPOSE.  See the GNU General Public License for more details.
 
  You should have received a copy of the GNU General Public License along with
*)

open TypeUtil
open Syntax
open MonadUtil
open Core.Result.Let_syntax
open MonomorphicSyntax

(* Translate ScillaSyntax to MonomorphicSyntax. *)
module ScillaCG_Mmph
    (SR : Rep)
    (ER : sig
       include Rep
       val get_type : rep -> PlainTypes.t inferred_type
     end) = struct

  module SER = SR
  module EER = ER
  module TU = TypeUtilities (SR) (ER)
  module TypedSyntax = ScillaSyntax (SR) (ER)
  module MS = MmphSyntax (SR) (ER)

  open TypedSyntax

  (*******************************************************)
  (* Gather possible instances of polymorphic functions  *)
  (*******************************************************)

  (* TODO: More precise analysis:
   *       "A Type- and Control-Flow Analysis for System F Technical Report" - Matthew Fluet. 
   * Currently we do only a little better than "all TApps flow to all TFuns". *)

  type tapps = typ list list

  (* Add a tapp to tracked list of instantiations. If "tapp" has a
   * TypeVar that is not in bound_tvars, return error. If the TypeVar is
   * bound, then it is tracked in the list as PolyFun(TypeVar) to make
   * simple to compare types using typ_equiv. *)
  let add_tapp (tenv : tapps) tapp bound_tvars lc =
    let%bind tapp' = mapM ~f:(fun t ->
      match t with
      | TypeVar tv ->
        if List.mem tv bound_tvars
        then pure @@PolyFun (tv, t)
        else fail1 "Monomorphize: Unbound type variable used in instantiation" lc
      | _ -> pure t) tapp in
    (* If tapp' doesn't exist in tenv, add it. *)
    let seen_before = List.exists (fun ta ->
      TU.type_equiv_list ta tapp'
    ) tenv in
    if seen_before then pure tenv else pure (tapp' :: tenv)

  (* Walk through "e" and add all TApps. *)
  let rec analyse_expr (e, erep) (tenv : tapps) (bound_tvars : string list) =
  match e with
  | Literal _ | Var _ |  Message _ | App _ 
  | Constr _ | Builtin _  -> pure tenv
  | Fixpoint (_, _, body) | Fun (_, _, body) -> analyse_expr body tenv bound_tvars
  | Let (_, _, lhs, rhs) ->
    let%bind tenv' = analyse_expr lhs tenv bound_tvars in
    analyse_expr rhs tenv' bound_tvars
  | MatchExpr (_, clauses) ->
    foldM ~f:(fun accenv (_, bre) ->
      let%bind tenv' = analyse_expr bre accenv bound_tvars in
      pure tenv'
    ) ~init:tenv clauses
  | TFun (v, e') -> analyse_expr e' tenv ((get_id v) :: bound_tvars)
  | TApp (_, tapp) -> add_tapp tenv tapp bound_tvars (ER.get_loc erep)

  (* Walk through statement list and add all TApps. *)
  let rec analyse_stmts stmts (tenv : tapps) =
  match stmts with
  | [] -> pure tenv
  | (s, _) :: sts ->
    (match s with
    | Load _ | Store _ | MapUpdate _ | MapGet _ | ReadFromBC _
    | AcceptPayment | SendMsgs _ | CreateEvnt _ | Throw _ ->
      analyse_stmts sts tenv
    | Bind (_ , e) ->
      let%bind tenv' = analyse_expr e tenv [] in
      analyse_stmts sts tenv'
    | MatchStmt (_, pslist) ->
      foldM ~f:(fun accenv (_, slist) ->
        let%bind tenv' = analyse_stmts slist accenv in
        pure tenv'
      ) ~init:tenv pslist
    )

  (* Walk through entire module, tracking TApps. *)
  let analyze_module (cmod : cmodule) rlibs elibs =
    let%bind rlib_env = foldM ~f:(fun accenv (_, e) ->
        analyse_expr e accenv []
    ) ~init:[] rlibs
    in

    (* Analyze external and contract libraries. *)
    let liblist =
      match cmod.libs with | Some clib -> elibs @ [clib] | None -> elibs
    in
    let%bind libs_env = foldM ~f:(fun accenv lib ->
      foldM ~f:(fun accenv lentry ->
        match lentry with
        | LibVar (_, lexp) ->
          let%bind tenv' = analyse_expr lexp accenv [] in
          pure tenv'
        | LibTyp _ -> pure accenv
      ) ~init:accenv lib.lentries
    ) ~init:rlib_env liblist
    in

    (* Analyze fields. *)
    let%bind fields_env = foldM ~f:(fun accenv (_, _, fexp) ->
      let%bind tenv' = analyse_expr fexp accenv [] in
      pure tenv'
    ) ~init:libs_env cmod.contr.cfields
    in

    (* Analyze transitions. *)
    let%bind trans_env = foldM ~f:(fun accenv trans ->
      let%bind tenv' = analyse_stmts trans.tbody accenv in
      pure tenv'
    ) ~init:fields_env cmod.contr.ctrans
    in
    pure trans_env

  (* Walk through "e" and replace TFun and TApp with TFunMap and TFunSel respectively. *)
  let rec monomorphize_expr (e, erep) (tappl : tapps) =
    match e with
    | Literal l -> pure ((MS.Literal l), erep)
    | Var v -> pure ((MS.Var v), erep)
    | Message m -> pure ((MS.Message m), erep)
    | App (a, l) -> pure ((MS.App (a, l)), erep)
    | Constr (s, tl, il) -> pure ((MS.Constr (s, tl, il)), erep)
    | Builtin (i, il)  -> pure ((MS.Builtin (i, il)), erep)
    | Fixpoint (i, t, body) ->
      let%bind body' = monomorphize_expr body tappl in
      pure ((MS.Fixpoint (i, t, body')), erep)
    | Fun (i, t, body) ->
      let%bind body' = monomorphize_expr body tappl in
      pure ((MS.Fun (i, t, body')), erep)
    | Let (i, topt, lhs, rhs) ->
      let%bind lhs' = monomorphize_expr lhs tappl in
      let%bind rhs' = monomorphize_expr rhs tappl in
      pure ((MS.Let (i, topt, lhs', rhs')), erep)
    | MatchExpr (i, clauses) ->
      let%bind clauses' = mapM ~f:(fun (p, cexp) ->
        let%bind cexp' = monomorphize_expr cexp tappl in
        pure (p, cexp')
      ) clauses
      in
      pure (MS.MatchExpr(i, clauses'), erep)
    | TFun (v, body) ->
      let%bind body' = monomorphize_expr body tappl in
      pure ((MS.TFunMap ((v, body'), [])), erep)
    | TApp (i, tl) -> pure ((MS.TFunSel (i, tl)), erep)
  
    (* Walk through statement list and replace TFun and TApp with TFunMap and TFunSel respectively. *)
  let rec monomorphize_stmts stmts (tappl : tapps) : ((MS.stmt_annot list), 'a) result =
    match stmts with
    | [] -> pure []
    | (s, srep) :: sts ->
      let%bind sts' = monomorphize_stmts sts tappl in
      (match s with
      | Load (x, m) ->
        let s' = MS.Load(x, m) in
        pure ((s', srep) :: sts')
      | Store (m, i) ->
        let s' = MS.Store(m, i) in
        pure ((s', srep) :: sts')
      | MapUpdate (i, il, io) ->
        let s' = MS.MapUpdate (i, il, io) in
        pure ((s', srep) :: sts')
      | MapGet (i, i', il, b) ->
        let s' = MS.MapGet (i, i', il, b) in
        pure ((s', srep) :: sts')
      | ReadFromBC (i, s) ->
        let s' = MS.ReadFromBC (i, s) in
        pure ((s', srep) :: sts')
      | AcceptPayment ->
        let s' = MS.AcceptPayment in
        pure ((s', srep) :: sts')
      | SendMsgs m ->
        let s' = MS.SendMsgs(m) in
        pure ((s', srep) :: sts')
      | CreateEvnt e ->
        let s' = MS.CreateEvnt(e) in
        pure ((s', srep) :: sts') 
      | Throw t ->
        let s' = MS.Throw(t) in
        pure ((s', srep) :: sts')
      | Bind (i , e) ->
        let%bind e' = monomorphize_expr e tappl in
        let s' = MS.Bind(i, e') in
        pure ((s', srep) :: sts')
      | MatchStmt (i, pslist) ->
        let%bind pslist' = mapM ~f:(fun (p, ss) ->
          let%bind ss' = monomorphize_stmts ss tappl in
          pure(p, ss')
        ) pslist
        in
        let s' = MS.MatchStmt(i, pslist') in
        pure ((s', srep) :: sts')
      )
  
  (* Walk through entire module and replace TFun and TApp with TFunMap and TFunSel respectively. *)
  let monomorphize_module (cmod : cmodule) rlibs elibs =
    (* Analyze and find all possible instantiations. *)
    let%bind tappl = analyze_module cmod rlibs elibs in

    (* Translate recursion libs. *)
    let%bind rlibs' = mapM ~f:(fun (i, e) ->
        let%bind e' = monomorphize_expr e tappl in
        pure (i, e')
    ) rlibs
    in

    (* Translate external libs. *)
    let%bind elibs' = mapM ~f:(fun lib ->
      mapM ~f:(fun lentry ->
        match lentry with
        | LibVar (i, lexp) ->
          let%bind lexp' = monomorphize_expr lexp tappl in
          pure (MS.LibVar(i, lexp'))
        | LibTyp (i, tdefs) ->
          let tdefs' = List.map (fun (t : ctr_def) ->
            { MS.cname = t.cname; MS.c_arg_types = t.c_arg_types }
          ) tdefs in
          pure (MS.LibTyp (i, tdefs'))
      ) lib.lentries
    ) elibs
    in

    (* Translate contract library. *)
    let%bind clibs' = match cmod.libs with
      | Some clib ->
        let%bind clibs' = mapM ~f:(fun lentry ->
          match lentry with
          | LibVar (i, lexp) ->
            let%bind lexp' = monomorphize_expr lexp tappl in
            pure (MS.LibVar(i, lexp'))
          | LibTyp (i, tdefs) ->
            let tdefs' = List.map (fun (t : ctr_def) ->
              { MS.cname = t.cname; MS.c_arg_types = t.c_arg_types }
            ) tdefs in
            pure (MS.LibTyp (i, tdefs'))
        ) clib.lentries
        in
        pure (Some 
          { MS.lname = clib.lname; MS.lentries = clibs' })
      | None -> pure None
    in

    let%bind fields' = mapM ~f:(fun (i, t, fexp) ->
      let%bind fexp' = monomorphize_expr fexp tappl in
      pure (i, t, fexp')
    ) cmod.contr.cfields
    in

    let%bind trans' = mapM ~f:(fun trans ->
      let%bind body' = monomorphize_stmts trans.tbody tappl in
      pure { MS.tname = trans.tname; MS.tparams = trans.tparams; MS.tbody = body' }
    ) cmod.contr.ctrans
    in

    let contr' = { MS.cname = cmod.contr.cname; MS.cparams = cmod.contr.cparams;
                   MS.cfields = fields'; ctrans = trans' } in
    let cmod' = { MS.smver = cmod.smver; MS.cname = cmod.cname;
                  MS.elibs = cmod.elibs;
                  MS.libs = clibs'; MS.contr = contr' } in

    (* Return back the whole program, transformed. *)
    pure (cmod', rlibs', elibs')

end
