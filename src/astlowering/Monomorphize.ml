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

(* 
 * This file contains code to instantiate all type polymorphic functions
 * in a Scilla program. The new AST is a variation of ScillaSyntax which
 * replace TApp and TFun expressions with TFunSel and TFunMap expressions.
 * The AST definition can be found in MonomorphicSyntax.ml.
 *)

open Core_kernel
open! Int.Replace_polymorphic_compare
module Array = BatDynArray
open Scilla_base
module Literal = Literal.FlattenedLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open MonadUtil
open UncurriedSyntax
open Core.Result.Let_syntax
open MonomorphicSyntax

(* Monadic version of List.fold_map *)
let fold_mapM ~f ~init l =
  let%bind acc, l'_rev =
    foldM ~init:(init, [])
      ~f:(fun (accacc, lrevacc) lel ->
        let%bind accacc', lel' = f accacc lel in
        pure (accacc', lel' :: lrevacc))
      l
  in
  pure (acc, List.rev l'_rev)

(* Translate ScillaSyntax to MonomorphicSyntax. *)
module ScillaCG_Mmph = struct
  module MS = MmphSyntax
  module TU = Uncurried_Syntax.TypeUtilities
  open UncurriedSyntax.Uncurried_Syntax

  (* ******************************************************** *)
  (*  Types used for the type- and control-flow analysis      *)
  (* ******************************************************** *)

  module TypElm = struct
    type t = typ

    let compare = TU.compare

    let sexp_of_t = sexp_of_typ

    let t_of_sexp = typ_of_sexp

    let make x = x
  end

  (* Calling context, with the caller's tfa_data index representing context. *)
  type context = int list [@@deriving sexp, compare]

  (* The context of free variables in a (type) closure. *)
  type context_env = (int * context) list [@@deriving sexp, compare]

  (* We track the flow of TFuns as a pair of tfa_data index (of the TFun)
   * and the context environment of its free type variables. *)
  type tfun_clo_env = int * context_env [@@deriving sexp, compare]

  module TFunCloElm = struct
    type t = tfun_clo_env

    let compare = compare_tfun_clo_env

    let sexp_of_t = sexp_of_tfun_clo_env

    let t_of_sexp = tfun_clo_env_of_sexp

    let make x = x
  end

  module TypSet = Set.Make (TypElm)
  module IntSet = Int.Set
  module TFunCloSet = Set.Make (TFunCloElm)

  type rev_ref = ExprRef of expr_annot ref | VarRef of string

  (* Data element propagated in the type-flow analysis. *)
  type tfa_el = {
    (* The TFun expressions that reach a program point or variable. *)
    reaching_tfuns : TFunCloSet.t;
    (* The Fun expressions that reach a program point or variable. *)
    reaching_funs : IntSet.t;
    (* The ground types that reach a type variable, under a given context. *)
    reaching_gtyps : (context * TypSet.t) list;
    (* A back reference to who this information belongs to. *)
    elof : rev_ref;
    (* The free type variables at a TFun.
     * Useful in building the context_env for reaching_tfuns. *)
    free_tvars : int list;
  }

  let empty_tfa_el elof =
    {
      reaching_tfuns = TFunCloSet.empty;
      reaching_funs = IntSet.empty;
      reaching_gtyps = [];
      elof;
      free_tvars = [];
    }

  (* Store for the analysis data. *)
  let tfa_data = Array.create ()

  (* ******************************************************** *)
  (* Add auxiliary annotation to perform type-flow analysis   *)
  (* ******************************************************** *)

  (* Add a new entry to tfa_data and return its index. *)
  let add_tfa_el el =
    let idx = Array.length tfa_data in
    let () = Array.add tfa_data el in
    idx

  (* Get the index of the next element to be inserted. *)
  let next_index () = Array.length tfa_data

  (* The initialization environment tracks the following: *)
  (* 1. The variable indices list is used to attach a tfa_el entry
   *   to a (type) variable at its binding point and use that to
   *   attach the same tfa_el entry at the uses. This way, we 
   *   don't have to rewrite the AST with unique names for variables
   *   and type variables.
   * 2. Free type variables. These are attached to TFun expressions
   *   to easily compute context_env for them.
   *)
  type init_env = { var_indices : (string * int) list; free_tvars : int list }

  let empty_init_env = { var_indices = []; free_tvars = [] }

  let resolv_var ienv v =
    match List.Assoc.find ~equal:String.equal ienv.var_indices v with
    | Some i -> pure i
    | None ->
        fail0 ("Monomorphize: initialize_tfa: Unable to resolve variable " ^ v)

  (* Attach tfa_data index to a variable @v already bound in @ienv *)
  let initialize_tfa_var ienv v =
    let vrep = Identifier.get_rep v in
    let%bind i = resolv_var ienv (Identifier.get_id v) in
    pure
    @@ Identifier.mk_id (Identifier.get_id v) { vrep with ea_auxi = Some i }

  (* Attach a new tfa_data index to variable @v and append it to @env *)
  let initialize_tfa_bind ienv v =
    let idx = add_tfa_el (empty_tfa_el (VarRef (Identifier.get_id v))) in
    let ienv' =
      { ienv with var_indices = (Identifier.get_id v, idx) :: ienv.var_indices }
    in
    let%bind v' = initialize_tfa_var ienv' v in
    pure (ienv', v')

  (* Attach tfa_data index to tvars in @t bound in @ienv *)
  let initialize_tfa_tvar ienv t =
    let rec go local_bounds t =
      match t with
      | TypeVar v ->
          if Identifier.is_mem_id v local_bounds then pure t
          else
            let%bind v' = initialize_tfa_var ienv v in
            pure (TypeVar v')
      | PolyFun (tv, t') -> go (tv :: local_bounds) t'
      | MapType (kt, vt) ->
          let%bind kt' = go local_bounds kt in
          let%bind vt' = go local_bounds vt in
          pure @@ MapType (kt', vt')
      | FunType (arg_typs, ret_typ) ->
          let%bind arg_typs' = mapM ~f:(go local_bounds) arg_typs in
          let%bind ret_typ' = go local_bounds ret_typ in
          pure @@ FunType (arg_typs', ret_typ')
      | ADT (tname, arg_typs) ->
          let%bind arg_typs' = mapM ~f:(go local_bounds) arg_typs in
          pure @@ ADT (tname, arg_typs')
      | PrimType _ | Unit -> pure t
    in
    go [] t

  (* Sets up a tfa_index for each bound variable and returns new env. *)
  let initialize_tfa_match_bind sp =
    let initialize_tfa_match_bind_base ienv = function
      | Wildcard -> pure (ienv, Wildcard)
      | Binder b ->
          let%bind ienv', b' = initialize_tfa_bind ienv b in
          pure (ienv', Binder b')
    in
    match sp with
    | Any base ->
        let%bind new_binds, base' =
          initialize_tfa_match_bind_base empty_init_env base
        in
        pure (new_binds, Any base')
    | Constructor (cname, basel) ->
        let%bind new_binds, basel'_rev =
          fold_mapM ~init:empty_init_env
            ~f:(fun accenv base -> initialize_tfa_match_bind_base accenv base)
            basel
        in
        pure (new_binds, Constructor (cname, List.rev basel'_rev))

  (* Attach an auxiliary annotation for expr, its constituent exprs and vars. *)
  let rec initialize_tfa_expr (ienv : init_env) (e, annot) =
    let%bind e' =
      match e with
      | Literal _ | JumpExpr _ -> pure e
      | Var v ->
          let%bind v' = initialize_tfa_var ienv v in
          pure (Var v')
      | Message comps ->
          let%bind pl' =
            mapM
              ~f:(function
                | s, MLit l -> pure (s, MLit l)
                | s, MVar v ->
                    let%bind v' = initialize_tfa_var ienv v in
                    pure (s, MVar v'))
              comps
          in
          pure (Message pl')
      | App (f, alist) ->
          let%bind f' = initialize_tfa_var ienv f in
          let%bind alist' = mapM ~f:(initialize_tfa_var ienv) alist in
          pure (App (f', alist'))
      | Constr (cname, tlist, vlist) ->
          let%bind tlist' = mapM ~f:(initialize_tfa_tvar ienv) tlist in
          let%bind vlist' = mapM ~f:(initialize_tfa_var ienv) vlist in
          pure @@ Constr (cname, tlist', vlist')
      | Builtin (b, vlist) ->
          let%bind vlist' = mapM ~f:(initialize_tfa_var ienv) vlist in
          pure @@ Builtin (b, vlist')
      | MatchExpr (p, blist, jopt) ->
          let%bind p' = initialize_tfa_var ienv p in
          let%bind blist' =
            mapM
              ~f:(fun (sp, e) ->
                let%bind new_binds, sp' = initialize_tfa_match_bind sp in
                let ienv' =
                  {
                    ienv with
                    var_indices = new_binds.var_indices @ ienv.var_indices;
                  }
                in
                let%bind e' = initialize_tfa_expr ienv' e in
                pure (sp', e'))
              blist
          in
          let%bind jopt' =
            match jopt with
            | None -> pure None
            | Some (l, je) ->
                let%bind e' = initialize_tfa_expr ienv je in
                pure (Some (l, e'))
          in
          pure @@ MatchExpr (p', blist', jopt')
      | Fun (atl, sube) ->
          let%bind ienv', atl'_rev =
            fold_mapM ~init:ienv
              ~f:(fun accenv (v, t) ->
                let%bind t' = initialize_tfa_tvar accenv t in
                let%bind accenv', v' = initialize_tfa_bind accenv v in
                pure (accenv', (v', t')))
              atl
          in
          let%bind sube' = initialize_tfa_expr ienv' sube in
          pure @@ Fun (List.rev atl'_rev, sube')
      | Fixpoint (v, t, sube) ->
          let%bind t' = initialize_tfa_tvar ienv t in
          let%bind ienv', v' = initialize_tfa_bind ienv v in
          let%bind sube' = initialize_tfa_expr ienv' sube in
          pure (Fixpoint (v', t', sube'))
      | Let (x, xtopt, lhs, rhs) ->
          let%bind lhs' = initialize_tfa_expr ienv lhs in
          let%bind xopt' =
            match xtopt with
            | Some xt ->
                let%bind xt' = initialize_tfa_tvar ienv xt in
                pure (Some xt')
            | None -> pure None
          in
          let%bind ienv', x' = initialize_tfa_bind ienv x in
          let%bind rhs' = initialize_tfa_expr ienv' rhs in
          pure (Let (x', xopt', lhs', rhs'))
      | TFun (tv, sube) ->
          let%bind ienv', tv' = initialize_tfa_bind ienv tv in
          let%bind tv_index = resolv_var ienv (Identifier.get_id tv') in
          (* For everything inside this TFun, tv is a free variable. *)
          let ienv'' =
            { ienv with free_tvars = tv_index :: ienv'.free_tvars }
          in
          let%bind sube' = initialize_tfa_expr ienv'' sube in
          pure (TFun (tv', sube'))
      | TApp (tf, targs) ->
          let%bind tf' = initialize_tfa_var ienv tf in
          let%bind targs' = mapM ~f:(initialize_tfa_tvar ienv) targs in
          pure (TApp (tf', targs'))
    in
    (* Add auxiliary annotation for the new expression. *)
    let idx = next_index () in
    let annot' = { annot with ea_auxi = Some idx } in
    let ea = (e', annot') in
    let tfael = empty_tfa_el (ExprRef (ref ea)) in
    let tfael' =
      match e' with
      | Fun _ ->
          (* Add this fun as reachable to itself. *)
          { tfael with reaching_funs = IntSet.add tfael.reaching_funs idx }
      | TFun _ ->
          (* We add this tfun as reachable to itself only if it has no
           * free type variables. Otherwise, we handle it when analyzing
           * its containing tfuns' applications. *)
          if List.is_empty ienv.free_tvars then
            {
              tfael with
              reaching_tfuns = TFunCloSet.add tfael.reaching_tfuns (idx, []);
            }
          else tfael
      | _ -> tfael
    in

    let _ = add_tfa_el tfael' in
    pure ea

  (* Walk through statement list and add all TApps. *)
  let rec initialize_tfa_stmts (ienv : init_env) stmts =
    match stmts with
    | [] -> pure []
    (* We leave statement annotations as-is, but annotate variables. *)
    | (s, annot) :: sts ->
        let%bind s', ienv' =
          match s with
          | AcceptPayment | JumpStmt _ -> pure (s, ienv)
          | Bind (x, e) ->
              let%bind e' = initialize_tfa_expr ienv e in
              let%bind ienv', x' = initialize_tfa_bind ienv x in
              pure (Bind (x', e'), ienv')
          | Load (x, f) ->
              let%bind ienv', x' = initialize_tfa_bind ienv x in
              pure (Load (x', f), ienv')
          | Store (f, x) ->
              let%bind x' = initialize_tfa_var ienv x in
              pure @@ (Store (f, x'), ienv)
          | MapGet (x, m, indices, exists) ->
              let%bind ienv', x' = initialize_tfa_bind ienv x in
              let%bind indices' = mapM ~f:(initialize_tfa_var ienv) indices in
              pure (MapGet (x', m, indices', exists), ienv')
          | MapUpdate (m, indices, vopt) ->
              let%bind indices' = mapM ~f:(initialize_tfa_var ienv) indices in
              let%bind vopt' =
                match vopt with
                | None -> pure None
                | Some v ->
                    let%bind v' = initialize_tfa_var ienv v in
                    pure (Some v')
              in
              pure (MapUpdate (m, indices', vopt'), ienv)
          | ReadFromBC (x, bs) ->
              let%bind x' = initialize_tfa_var ienv x in
              pure (ReadFromBC (x', bs), ienv)
          | Iterate (l, p) ->
              let%bind l' = initialize_tfa_var ienv l in
              pure (Iterate (l', p), ienv)
          | CallProc (p, args) ->
              let%bind args' = mapM ~f:(initialize_tfa_var ienv) args in
              pure (CallProc (p, args'), ienv)
          | SendMsgs m ->
              let%bind m' = initialize_tfa_var ienv m in
              pure (SendMsgs m', ienv)
          | CreateEvnt m ->
              let%bind m' = initialize_tfa_var ienv m in
              pure (CreateEvnt m', ienv)
          | Throw mopt ->
              let%bind mopt' =
                match mopt with
                | None -> pure None
                | Some m ->
                    let%bind m' = initialize_tfa_var ienv m in
                    pure (Some m')
              in
              pure (Throw mopt', ienv)
          | MatchStmt (p, blist, jopt) ->
              let%bind p' = initialize_tfa_var ienv p in
              let%bind blist' =
                mapM
                  ~f:(fun (sp, e) ->
                    let%bind new_binds, sp' = initialize_tfa_match_bind sp in
                    let ienv' =
                      {
                        ienv with
                        var_indices = new_binds.var_indices @ ienv.var_indices;
                      }
                    in
                    let%bind e' = initialize_tfa_stmts ienv' e in
                    pure (sp', e'))
                  blist
              in
              let%bind jopt' =
                match jopt with
                | None -> pure None
                | Some (l, je) ->
                    let%bind e' = initialize_tfa_stmts ienv je in
                    pure (Some (l, e'))
              in
              pure (MatchStmt (p', blist', jopt'), ienv)
        in
        let%bind sts' = initialize_tfa_stmts ienv' sts in
        pure @@ ((s', annot) :: sts')

  (* Walk through entire module, initializing AST nodes to a TFA element. *)
  let initialize_tfa_module (cmod : cmodule) rlibs elibs =
    (* Function to anaylze library entries. *)
    let initialize_tfa_lib_entries env lentries =
      fold_mapM
        ~f:(fun accenv lentry ->
          match lentry with
          | LibVar (x, topt, lexp) ->
              let%bind lexp' = initialize_tfa_expr accenv lexp in
              let%bind accenv', x' = initialize_tfa_bind accenv x in
              let%bind topt' =
                match topt with
                | Some t ->
                    let%bind t' = initialize_tfa_tvar accenv t in
                    pure (Some t')
                | None -> pure None
              in
              pure (accenv', LibVar (x', topt', lexp'))
          | LibTyp _ -> pure (accenv, lentry))
        ~init:env lentries
    in

    (* Intialize in recursion library entries. *)
    let%bind rlib_env, rlibs' =
      initialize_tfa_lib_entries empty_init_env rlibs
    in

    (* Function to initialize in external and contract libraries. *)
    let initialize_tfa_library env lib =
      initialize_tfa_lib_entries env lib.lentries
    in

    (* Initialize in full library tree. *)
    let rec initialize_tfa_libtree env lib =
      (* first analyze all the dependent libraries. *)
      let%bind env', deps' =
        fold_mapM
          ~f:(fun accenv lib -> initialize_tfa_libtree accenv lib)
          ~init:env lib.deps
      in
      (* intialize in this library. *)
      let%bind env'', lentris' = initialize_tfa_library env' lib.libn in
      pure
        (env'', { libn = { lib.libn with lentries = lentris' }; deps = deps' })
    in
    let%bind elibs_env, elibs' =
      fold_mapM
        ~f:(fun accenv libt -> initialize_tfa_libtree accenv libt)
        ~init:rlib_env elibs
    in
    let%bind libs_env, cmod_libs =
      match cmod.libs with
      | Some lib ->
          let%bind libs_env, lentries' = initialize_tfa_library elibs_env lib in
          pure
            ( libs_env,
              { cmod with libs = Some { lib with lentries = lentries' } } )
      | None -> pure (elibs_env, cmod)
    in

    (* Initialize in fields. *)
    let%bind cmod_cfields =
      let%bind cfields' =
        mapM
          ~f:(fun (f, t, fexp) ->
            let%bind t' = initialize_tfa_tvar libs_env t in
            let%bind fexp' = initialize_tfa_expr libs_env fexp in
            pure (f, t', fexp'))
          cmod_libs.contr.cfields
      in
      pure
        { cmod_libs with contr = { cmod_libs.contr with cfields = cfields' } }
    in

    (* Initialize in contract parameters. Note: These are of no interest
     * to us. But since they are accessed the same way as any other bound
     * variables in transitions / procedures, we must have a tfa_el annotated
     * for them, for simpler uniform access. *)
    let%bind cparams_env, cmod_cparams =
      let%bind cparams_env, cparams' =
        fold_mapM ~init:libs_env
          ~f:(fun accenv (v, t) ->
            let%bind accenv', v' = initialize_tfa_bind accenv v in
            let%bind t' = initialize_tfa_tvar accenv t in
            pure (accenv', (v', t')))
          cmod_cfields.contr.cparams
      in
      pure
        ( cparams_env,
          {
            cmod_cfields with
            contr = { cmod_cfields.contr with cparams = cparams' };
          } )
    in

    (* Initialize in components. *)
    let%bind cmod_comps =
      let%bind ccomps' =
        mapM
          ~f:(fun comp ->
            let%bind env', comp_params' =
              fold_mapM ~init:cparams_env
                ~f:(fun accenv (v, t) ->
                  let%bind accenv', v' = initialize_tfa_bind accenv v in
                  let%bind t' = initialize_tfa_tvar accenv t in
                  pure (accenv', (v', t')))
                comp.comp_params
            in
            let%bind stmts' = initialize_tfa_stmts env' comp.comp_body in
            pure { comp with comp_body = stmts'; comp_params = comp_params' })
          cmod_cparams.contr.ccomps
      in
      pure
        {
          cmod_cparams with
          contr = { cmod_cparams.contr with ccomps = ccomps' };
        }
    in
    pure (cmod_comps, rlibs', elibs')

  (* ******************************************************** *)
  (* ******* Type-flow + control-flow analysis ************** *)
  (* ******************************************************** *)

  (* The analysis is a context-sensitive control-flow analysis over TFuns,
   * which is a control-flow-analysis, but over type abstractions
   * instead of value abstractions. The analysis also does the usual
   * control-flow analysis, but without context-sensitivity.
   * References:
      1. Principles of Program Analysis by Flemming Nielson, Hanne R. Nielson, Chris Hankin.
      2. An Efficient Type- and Control-Flow Analysis for System F - Adsit and Fluet.
   *)

  (* ******************************************************** *)
  (* ************** Monomorphization  *********************** *)
  (* ******************************************************** *)

  (* Walk through "e" and replace TFun and TApp with TFunMap and TFunSel respectively. *)
  let rec monomorphize_expr (e, rep) =
    match e with
    | Literal l -> pure (MS.Literal l, rep)
    | Var v -> pure (MS.Var v, rep)
    | Message m ->
        let m' = List.map ~f:(fun (s, p) -> (s, p)) m in
        pure (MS.Message m', rep)
    | App (a, l) -> pure (MS.App (a, l), rep)
    | Constr (s, tl, il) -> pure (MS.Constr (s, tl, il), rep)
    | Builtin (i, il) -> pure (MS.Builtin (i, il), rep)
    | Fixpoint (i, t, body) ->
        let%bind body' = monomorphize_expr body in
        pure (MS.Fixpoint (i, t, body'), rep)
    | Fun (args, body) ->
        let%bind body' = monomorphize_expr body in
        pure (MS.Fun (args, body'), rep)
    | Let (i, topt, lhs, rhs) ->
        let%bind lhs' = monomorphize_expr lhs in
        let%bind rhs' = monomorphize_expr rhs in
        pure (MS.Let (i, topt, lhs', rhs'), rep)
    | JumpExpr l -> pure (MS.JumpExpr l, rep)
    | MatchExpr (i, clauses, join_clause_opt) ->
        let%bind clauses' =
          mapM
            ~f:(fun (p, cexp) ->
              let%bind cexp' = monomorphize_expr cexp in
              pure (p, cexp'))
            clauses
        in
        let%bind join_clause_opt' =
          match join_clause_opt with
          | Some (l, join_clause) ->
              let%bind join_clause' = monomorphize_expr join_clause in
              pure (Some (l, join_clause'))
          | None -> pure None
        in
        pure (MS.MatchExpr (i, clauses', join_clause_opt'), rep)
    | TFun _ ->
        (* TODO *)
        pure (MS.TFunMap [], rep)
    | TApp (i, tl) -> pure (MS.TFunSel (i, tl), rep)

  (* Walk through statement list and replace TFun and TApp with TFunMap and TFunSel respectively. *)
  let rec monomorphize_stmts stmts : (MS.stmt_annot list, 'a) result =
    match stmts with
    | [] -> pure []
    | (s, srep) :: sts -> (
        let%bind sts' = monomorphize_stmts sts in
        match s with
        | Load (x, m) ->
            let s' = MS.Load (x, m) in
            pure ((s', srep) :: sts')
        | Store (m, i) ->
            let s' = MS.Store (m, i) in
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
            let s' = MS.SendMsgs m in
            pure ((s', srep) :: sts')
        | CreateEvnt e ->
            let s' = MS.CreateEvnt e in
            pure ((s', srep) :: sts')
        | Throw t ->
            let s' = MS.Throw t in
            pure ((s', srep) :: sts')
        | CallProc (p, al) ->
            let s' = MS.CallProc (p, al) in
            pure ((s', srep) :: sts')
        | Iterate (l, p) ->
            let s' = MS.Iterate (l, p) in
            pure ((s', srep) :: sts')
        | Bind (i, e) ->
            let%bind e' = monomorphize_expr e in
            let s' = MS.Bind (i, e') in
            pure ((s', srep) :: sts')
        | JumpStmt l ->
            let s' = MS.JumpStmt l in
            pure ((s', srep) :: sts')
        | MatchStmt (i, pslist, join_clause_opt) ->
            let%bind pslist' =
              mapM
                ~f:(fun (p, ss) ->
                  let%bind ss' = monomorphize_stmts ss in
                  pure (p, ss'))
                pslist
            in
            let%bind join_clause_opt' =
              match join_clause_opt with
              | Some (l, join_clause) ->
                  let%bind join_clause' = monomorphize_stmts join_clause in
                  pure (Some (l, join_clause'))
              | None -> pure None
            in
            let s' = MS.MatchStmt (i, pslist', join_clause_opt') in
            pure ((s', srep) :: sts') )

  (* Walk through entire module and replace TFun and TApp with TFunMap and TFunSel respectively. *)
  let monomorphize_module (cmod : cmodule) rlibs elibs =
    (* Analyze and find all possible instantiations. *)
    let%bind _cmod', _rlibs', _elibs' =
      initialize_tfa_module cmod rlibs elibs
    in

    (* Function to monomorphize library entries. *)
    let monomorphize_lib_entries lentries =
      mapM
        ~f:(fun lentry ->
          match lentry with
          | LibVar (i, topt, lexp) ->
              let%bind lexp' = monomorphize_expr lexp in
              pure (MS.LibVar (i, topt, lexp'))
          | LibTyp (i, tdefs) ->
              let tdefs' =
                List.map
                  ~f:(fun (t : ctr_def) ->
                    { MS.cname = t.cname; MS.c_arg_types = t.c_arg_types })
                  tdefs
              in
              pure (MS.LibTyp (i, tdefs')))
        lentries
    in

    (* Translate recursion libs. *)
    let%bind rlibs' = monomorphize_lib_entries rlibs in

    (* Function to monomorphize a library. *)
    let monomorphize_lib lib =
      let%bind lentries' = monomorphize_lib_entries lib.lentries in
      let lib' = { MS.lname = lib.lname; lentries = lentries' } in
      pure lib'
    in

    (* Monomorphize the library tree. *)
    let rec monomorphize_libtree libt =
      let%bind deps' =
        mapM ~f:(fun dep -> monomorphize_libtree dep) libt.deps
      in
      let%bind libn' = monomorphize_lib libt.libn in
      let libt' = { MS.libn = libn'; MS.deps = deps' } in
      pure libt'
    in
    let%bind elibs' = mapM ~f:(fun elib -> monomorphize_libtree elib) elibs in

    (* Translate contract library. *)
    let%bind clibs' =
      match cmod.libs with
      | Some clib ->
          let%bind clib' = monomorphize_lib clib in
          pure @@ Some clib'
      | None -> pure None
    in

    (* Translate fields and their initializations. *)
    let%bind fields' =
      mapM
        ~f:(fun (i, t, fexp) ->
          let%bind fexp' = monomorphize_expr fexp in
          pure (i, t, fexp'))
        cmod.contr.cfields
    in

    (* Translate all contract components. *)
    let%bind comps' =
      mapM
        ~f:(fun comp ->
          let%bind body' = monomorphize_stmts comp.comp_body in
          pure
            {
              MS.comp_type = comp.comp_type;
              MS.comp_name = comp.comp_name;
              MS.comp_params = comp.comp_params;
              MS.comp_body = body';
            })
        cmod.contr.ccomps
    in

    let contr' =
      {
        MS.cname = cmod.contr.cname;
        MS.cparams = cmod.contr.cparams;
        MS.cfields = fields';
        ccomps = comps';
      }
    in
    let cmod' =
      {
        MS.smver = cmod.smver;
        MS.elibs = cmod.elibs;
        MS.libs = clibs';
        MS.contr = contr';
      }
    in

    (* Return back the whole program, transformed. *)
    pure (cmod', rlibs', elibs')

  (* For monomorphizing standalone expressions. *)
  let monomorphize_expr_wrapper expr =
    let%bind expr' = initialize_tfa_expr empty_init_env expr in
    let%bind expr'' = monomorphize_expr expr' in
    pure expr''

  module OutputSyntax = MS
end

(* References:
  Motivation for a monomorphizing compiler:
  - Levity Polymorphism - Richard A. Eisenberg and Simon Peyton Jones
  - http://web.cecs.pdx.edu/~apt/jfp98.ps
  - http://mlton.org/References.attachments/060916-mlton.pdf
  - https://twitter.com/pcwalton/status/1192970706482388992?s=20 
*)
