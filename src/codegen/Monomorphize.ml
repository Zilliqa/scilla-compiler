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
  * Postponing the analysis of computing the possible instantiations of a
  * TFun expression, we make a naive assumption that all types used in TApps
  * in the whole program can be used to instantiate a TFun. While this is
  * conservative (and imprecise), it is safe.

  * - `analyze_module` is the entry to the analysis that goes through the AST and
  * computes a list of type applications. This is `type list`. It is a simple
  * walk of the AST looking for `TApp` expressions and adding to the list (if the
  * list doesn't already contain an identical `TApp`). By way of this being a
  * simple walk, it does not filter out non-ground-type `TApp`s (instantiations).
  * - As a post-process on the analyzed data from `analyze_module`, to eliminate
  * presence of non-ground types, `postprocess_tappl` is called, which does:
  *    * Build a list of ground types scanning through the tapps list from
         `analyze_module`.
       * This finite list of ground types is substituted into all non-ground
         types in the tapps list, in all combinations possible.
       * The functions to do this are written in a bottom-up fashion, where
         functions that do the smallest of substitutions are defined first and 
         these are then used to substitute at a higher abstract. In each level
         here, there is a potential exponential blow-up of substituted ground
         types.

  * Finally, the output of `postprocess_tappl`, a list of ground types,
    is used to instantiate the input program. For each `TFun` expression, the
    function `compute_instantiations` uses the tapps data to compute (based on
    the heuristic described above) the possible instantiations.

  * TODO: (1) A more precise analysis to compute possible instantiations of a TFun
  * exprsesion. (2) Update / add annotations to instantiated expressions.
*)

open Core_kernel
open! Int.Replace_polymorphic_compare
open TypeUtil
open MonadUtil
open Core.Result.Let_syntax
open MonomorphicSyntax

(* Translate ScillaSyntax to MonomorphicSyntax. *)
module ScillaCG_Mmph = struct
  module MS = MmphSyntax
  module TU = TypeUtilities
  open ExplicitAnnotationSyntax.EASyntax

  (*******************************************************)
  (* Gather possible instances of polymorphic functions  *)
  (*******************************************************)

  (* TODO: More precise analysis:
   *       "A Type- and Control-Flow Analysis for System F Technical Report" - Matthew Fluet. 
   * Currently only have "all TApps flow to all TFuns". *)

  (* Add a type application to tracked list of instantiations. If any type has a
   * free TypeVar that is not in bound_tvars, return error. If the TypeVar
   * is bound, then it is tracked in the env as PolyFun(TypeVar) to make
   * simple to compare types using type_equiv (alpha equivalence). *)
  let add_tapp tenv tapp bound_tvars lc =
    let%bind tapp' =
      mapM
        ~f:(fun t ->
          let ftvs = Type.free_tvars t in
          match
            List.find
              ~f:(fun v -> not (List.mem bound_tvars ~equal:String.( = ) v))
              ftvs
          with
          | Some v ->
              fail1
                (Printf.sprintf
                   "Monomorphize: Unbound type variable %s used in \
                    instantiation"
                   v)
                lc
          | None ->
              (* Bind all free variables for it to work with type_equiv *)
              pure
              @@ List.fold_left
                   ~f:(fun acc ftv -> PolyFun (ftv, acc))
                   ~init:t ftvs)
        tapp
    in
    (* For each type in tapp', if doesn't exist in tenv, add it. *)
    pure
    @@ List.fold_left
         ~f:(fun accenv t ->
           Utils.list_add_unique ~equal:[%equal: Type.t] accenv t)
         ~init:tenv tapp'

  (* Walk through "e" and add all TApps. *)
  let rec analyse_expr (e, rep) tenv (bound_tvars : string list) =
    match e with
    | Literal _ | Var _ | Message _ | App _ | Constr _ | Builtin _ -> pure tenv
    | Fixpoint (_, _, body) | Fun (_, _, body) ->
        analyse_expr body tenv bound_tvars
    | Let (_, _, lhs, rhs) ->
        let%bind tenv' = analyse_expr lhs tenv bound_tvars in
        analyse_expr rhs tenv' bound_tvars
    | MatchExpr (_, clauses) ->
        foldM
          ~f:(fun accenv (_, bre) ->
            let%bind tenv' = analyse_expr bre accenv bound_tvars in
            pure tenv')
          ~init:tenv clauses
    | TFun (v, e') -> analyse_expr e' tenv (Identifier.get_id v :: bound_tvars)
    | TApp (_, tapp) -> add_tapp tenv tapp bound_tvars rep.ea_loc

  (* Walk through statement list and add all TApps. *)
  let rec analyse_stmts stmts tenv =
    match stmts with
    | [] -> pure tenv
    | (s, _) :: sts -> (
        match s with
        | Load _ | Store _ | MapUpdate _ | MapGet _ | ReadFromBC _ | Iterate _
        | AcceptPayment | SendMsgs _ | CreateEvnt _ | Throw _ | CallProc _ ->
            analyse_stmts sts tenv
        | Bind (_, e) ->
            let%bind tenv' = analyse_expr e tenv [] in
            analyse_stmts sts tenv'
        | MatchStmt (_, pslist) ->
            foldM
              ~f:(fun accenv (_, slist) ->
                let%bind tenv' = analyse_stmts slist accenv in
                pure tenv')
              ~init:tenv pslist )

  (* Walk through entire module, tracking TApps. *)
  let analyze_module (cmod : cmodule) rlibs elibs =
    (* Function to anaylze library entries. *)
    let analyze_lib_entries env lentries =
      foldM
        ~f:(fun accenv lentry ->
          match lentry with
          | LibVar (_, _, lexp) ->
              let%bind tenv' = analyse_expr lexp accenv [] in
              pure tenv'
          | LibTyp _ -> pure accenv)
        ~init:env lentries
    in

    (* Analyze recursion library entries. *)
    let%bind rlib_env = analyze_lib_entries [] rlibs in

    (* Function to analyze external and contract libraries. *)
    let analyze_library env lib = analyze_lib_entries env lib.lentries in

    (* Analyze full library tree. *)
    let rec analyze_libtree env lib =
      (* first analyze all the dependent libraries. *)
      let%bind env' =
        foldM
          ~f:(fun accenv lib -> analyze_libtree accenv lib)
          ~init:env lib.deps
      in
      (* analyze this library. *)
      analyze_library env' lib.libn
    in
    let%bind elibs_env =
      foldM
        ~f:(fun accenv libt -> analyze_libtree accenv libt)
        ~init:rlib_env elibs
    in
    let%bind libs_env =
      match cmod.libs with
      | Some lib -> analyze_library elibs_env lib
      | None -> pure elibs_env
    in

    (* Analyze fields. *)
    let%bind fields_env =
      foldM
        ~f:(fun accenv (_, _, fexp) ->
          let%bind tenv' = analyse_expr fexp accenv [] in
          pure tenv')
        ~init:libs_env cmod.contr.cfields
    in

    (* Analyze transitions. *)
    let%bind trans_env =
      foldM
        ~f:(fun accenv comp ->
          let%bind tenv' = analyse_stmts comp.comp_body accenv in
          pure tenv')
        ~init:fields_env cmod.contr.ccomps
    in
    pure trans_env

  (* The type applications collected by analyze_module may have non-ground applications.
   * This function will substitute into and eliminate such applications. *)
  let postprocess_tappl tappl =
    (* Get a list of all ground types. *)
    let gts =
      List.fold_left
        ~f:(fun acc t ->
          if TU.is_ground_type t then
            (* If "t" is not already in acc, add it. *)
            Utils.list_add_unique ~equal:[%equal: Type.t] acc t
          else acc)
        ~init:[] tappl
    in

    (* Given a type, substitute all of the given ground types, in all combinations. 
     * Return a list of concrete types that will replace the input type. *)
    let eliminate_tvars t gts =
      (* First ensure that all TVars are bound. *)
      if not @@ List.is_empty (Type.free_tvars t) then
        fail0 "Unbound type variables during Monomorphize"
      else
        (* Subsitute the first PolyFun in t with tg. *)
        let subst_first_polyfun t tg =
          let rec subst t =
            (* Call subst for each element in tls, till there is a substitution. *)
            let subst_tlist tls =
              let%bind _, rtls =
                foldM
                  ~f:(fun (substituted, rtls) t ->
                    if substituted then pure (true, t :: rtls)
                    else
                      let%bind t' = subst t in
                      pure ([%equal: Type.t] t t', t' :: rtls))
                  ~init:(false, []) tls
              in
              pure @@ List.rev rtls
            in
            match t with
            | PrimType _ | Unit -> pure t
            | MapType (kt, vt) -> (
                let%bind s' = subst_tlist [ kt; vt ] in
                match s' with
                | [ kt'; vt' ] -> pure @@ Type.MapType (kt', vt')
                | _ -> fail0 "Monomorphize: Internal error in type substitution"
                )
            | FunType (at, ft) -> (
                let%bind s' = subst_tlist [ at; ft ] in
                match s' with
                | [ kt'; vt' ] -> pure @@ Type.FunType (kt', vt')
                | _ -> fail0 "Monomorphize: Internal error in type substitution"
                )
            | ADT (tname, tls) ->
                let%bind tls' = subst_tlist tls in
                pure @@ Type.ADT (tname, tls')
            | TypeVar tv ->
                fail0 (Printf.sprintf "Monomorphize: Unbound TypeVar %s" tv)
            | PolyFun (tv, tbody) ->
                (* replace tv with tg in tbody. *)
                pure @@ Type.subst_type_in_type tv tg tbody
          in
          subst t
        in

        (* Substitute each ground type in tgs into all types in ts.
           * The result is a list of size length(tgs) * length(ts). *)
        let subst_all_ground_into_tlist ts tgs =
          let%bind ts' =
            mapM
              ~f:(fun t -> mapM ~f:(fun tg -> subst_first_polyfun t tg) tgs)
              ts
          in
          pure @@ List.concat ts'
        in

        (* Call "subst_all_ground_into_tlist" till no more substitutions are possible. *)
        let rec eliminate ts tgs =
          match ts with
          | [] -> pure ts
          | t :: _ ->
              (* Check just one element, others are expected to be the same. *)
              (* if "t" is ground type, no more substitutions are possible. *)
              if TU.is_ground_type t then pure ts
              else
                let%bind ts' = subst_all_ground_into_tlist ts tgs in
                eliminate ts' tgs
        in

        (* We end the definition of eliminate_tvars by calling eliminate. *)
        eliminate [ t ] gts
    in

    (* We now have a list of ground types for substitution into tappl 
     * AND the tool to do the substitution in all possible ways and return
     * a list of substituted types. We need to do this substitution into
     * all types in the input list of type applications: tappl. *)
    foldM
      ~f:(fun acc ta ->
        let%bind tgs = eliminate_tvars ta gts in
        (* Add-unique each t in tgs to acc. *)
        let acc' =
          List.fold_left
            ~f:(fun acc t ->
              Utils.list_add_unique ~equal:[%equal: Type.t] acc t)
            ~init:acc tgs
        in
        pure acc')
      ~init:[] tappl

  (* End of postprocess_tappl. *)

  let monomorphize_payload = function
    | MLit l -> MS.MLit l
    | MVar v -> MS.MVar v

  let rec monomorphize_pattern = function
    | Wildcard -> MS.Wildcard
    | Binder v -> MS.Binder v
    | Constructor (s, plist) ->
        MS.Constructor (s, List.map ~f:monomorphize_pattern plist)

  (* Walk through "e" and replace TFun and TApp with TFunMap and TFunSel respectively. *)
  let rec monomorphize_expr (e, rep) tappl =
    match e with
    | Literal l -> pure (MS.Literal l, rep)
    | Var v -> pure (MS.Var v, rep)
    | Message m ->
        let m' = List.map ~f:(fun (s, p) -> (s, monomorphize_payload p)) m in
        pure (MS.Message m', rep)
    | App (a, l) -> pure (MS.App (a, l), rep)
    | Constr (s, tl, il) -> pure (MS.Constr (s, tl, il), rep)
    | Builtin (i, il) -> pure (MS.Builtin (i, il), rep)
    | Fixpoint (i, t, body) ->
        let%bind body' = monomorphize_expr body tappl in
        pure (MS.Fixpoint (i, t, body'), rep)
    | Fun (i, t, body) ->
        let%bind body' = monomorphize_expr body tappl in
        pure (MS.Fun (i, t, body'), rep)
    | Let (i, topt, lhs, rhs) ->
        let%bind lhs' = monomorphize_expr lhs tappl in
        let%bind rhs' = monomorphize_expr rhs tappl in
        pure (MS.Let (i, topt, lhs', rhs'), rep)
    | MatchExpr (i, clauses) ->
        let%bind clauses' =
          mapM
            ~f:(fun (p, cexp) ->
              let%bind cexp' = monomorphize_expr cexp tappl in
              pure (monomorphize_pattern p, cexp'))
            clauses
        in
        pure (MS.MatchExpr (i, clauses'), rep)
    | TFun (v, body) ->
        let%bind tfuns =
          mapM
            ~f:(fun t ->
              if
                (not (List.is_empty (Type.free_tvars t)))
                || not (TU.is_ground_type t)
              then
                fail1
                  "Internal error. Attempting to instantiate with a non-ground \
                   type or type variable."
                  rep.ea_loc
              else
                (* ******************************************************************************* *)
                let lc = rep.ea_loc in
                Printf.printf "Instantiating at (%s,%d,%d) with type: %s\n"
                  lc.fname lc.lnum lc.cnum (Type.pp_typ t);
                (* ******************************************************************************* *)
                let ibody = subst_type_in_expr v t body in
                let%bind ibody' = monomorphize_expr ibody tappl in
                pure (t, ibody'))
            tappl
        in
        pure (MS.TFunMap tfuns, rep)
    | TApp (i, tl) -> pure (MS.TFunSel (i, tl), rep)

  (* Walk through statement list and replace TFun and TApp with TFunMap and TFunSel respectively. *)
  let rec monomorphize_stmts stmts tappl : (MS.stmt_annot list, 'a) result =
    match stmts with
    | [] -> pure []
    | (s, srep) :: sts -> (
        let%bind sts' = monomorphize_stmts sts tappl in
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
            let%bind e' = monomorphize_expr e tappl in
            let s' = MS.Bind (i, e') in
            pure ((s', srep) :: sts')
        | MatchStmt (i, pslist) ->
            let%bind pslist' =
              mapM
                ~f:(fun (p, ss) ->
                  let%bind ss' = monomorphize_stmts ss tappl in
                  pure (monomorphize_pattern p, ss'))
                pslist
            in
            let s' = MS.MatchStmt (i, pslist') in
            pure ((s', srep) :: sts') )

  (* Walk through entire module and replace TFun and TApp with TFunMap and TFunSel respectively. *)
  let monomorphize_module (cmod : cmodule) rlibs elibs =
    (* Analyze and find all possible instantiations. *)
    let%bind tappl' = analyze_module cmod rlibs elibs in
    let%bind tappl = postprocess_tappl tappl' in

    (* Function to monomorphize library entries. *)
    let monomorphize_lib_entries tappl lentries =
      mapM
        ~f:(fun lentry ->
          match lentry with
          | LibVar (i, topt, lexp) ->
              let%bind lexp' = monomorphize_expr lexp tappl in
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
    let%bind rlibs' = monomorphize_lib_entries tappl rlibs in

    (* Function to monomorphize a library. *)
    let monomorphize_lib tappl lib =
      let%bind lentries' = monomorphize_lib_entries tappl lib.lentries in
      let lib' = { MS.lname = lib.lname; lentries = lentries' } in
      pure lib'
    in

    (* Monomorphize the library tree. *)
    let rec monomorphize_libtree tappl libt =
      let%bind deps' =
        mapM ~f:(fun dep -> monomorphize_libtree tappl dep) libt.deps
      in
      let%bind libn' = monomorphize_lib tappl libt.libn in
      let libt' = { MS.libn = libn'; MS.deps = deps' } in
      pure libt'
    in
    let%bind elibs' =
      mapM ~f:(fun elib -> monomorphize_libtree tappl elib) elibs
    in

    (* Translate contract library. *)
    let%bind clibs' =
      match cmod.libs with
      | Some clib ->
          let%bind clib' = monomorphize_lib tappl clib in
          pure @@ Some clib'
      | None -> pure None
    in

    (* Translate fields and their initializations. *)
    let%bind fields' =
      mapM
        ~f:(fun (i, t, fexp) ->
          let%bind fexp' = monomorphize_expr fexp tappl in
          pure (i, t, fexp'))
        cmod.contr.cfields
    in

    (* Translate all contract components. *)
    let%bind comps' =
      mapM
        ~f:(fun comp ->
          let%bind body' = monomorphize_stmts comp.comp_body tappl in
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
        MS.cname = cmod.cname;
        MS.elibs = cmod.elibs;
        MS.libs = clibs';
        MS.contr = contr';
      }
    in

    (* Return back the whole program, transformed. *)
    pure (cmod', rlibs', elibs')

  (* For monomorphizing standalone expressions. *)
  let monomorphize_expr_wrapper expr =
    let%bind tappl' = analyse_expr expr [] [] in
    let%bind tappl = postprocess_tappl tappl' in
    let%bind expr' = monomorphize_expr expr tappl in
    pure expr'

  module OutputSyntax = MS
end

(* References:
  Motivation for a monomorphizing compiler:
  - Levity Polymorphism - Richard A. Eisenberg and Simon Peyton Jones
  - http://web.cecs.pdx.edu/~apt/jfp98.ps
  - http://mlton.org/References.attachments/060916-mlton.pdf
  - https://twitter.com/pcwalton/status/1192970706482388992?s=20 
*)
