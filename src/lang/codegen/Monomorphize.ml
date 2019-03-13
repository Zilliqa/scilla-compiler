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
  * The only simple improvement we currently have on top of 
  * "every TFun is instantiated with all types in tappl" is the following:
  * The expression
  *     let a = tfun 'A => (anything but another tfun) ...  
  *      ...
  *     let x = @b Int32 Int64 in
  * Here, "a" can only be instantiated with Int64 and not Int32.
  * To accommodate this minor improvement heuristic, rather than computing
  * a list of all concrete types that can instantiate a TFun, we compute a
  * list of (list of pairs - corresponding to TApps) and use that to filter
  * out a few instantiations as shown in the example above.

  * - `analyze_module` is the entry to the analysis that goes through the AST and
  * computes a list of type applications. This is `type list list`. It is a simple
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

  * Finally, the output of `postprocess_tappl`, a list of list of ground types
    is used to instantiate the input program. For each `TFun` expression, the
    function `compute_instantiations` uses the tapps data to compute (based on
    the heuristic described above) the possible instantiations.

  * TODO: (1) A more precise analysis to compute possible instantiations of a TFun
  * exprsesion. (2) Update / add annotations to instantiated expressions.
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
   * free TypeVar that is not in bound_tvars, return error. If the TypeVar
   * is bound, then it is tracked in the tapp list as PolyFun(TypeVar) to make
   * simple to compare types using type_equiv. *)
  let add_tapp (tenv : tapps) tapp bound_tvars lc =
    let%bind tapp' = mapM ~f:(fun t ->
      let ftvs = free_tvars t in
      match List.find_opt (fun v -> not (List.mem v bound_tvars)) ftvs with
      | Some v -> fail1 (Printf.sprintf "Monomorphize: Unbound type variable %s used in instantiation" v) lc
      | None ->
        (* Bind all free variables for it to work with type_equiv *)
        pure @@ List.fold_left (fun acc ftv -> PolyFun (ftv, acc)) t ftvs
      ) tapp in
    (* If tapp' doesn't exist in tenv, add it. *)
    pure @@ Utils.list_add_unique ~equal:(TU.type_equiv_list) tenv tapp'

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

  (* The type applications collected by analyze_module may have non-ground applications.
   * This function will substitute into and eliminate such applications. *)
  let postprocess_tappl (tappll : tapps) =

    (* Get a flat list of all ground types. *)
    let gts = List.fold_left (fun acc tl ->
      List.fold_left (fun acc t ->
        if TU.is_ground_type t
        then
          (* If "t" is not already in acc, add it. *)
          Utils.list_add_unique ~equal:(TU.type_equiv) acc t
        else
          acc
      ) acc tl
    ) [] tappll in

    (* Given a type, substitute all of the given ground types, in all combinations. 
     * Return a list of concrete types that will replace the input type. *)
    let eliminate_tvars t gts =
      (* First ensure that all TVars are bound. *)
      if free_tvars t <> [] then fail0 "Unbound type variables during Monomorphize" else

      (* Subsitute the first PolyFun in t with tg. *)
      let subst_first_polyfun t tg =
        let rec subst t =
          (* Call subst for each element in tls, till there is a substitution. *)
          let subst_tlist tls =
            let%bind (_, rtls) = foldM ~f:(fun (substituted, rtls) t ->
              if substituted then pure (true, t :: rtls) else
              let%bind t' = subst t in
              pure (t = t', t'::rtls)
            ) ~init:(false, []) tls 
            in
            pure @@ List.rev rtls
          in
          match t with
          | PrimType _ | Unit -> pure t
          | MapType (kt, vt) ->
            let%bind s' = subst_tlist [kt;vt] in
            (match s' with
            | [kt';vt'] -> pure @@ MapType(kt', vt')
            | _ -> fail0 "Monomorphize: Internal error in type substitution")
          | FunType  (at, ft) ->
            let%bind s' = subst_tlist [at;ft] in
            (match s' with
            | [kt';vt'] -> pure @@ FunType(kt', vt')
            | _ -> fail0 "Monomorphize: Internal error in type substitution")
          | ADT (tname, tls) ->
            let%bind tls' = subst_tlist tls in
            pure @@ ADT(tname, tls')
          | TypeVar tv -> fail0 (Printf.sprintf "Monomorphize: Unbound TypeVar %s" tv)
          | PolyFun (tv, tbody) ->
            (* replace tv with tg in tbody. *)
            pure @@ subst_type_in_type tv tg tbody
        in
        subst t
      in

      (* Substitute each ground type in tgs into all types in ts. 
      * The result is a list of size length(tgs) * length(ts). *)
      let subst_all_ground_into_tlist ts tgs =
        let%bind ts' = mapM ~f:(fun t ->
          mapM ~f:(fun tg ->
            subst_first_polyfun t tg
          ) tgs
        ) ts
        in
        pure @@ List.concat ts'
      in

      (* Call "subst_all_ground_into_tlist" till no more substitutions are possible. *)
      let rec eliminate ts tgs =
        match ts with
        | [] -> pure ts
        | t :: _ -> (* Check just one element, others are expected to be the same. *)
          (* if "t" is ground type, no more substitutions are possible. *)
          if TU.is_ground_type t then pure ts else
          let%bind ts' = subst_all_ground_into_tlist ts tgs in
          eliminate ts' tgs
      in

      (* We end the definition of eliminate_tvars by calling eliminate. *)
      eliminate [t] gts
    in

    (* We now have a list of ground types for substitution into tappl 
     * AND the tool to do the substitution in all possible ways and return
     * a list of substituted types. We need to do this substitution into
     * all types in the input list of type applications: tappl. *)

    (* Given a type application tl (a list of types), substitute gound types tgs into
     * all non-ground types in tl and return a list of ground type applications. *)
    let subst_in_tappl tl tgs =

      (* Given a list of types (a type application), substitute tgs into the first non-ground type and
       *  return a list of type apps. This is similar to what was done in subst_first_polyfun above. *)
      let subst_in_first_non_ground tl tgs =
        (* Separate tl into three parts, in order.
         * (1) initial ground types. (2) first non-ground type (3) rest *)
        let rec separator tlist l1 =
          match tlist with
          | [] -> (l1, None, [])
          | cur :: rest ->
            if TU.is_ground_type cur
            then
              separator rest (l1 @ [cur])
            else
              (l1, Some cur, rest)
        in
        let (l1, non_ground_opt, l2) = separator tl [] in
        (* If there is no ground type, return tl back. That's the result. *)
        match non_ground_opt with
        | None -> pure [tl]
        | Some ngt ->
          let%bind gts = eliminate_tvars ngt tgs in
          mapM ~f:(fun gt -> pure (l1 @ [gt] @ l2)) gts
      in

      (* Call subst_in_first_non_ground until no non-ground type is left. *)
      let rec subst_all tll tgs =
        match tll with
        | [] -> pure []
        | tl :: _ ->
          (* If tl has a non-ground type, then we substitute in all of tell. *)
          if List.exists (TU.is_ground_type) tl
          then
            let%bind tll' = mapM ~f:(fun tl -> subst_in_first_non_ground tl tgs) tll in
            let tll'' =  List.concat tll' in
            subst_all tll'' tgs
          else
            pure tll
      in
        subst_all [tl] tgs
    in

    (* We're almost done. Just go through each appl in tappll and call
     * subst_in_tappl for each and accumulate a result. *)
    foldM ~f:(fun  acc tappl ->
        let%bind tappll' = subst_in_tappl tappl gts in
        pure @@ List.fold_left (fun acc tapp ->
          Utils.list_add_unique ~equal:(TU.type_equiv_list) acc tapp
        ) acc tappll'
    ) ~init:[] tappll


  (* Given a polymorphic type "t", return a list of concrete types from
   * tappl that "t" must be instantiated with. The only simple improvement
   * we currently have on top of "every TFun is instantiated with all types
   * in tappl" is the following:
   * The expression
   *     let a = tfun 'A => (anything but another tfun) ...  
   *      ...
   *     let x = @b Int32 Int64 in
   * Here, "a" can only be instantiated with Int64 and not Int32.
   * To compute this, we look at the number "n" of consecutive PolyFun starting
   * from "t". From the list of type applications in "tappl", we select only
   * those whose lengths (or suffixes whose lengths) are lesser than or equal to "n".
   * TODO: Improving the way we organize `tapps` ("tappl") can help make this
   * computation faster.
   *)
  let compute_instantiations t tappl =
    (* compute the number "n" of consecutive PolyFun starting from "t" *)
    let ntfuns t =
      let rec ntfuns' n t =
        match t with
        | PolyFun (_, t') -> ntfuns' (n+1) t'
        | _ -> n
      in
      ntfuns' 0 t
    in
    let nt = ntfuns t in
    (* Add a type to a list of types if it doensn't already contain it. *)
    let add_to_list t ls =
      if List.exists (fun t' -> TU.type_equiv t t') ls then ls else (t :: ls)
    in
    (* Return the last "n" or lesser elements of ls. *)
    let n_tl n ls =
      snd @@ List.fold_right (fun l (nacc, lacc) ->
        if nacc < n then (nacc+1, l :: lacc) else (nacc, lacc)
      ) ls (0, [])
    in
    (* Add suffixes of length <= nt of each entry in tappl, to our return value. *)
    List.fold_left (fun acc tl ->
      (* pick the last nt elements *)
      let ntl = n_tl nt tl in
      (* and add them to acc *)
      List.fold_left (fun acc' t -> add_to_list t acc') acc ntl
    ) [] tappl

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
      let insts = compute_instantiations (ER.get_type erep).tp tappl in
      (* ******************************************************************************* *)
        let lc = ER.get_loc erep in
        Printf.printf "Instantiating at (%s,%d,%d) with types: " lc.fname lc.lnum lc.cnum;
        List.iter (fun t -> Printf.printf "%s" (pp_typ t)) insts;
      (* ******************************************************************************* *)
      let%bind tfuns = mapM ~f:(fun t ->
        if (free_tvars t) <> [] || not (TU.is_ground_type t)
        then
          fail1 "Internal error. Attempting to instantiate with a non-ground type or type variable." (ER.get_loc erep)
        else
          let ibody = MS.subst_type_in_expr v t body in
          let%bind ibody' = monomorphize_expr ibody tappl in
          pure (t, ibody')
      ) insts in
      pure ((MS.TFunMap ((v, body'), tfuns)), erep)
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
    let%bind tappl' = analyze_module cmod rlibs elibs in
    let%bind tappl = postprocess_tappl tappl' in

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
