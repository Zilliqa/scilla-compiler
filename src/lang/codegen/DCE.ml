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

(* A simple dead code elimination pass. This needs to be run before the 
 * Monomorphize pass to keep the number of instantiations tractable.
 * Without it, including a library (such as ListUtils) will include all
 * its definitions in the whole program being compiled, resulting in
 * an exponential blow-up of the number of of instantiations. *)

open Core
open Syntax
open ExplicitAnnotationSyntax

(* Print a message with location info. TODO: Move to PrettyPrinters *)
let located_msg msg loc =
  let open ErrorUtils in
  (sprintf "%s:%d:%d: %s" loc.fname loc.lnum loc.cnum msg)

(* TODO: Move these to Syntax.ml *)
let equal_id a b = get_id a = get_id b
let compare_id a b = compare (get_id a) (get_id b)
let dedup_id_list l = List.dedup_and_sort ~compare:compare_id l
let mem_id i l = List.exists l ~f:(fun b -> get_id b = get_id i)

 module ScillaCG_Dce = struct

  open ExplicitAnnotationSyntax.EASyntax

  (* Eliminate dead-code in e (primarily with let-in expressions),
   * simultaneously returning the free variables in e. *)
  let rec expr_dce (e, rep) = match e with
    | Literal _ -> (e, rep), []
    | Var v | TApp (v, _) -> (e, rep), [v]
    |  Message mlist  ->
      let fvars = List.filter_map ~f:(fun (_, pl) -> match pl with MVar v -> Some v | MLit _ -> None) mlist in
      (e, rep), fvars
    | App (f, alist) -> (e, rep), f::alist
    | Constr (_, _, alist) | Builtin (_, alist) -> (e, rep), alist
    | Fixpoint (a, t, body) ->
      let (body', fv) = expr_dce body in
      let fv' = List.filter ~f:(fun i -> get_id i <> get_id a) fv in
      (Fixpoint (a, t, body'), rep), fv'
    | Fun (a, t, body) ->
      let (body', fv) = expr_dce body in
      let fv' = List.filter ~f:(fun i -> get_id i <> get_id a) fv in
      (Fun (a, t, body'), rep), fv'
    | Let (x, t, lhs, rhs) ->
      let (rhs', fvrhs) = expr_dce rhs in
      if List.mem fvrhs x ~equal:(fun a b -> get_id a = get_id b)
      then
        (* LHS not dead. *)
        let (lhs', fvlhs) = expr_dce lhs in
        let fv = dedup_id_list (fvlhs @ fvrhs) in
        (Let (x, t, lhs', rhs'), rep), fv
      else
        (* LHS Dead. *)
        (DebugMessage.plog (located_msg (sprintf "Eliminated dead expression %s" (get_id x)) rep.ea_loc);
        (rhs', fvrhs))
    | MatchExpr (p, clauses) ->
      let (clauses', fvl) = List.unzip @@ 
        List.map clauses ~f:(fun (pat, e) ->
          let (e', fvl) = expr_dce e in
          let bounds = get_pattern_bounds pat in
          (* Remove bound variables from the free variable list. *)
          let fvl' = List.filter fvl ~f:(fun a -> not (mem_id a bounds)) in
          ((pat, e'), fvl')
        )
      in
      let fvl' = dedup_id_list (List.concat fvl) in
      (MatchExpr(p, clauses'), rep), fvl'
    | TFun (v, e) ->
      let (e', fv) = expr_dce e in
      (TFun (v, e'), rep), fv

  (* Eliminate dead-code in a list of staements,
   * simultaneously returning the free variables. *)
  let rec stmts_dce stmts = match stmts with
    | (s, rep) :: rest_stmts ->
      let (rest', live_vars') = stmts_dce rest_stmts in
      (match s with
      | Load (x, m) ->
        if mem_id x live_vars'
        then ((s, rep) :: rest'), m :: live_vars'
        else rest', live_vars'
      | Store (_, i) ->
        ((s, rep) :: rest'), dedup_id_list @@ i :: live_vars'
      | MapUpdate (i, il, io) ->
        let live_vars = match io with | Some ii -> i :: ii :: il | None -> i :: il in
        ((s, rep) :: rest'), dedup_id_list @@ live_vars @ live_vars'
      | MapGet (x, i, il, _) ->
        if mem_id x live_vars'
        then ((s, rep) :: rest'), dedup_id_list (i :: (il @ live_vars'))
        else
          (DebugMessage.plog (located_msg (sprintf "Eliminated dead MapGet assignment to %s" (get_id x)) rep.ea_loc);
          rest', live_vars')
      | ReadFromBC (x, _) ->
        if mem_id x live_vars'
        then ((s, rep) :: rest'), live_vars'
        else rest', live_vars'
      | AcceptPayment -> ((s, rep) :: rest'), live_vars'
      | SendMsgs v | CreateEvnt v -> ((s, rep) :: rest'), dedup_id_list @@ v :: live_vars'
      | Throw t -> ((s, rep) :: rest'), dedup_id_list @@ t :: live_vars'
      | CallProc (p, al) -> ((s, rep) :: rest'), dedup_id_list (p :: (al @ live_vars'))
      | Bind (i , e) ->
        if mem_id i live_vars'
        then
          let (e', e_live_vars) = expr_dce e in
          let s' = Bind(i, e') in
          ((s', rep) :: rest'), dedup_id_list @@ e_live_vars @ live_vars'
        else
          (rest', live_vars')
      | MatchStmt (i, pslist) ->
        let (pslist', live_vars) = List.unzip @@ List.filter_map pslist ~f:(fun (pat, stmts) ->
          let (stmts', fvl) = stmts_dce stmts in
          let bounds = get_pattern_bounds pat in
          (* Remove bound variables from the free variable list. *)
          let fvl' = List.filter fvl ~f:(fun a -> not (mem_id a bounds)) in
          (* Eliminate empty branches. *)
          if stmts' = [] then None else Some ((pat, stmts'), fvl')
        ) in
        if pslist' = []
        then rest', live_vars'
        else
          let lv = dedup_id_list @@ i :: ((List.concat live_vars) @ live_vars') in
          (MatchStmt(i, pslist'), rep) :: rest', lv
      )
    | [] -> ([], [])

  let cmod_dce cmod rlibs elibs =

    (* DCE all contract components. *)
    let (comps', comps_lv) = List.unzip @@ List.map ~f:(fun comp ->
      let (body', lv) = stmts_dce comp.comp_body in
      let lv' = List.filter lv ~f:
        (fun a -> not (List.exists comp.comp_params ~f:(fun (b, _) -> equal_id a b))) in
      { comp with comp_body = body' }, lv'
    ) cmod.contr.ccomps
    in
    let comps_lv' = dedup_id_list (List.concat comps_lv) in

    (* DCE field initializations. *)
    let (fields', fields_lv) = List.unzip @@ List.map ~f:(fun (i, t, fexp) ->
      let (fexp', fields_lv) = expr_dce fexp in
      (i, t, fexp'), fields_lv
    ) cmod.contr.cfields
    in
    let fields_lv' = dedup_id_list (List.concat fields_lv) in

    (* Remove contract parameters from live variable list. *)
    let paraml = List.map cmod.contr.cparams ~f:(fst) in
    let lv_contract = List.filter (comps_lv' @ fields_lv') 
        ~f:(fun a -> not (mem_id a paraml)) in

    (* Function to dce library entries. *)
    let rec dce_lib_entries lentries freevars =
      match lentries with
      | lentry :: rentries ->
        let (lentries', freevars') = dce_lib_entries rentries freevars in
        (match lentry with
        | LibVar (i, lexp) ->
          if mem_id i freevars'
          then
            let (lexp', fv) = expr_dce lexp in
            LibVar(i, lexp') :: lentries', dedup_id_list @@ fv @ freevars'
          else
            (DebugMessage.plog (located_msg (sprintf "Eliminated dead library value %s" (get_id i)) (get_rep i).ea_loc);
            lentries', freevars')
        | LibTyp _ ->
          lentry :: lentries', freevars'
        )
      | [] -> [], freevars
    in

    (* Function to dce a library. *)
    let dce_lib lib freevars =
      let (lentries', freevars') = dce_lib_entries lib.lentries freevars in
      let lib' = { lname = lib.lname; lentries = lentries' } in
      lib', freevars'
    in

    (* DCE contract library. *)
    let (clibs', lv_clibs) =
      match cmod.libs with
      | Some l ->
        let (clibs', freevars') = dce_lib l lv_contract in
        (Some clibs', freevars')
      | None -> None, lv_contract
    in

    (* DCE the library tree. *)
    let rec dce_libtree libt freevars =
      let (libn', freevars') = dce_lib libt.libn freevars in
      let (deps', freevars'') = List.unzip @@ List.map ~f:(fun dep ->
        dce_libtree dep freevars'
      ) libt.deps in
      let libt' = { libn = libn'; deps = deps' } in
      (libt', List.concat freevars'')
    in
    let (elibs', _fv_elibs) = List.unzip @@ List.map ~f:(fun elib ->
      dce_libtree elib lv_clibs
    ) elibs in

    (* We don't DCE recursion libs. *)

    let contr' = { cmod.contr with ccomps = comps'; cfields = fields' } in
    let cmod' = { cmod with contr = contr'; libs = clibs' } in

    (* Return back the whole program, transformed. *)
    (cmod', rlibs, elibs')

end