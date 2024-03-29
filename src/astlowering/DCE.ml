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
open ExplicitAnnotationSyntax
open Scilla_base
open PrettyPrinters
module Literal = Literal.GlobalLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
module GC = GasCharge.ScillaGasCharge (Identifier.Name)

module ScillaCG_Dce = struct
  open ExplicitAnnotationSyntax.EASyntax

  let rec get_const_gas = function
    | GC.StaticCost i -> Some i
    | SizeOf _ | ValueOf _ | LengthOf _ | MapSortCost _ -> None
    | SumOf (g1, g2) -> (
        match (get_const_gas g1, get_const_gas g2) with
        | Some i1, Some i2 -> Some (i1 + i2)
        | _ -> None)
    | ProdOf (g1, g2) -> (
        match (get_const_gas g1, get_const_gas g2) with
        | Some i1, Some i2 -> Some (i1 * i2)
        | _ -> None)
    | MinOf (g1, g2) -> (
        match (get_const_gas g1, get_const_gas g2) with
        | Some i1, Some i2 -> Some (Int.min i1 i2)
        | _ -> None)
    | DivCeil (g, pi) -> (
        let div_ceil x y = if x % y = 0 then x / y else (x / y) + 1 in
        match get_const_gas g with
        | Some i1 -> Some (div_ceil i1 (GasCharge.PositiveInt.get pi))
        | _ -> None)
    | LogOf g -> (
        (* LogOf(I) = int (log(float(I) + 1.0)) + 1 *)
        let logger uf =
          let f =
            match uf with GasCharge.GFloat f -> f | GInt i -> Float.of_int i
          in
          (Float.to_int @@ Float.log (f +. 1.0)) + 1
        in
        match get_const_gas g with
        | Some i1 -> Some (logger (GInt i1))
        | _ -> None)

  let rec gas_get_vars = function
    | GC.StaticCost _ -> []
    | SizeOf v | ValueOf v | LengthOf v | MapSortCost v ->
        [ Identifier.mk_id v empty_annot ]
    | SumOf (g1, g2) | ProdOf (g1, g2) | MinOf (g1, g2) ->
        gas_get_vars g1 @ gas_get_vars g2
    | DivCeil (g, _) | LogOf g -> gas_get_vars g

  (* Mark an expr with (Some c) if it can be replaced
   * with a constant gas charge of c. Otherwise None.
   *)
  let rec expr_constgas (e, rep) =
    match e with
    | Literal _ | Var _ | Message _ | Constr _ | Fixpoint _ | Fun _ | TFun _
    | Builtin _ ->
        (* All of these have a cost wrapper.
         * AnnotationExplicitizer added one for Builtin.
         * The remaining get it from Gas.ml itself.
         *)
        (e, { rep with ea_auxi = Some 0 })
    | App _ | TApp _ ->
        (* We don't know what's going to happen in here. *)
        (e, rep)
    | Let (x, t, lhs, rhs) -> (
        let ((_, rhs_rep) as rhs') = expr_constgas rhs in
        let ((_, lhs_rep) as lhs') = expr_constgas lhs in
        match (lhs_rep, rhs_rep) with
        | ( { ea_tp = _; ea_loc = _; ea_auxi = Some c1 },
            { ea_tp = _; ea_loc = _; ea_auxi = Some c2 } ) ->
            (Let (x, t, lhs', rhs'), { rep with ea_auxi = Some (c1 + c2) })
        | _ -> (Let (x, t, lhs', rhs'), rep))
    | MatchExpr (p, clauses) -> (
        (* Check that all branches have the same statically known cost. *)
        let uniform_cost, clauses' =
          List.fold_map ~init:None clauses ~f:(fun acc_rep (pat, e) ->
              let ((_, rep') as e') = expr_constgas e in
              match (acc_rep, rep') with
              | ( Some (Some bcost),
                  { ea_tp = _; ea_loc = _; ea_auxi = Some repv } )
                when bcost = repv ->
                  (Some (Some bcost), (pat, e'))
              | None, { ea_tp = _; ea_loc = _; ea_auxi = Some repv } ->
                  (Some (Some repv), (pat, e'))
              | _, _ -> (Some None, (pat, e')))
        in
        match uniform_cost with
        | Some (Some cost) ->
            (* Every branch has the same statically known cost. *)
            (MatchExpr (p, clauses'), { rep with ea_auxi = Some cost })
        | None ->
            (* No branch *)
            (MatchExpr (p, clauses'), { rep with ea_auxi = Some 0 })
        | Some None -> (MatchExpr (p, clauses'), rep))
    | GasExpr (g, e) -> (
        let ((_, { ea_tp = _; ea_loc = _; ea_auxi = ecost }) as e') =
          expr_constgas e
        in
        match (get_const_gas g, ecost) with
        | Some gc, Some ec ->
            (GasExpr (g, e'), { rep with ea_auxi = Some (gc + ec) })
        | _, _ -> (GasExpr (g, e'), rep))

  (* Eliminate dead-code in e (primarily with let-in expressions),
   * simultaneously returning the free variables in e. *)
  let rec expr_dce (e, rep) =
    match e with
    | Literal _ -> ((e, rep), [])
    | Var v | TApp (v, _) -> ((e, rep), [ v ])
    | Message mlist ->
        let fvars =
          List.filter_map
            ~f:(fun (_, pl) ->
              match pl with MVar v -> Some v | MLit _ -> None)
            mlist
        in
        ((e, rep), fvars)
    | App (f, alist) -> ((e, rep), f :: alist)
    | Constr (_, _, alist) | Builtin (_, _, alist) -> ((e, rep), alist)
    | Fixpoint (a, t, body) ->
        let body', fv = expr_dce body in
        let fv' = List.filter ~f:(fun i -> not @@ Identifier.equal i a) fv in
        ((Fixpoint (a, t, body'), rep), fv')
    | Fun (a, t, body) ->
        let body', fv = expr_dce body in
        let fv' = List.filter ~f:(fun i -> not @@ Identifier.equal i a) fv in
        ((Fun (a, t, body'), rep), fv')
    | Let (x, t, ((_, lhs_rep) as lhs), rhs) ->
        let ((_, rhs'_rep) as rhs'), fvrhs = expr_dce rhs in
        let fvrhs_no_x =
          List.filter ~f:(fun i -> not @@ Identifier.equal i x) fvrhs
        in
        if
          (* Does LHS have a use in RHS? *)
          List.mem fvrhs x ~equal:Identifier.equal
          (* Is the gas-cost of LHS statically unknown? *)
          || Option.is_none lhs_rep.ea_auxi
        then
          (* LHS cannot be removed. *)
          let lhs', fvlhs = expr_dce lhs in
          let fv = Identifier.dedup_id_list (fvlhs @ fvrhs_no_x) in
          ((Let (x, t, lhs', rhs'), rep), fv)
        else
          let gc = Option.value_exn lhs_rep.ea_auxi in
          (* LHS dead, and can be replaced by static gas cost. *)
          DebugMessage.plog
            (located_msg
               (sprintf "Replacing dead expression %s with gas cost %d\n"
                  (Identifier.as_string x) gc)
               rep.ea_loc);
          ( ( GasExpr (GC.StaticCost gc, rhs'),
              { rhs'_rep with ea_auxi = rep.ea_auxi } ),
            fvrhs_no_x )
    | MatchExpr (p, clauses) ->
        let clauses', fvl =
          List.unzip
          @@ List.map clauses ~f:(fun (pat, e) ->
                 let e', fvl = expr_dce e in
                 let bounds = get_pattern_bounds pat in
                 (* Remove bound variables from the free variable list. *)
                 let fvl' =
                   List.filter fvl ~f:(fun a ->
                       not (Identifier.is_mem_id a bounds))
                 in
                 ((pat, e'), fvl'))
        in
        let fvl' = Identifier.dedup_id_list (p :: List.concat fvl) in
        ((MatchExpr (p, clauses'), rep), fvl')
    | TFun (v, e) ->
        let e', fv = expr_dce e in
        ((TFun (v, e'), rep), fv)
    | GasExpr (g, e) ->
        let e', fv = expr_dce e in
        let fv' = Identifier.dedup_id_list (gas_get_vars g @ fv) in
        ((GasExpr (g, e'), rep), fv')

  (* Eliminate dead-code in a list of statements,
   * simultaneously returning the free variables. *)
  let rec stmts_dce stmts =
    match stmts with
    | (s, rep) :: rest_stmts -> (
        let rest', live_vars' = stmts_dce rest_stmts in
        match s with
        | Load (x, m) ->
            if Identifier.is_mem_id x live_vars' then
              ((s, rep) :: rest', Identifier.dedup_id_list (m :: live_vars'))
            else (rest', live_vars')
        | RemoteLoad (x, addr, m) ->
            if Identifier.is_mem_id x live_vars' then
              ( (s, rep) :: rest',
                Identifier.dedup_id_list (addr :: m :: live_vars') )
            else (rest', live_vars')
        | TypeCast (x, a, _) ->
            if Identifier.is_mem_id x live_vars' then
              ((s, rep) :: rest', Identifier.dedup_id_list (a :: live_vars'))
            else (rest', live_vars')
        | Store (_, i) ->
            ((s, rep) :: rest', Identifier.dedup_id_list @@ (i :: live_vars'))
        | MapUpdate (i, il, io) ->
            let live_vars =
              match io with Some ii -> i :: ii :: il | None -> i :: il
            in
            ( (s, rep) :: rest',
              Identifier.dedup_id_list @@ live_vars @ live_vars' )
        | MapGet (x, i, il, _) ->
            if Identifier.is_mem_id x live_vars' then
              ( (s, rep) :: rest',
                Identifier.dedup_id_list (i :: (il @ live_vars')) )
            else (
              DebugMessage.plog
                (located_msg
                   (sprintf "Eliminated dead MapGet assignment to %s\n"
                      (Identifier.as_string x))
                   rep.ea_loc);
              (rest', live_vars'))
        | RemoteMapGet (x, addr, i, il, _) ->
            if Identifier.is_mem_id x live_vars' then
              ( (s, rep) :: rest',
                Identifier.dedup_id_list (addr :: i :: (il @ live_vars')) )
            else (
              DebugMessage.plog
                (located_msg
                   (sprintf "Eliminated dead MapGet assignment to %s\n"
                      (Identifier.as_string x))
                   rep.ea_loc);
              (rest', live_vars'))
        | ReadFromBC (x, bci) ->
            let new_lives =
              match bci with
              | Timestamp v -> [ v ]
              | ReplicateContr (addr, iparams) -> [ addr; iparams ]
              | CurBlockNum | ChainID -> []
            in
            if Identifier.is_mem_id x live_vars' then
              ( (s, rep) :: rest',
                Identifier.dedup_id_list @@ new_lives @ live_vars' )
            else (rest', live_vars')
        | AcceptPayment -> ((s, rep) :: rest', live_vars')
        | GasStmt g ->
            ( (s, rep) :: rest',
              Identifier.dedup_id_list (gas_get_vars g @ live_vars') )
        | SendMsgs v | CreateEvnt v ->
            ((s, rep) :: rest', Identifier.dedup_id_list @@ (v :: live_vars'))
        | Throw topt -> (
            match topt with
            | Some t ->
                ( (s, rep) :: rest',
                  Identifier.dedup_id_list @@ (t :: live_vars') )
            | None -> ((s, rep) :: rest', Identifier.dedup_id_list @@ live_vars')
            )
        | CallProc (p, al) ->
            ( (s, rep) :: rest',
              Identifier.dedup_id_list (p :: (al @ live_vars')) )
        | Iterate (l, p) ->
            ((s, rep) :: rest', Identifier.dedup_id_list (l :: p :: live_vars'))
        | Bind (i, ((_, erep) as e)) ->
            if Identifier.is_mem_id i live_vars' || Option.is_none erep.ea_auxi
            then
              (* Either i is live or e cannot be replaced with static gas cost. *)
              let e', e_live_vars = expr_dce e in
              let s' = Bind (i, e') in
              ( (s', rep) :: rest',
                Identifier.dedup_id_list @@ e_live_vars @ live_vars' )
            else
              ( (GasStmt (GC.StaticCost (Option.value_exn erep.ea_auxi)), rep)
                :: rest',
                live_vars' )
        | MatchStmt (i, pslist) ->
            let pslist', live_vars =
              List.unzip
              @@ List.map pslist ~f:(fun (pat, stmts) ->
                     let stmts', fvl = stmts_dce stmts in
                     let bounds = get_pattern_bounds pat in
                     (* Remove bound variables from the free variable list. *)
                     let fvl' =
                       List.filter fvl ~f:(fun a ->
                           not (Identifier.is_mem_id a bounds))
                     in
                     (* We do not eliminate empty branches as that messes up the FlattenPatterns pass. *)
                     ((pat, stmts'), fvl'))
            in
            if List.is_empty pslist' then (rest', live_vars')
            else
              let lv =
                Identifier.dedup_id_list
                @@ (i :: (List.concat live_vars @ live_vars'))
              in
              ((MatchStmt (i, pslist'), rep) :: rest', lv))
    | [] -> ([], [])

  let rec stmt_constgas (s, srep) =
    match s with
    | Load _ | RemoteLoad _ | TypeCast _ | Store _ | MapUpdate _ | MapGet _
    | RemoteMapGet _ | ReadFromBC _ | AcceptPayment | GasStmt _ | SendMsgs _
    | CreateEvnt _ | Throw _ | CallProc _ | Iterate _ ->
        (s, srep)
    | Bind (i, e) -> (Bind (i, expr_constgas e), srep)
    | MatchStmt (b, plist) ->
        ( MatchStmt
            ( b,
              List.map plist ~f:(fun (p, sts) ->
                  (p, List.map sts ~f:stmt_constgas)) ),
          srep )

  let comp_constgas comp =
    { comp with comp_body = List.map comp.comp_body ~f:stmt_constgas }

  let lib_entries_constgas lentries =
    List.map lentries ~f:(fun lentry ->
        match lentry with
        | LibVar (i, topt, lexp) -> LibVar (i, topt, expr_constgas lexp)
        | LibTyp _ -> lentry)

  let lib_constgas lib =
    { lib with lentries = lib_entries_constgas lib.lentries }

  let rec libtree_constgas libt =
    let deps' = List.map ~f:libtree_constgas libt.deps in
    let libn' = lib_constgas libt.libn in
    { libn = libn'; deps = deps' }

  (* Function to dce library entries. *)
  let dce_lib_entries libname_opt lentries freevars =
    let lentries', freevars', eliminated_gas =
      List.fold_right lentries ~init:([], freevars, 0)
        ~f:(fun lentry (acc_lentries, acc_freevars, acc_eliminated_gas) ->
          match lentry with
          | LibVar (i, topt, ((_, lrep) as lexp)) ->
              let freevars_no_i =
                List.filter
                  ~f:(fun i' -> not @@ Identifier.equal i' i)
                  acc_freevars
              in
              if
                Identifier.is_mem_id i acc_freevars
                || Option.is_none lrep.ea_auxi
              then
                (* Either i is used or cannot be replaced by a const gas expr. *)
                let lexp', fv = expr_dce lexp in
                ( LibVar (i, topt, lexp') :: acc_lentries,
                  Identifier.dedup_id_list @@ fv @ freevars_no_i,
                  acc_eliminated_gas )
              else
                let gc = Option.value_exn lrep.ea_auxi in
                DebugMessage.plog
                  (located_msg
                     (sprintf
                        "Replacing dead library value %s with gas cost %d\n"
                        (Identifier.as_string i) gc)
                     (Identifier.get_rep i).ea_loc);
                (acc_lentries, freevars_no_i, acc_eliminated_gas + gc)
          | LibTyp _ ->
              (lentry :: acc_lentries, acc_freevars, acc_eliminated_gas))
    in
    if eliminated_gas > 0 then
      (* Add a new entry to charge all the gas that we eliminated. *)
      let ea =
        {
          empty_annot with
          ea_auxi = Some eliminated_gas;
          ea_tp = Some (Type.PrimType (Int_typ Bits32));
        }
      in
      let gentry =
        ( GasExpr
            ( GC.StaticCost eliminated_gas,
              ( Literal
                  (Literal.IntLit (Int32L (Int32.of_int_exn eliminated_gas))),
                ea ) ),
          ea )
      in
      let libname = Option.value libname_opt ~default:"" in
      ( LibVar
          ( Identifier.mk_id
              (Identifier.Name.parse_simple_name
                 (LoweringUtils.tempname ("_gas_charge_acc" ^ libname)))
              ea,
            None,
            gentry )
        :: lentries',
        freevars' )
    else (lentries', freevars')

  (* Function to dce a library. *)
  let dce_lib lib freevars =
    let lentries', freevars' =
      dce_lib_entries
        (Some (Identifier.as_string lib.lname))
        lib.lentries freevars
    in
    let lib' = { lname = lib.lname; lentries = lentries' } in
    (lib', freevars')

  (* DCE the library tree. *)
  let rec dce_libtree libt freevars =
    let libn', freevars' = dce_lib libt.libn freevars in
    let deps', freevars'' =
      List.unzip @@ List.map ~f:(fun dep -> dce_libtree dep freevars') libt.deps
    in
    let libt' = { libn = libn'; deps = deps' } in
    (* Dependent libraries can't make our free variables in libt dead. *)
    let freevars''' =
      Identifier.dedup_id_list @@ freevars' @ List.concat freevars''
    in
    (libt', freevars''')

  let cmod_dce (cmod'' : cmodule) rlibs'' elibs'' =
    (* Analysis for const gas. *)
    let rlibs = lib_entries_constgas rlibs'' in
    let elibs = List.map elibs'' ~f:libtree_constgas in
    let cmod =
      {
        cmod'' with
        libs = Option.map cmod''.libs ~f:lib_constgas;
        contr =
          {
            cmod''.contr with
            ccomps = List.map cmod''.contr.ccomps ~f:comp_constgas;
          };
      }
    in

    (* DCE all contract components. *)
    let comps', comps_lv =
      List.unzip
      @@ List.map
           ~f:(fun comp ->
             let body', lv = stmts_dce comp.comp_body in
             let lv' =
               List.filter lv ~f:(fun a ->
                   not
                     (List.exists comp.comp_params ~f:(fun (b, _) ->
                          Identifier.equal a b)))
             in
             ({ comp with comp_body = body' }, lv'))
           cmod.contr.ccomps
    in
    let comps_lv' = Identifier.dedup_id_list (List.concat comps_lv) in

    (* DCE field initializations. *)
    let fields', fields_lv =
      List.unzip
      @@ List.map
           ~f:(fun (i, t, fexp) ->
             let fexp', fields_lv = expr_dce fexp in
             ((i, t, fexp'), fields_lv))
           cmod.contr.cfields
    in

    (* DCE contract constraint. *)
    let cconstraint', cconstraint_lv = expr_dce cmod.contr.cconstraint in
    let cconstraint_lv' =
      Identifier.dedup_id_list (List.concat fields_lv @ cconstraint_lv)
    in

    (* Remove contract parameters from live variable list. *)
    let paraml = List.map cmod.contr.cparams ~f:fst in
    let lv_contract =
      List.filter (comps_lv' @ cconstraint_lv') ~f:(fun a ->
          not (Identifier.is_mem_id a paraml))
    in

    (* DCE contract library. *)
    let clibs', lv_clibs =
      match cmod.libs with
      | Some l ->
          let clibs', freevars' = dce_lib l lv_contract in
          (Some clibs', freevars')
      | None -> (None, lv_contract)
    in

    let elibs', fv_elibs =
      List.unzip @@ List.map ~f:(fun elib -> dce_libtree elib lv_clibs) elibs
    in
    let fv_elibs' = Identifier.dedup_id_list (List.concat fv_elibs) in

    (* DCE recursion libs. *)
    let rlibs', _fv_rlibs = dce_lib_entries None rlibs fv_elibs' in

    (* We're done. *)
    let contr' =
      {
        cmod.contr with
        cconstraint = cconstraint';
        ccomps = comps';
        cfields = fields';
      }
    in
    let cmod' = { cmod with contr = contr'; libs = clibs' } in

    (* Return back the whole program, transformed. *)
    (cmod', rlibs', elibs')

  (* A wrapper to be used from expr_compiler. *)
  let expr_dce_wrapper rlibs'' elibs'' e'' =
    (* Analysis for const gas. *)
    let rlibs = lib_constgas rlibs'' in
    let elibs = List.map elibs'' ~f:libtree_constgas in
    let e = expr_constgas e'' in

    (* Actual DCE. *)
    let e', fv_e = expr_dce e in
    let elibs', fv_elibs =
      List.unzip @@ List.map ~f:(fun elib -> dce_libtree elib fv_e) elibs
    in
    let fv_elibs' = Identifier.dedup_id_list (List.concat fv_elibs) in
    let rlibs', _fv_rlibs = dce_lib rlibs fv_elibs' in
    (rlibs', elibs', e')
end
