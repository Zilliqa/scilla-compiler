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
  This file translates FlatPatSyntax to Uncurried_Syntax.
  This involves splitting FlatPatSyntax.App into a sequence
  of Uncurried_Syntax.App nodes. All types and type annotations
  are translated to Uncurried_Syntax.typ. 

  Once the AST has been translated, combine curried functions
  into functions that take multiple arguments and rewrite their
  partial applications (sequence of Uncurried_Syntax.App) into
  a application. This optimization combines multiple functions
  calls into a single one, making calls more efficient.

*)

open Core_kernel
module Array = BatDynArray
open Result.Let_syntax
open Scilla_base
module Literal = Literal.GlobalLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open MonadUtil
open FlatPatternSyntax
open UncurriedSyntax

module ScillaCG_Uncurry = struct
  module FPS = FlatPatSyntax
  module UCS = Uncurried_Syntax
  open FPS

  let rec translate_typ = function
    | Type.PrimType pt -> UCS.PrimType pt
    | MapType (kt, vt) -> UCS.MapType (translate_typ kt, translate_typ vt)
    | FunType (argt, rett) ->
        UCS.FunType ([ translate_typ argt ], translate_typ rett)
    | ADT (tname, tlist) -> UCS.ADT (tname, List.map tlist ~f:translate_typ)
    | TypeVar tv -> UCS.TypeVar (UCS.mk_noannot_id tv)
    | PolyFun (tv, t) -> UCS.PolyFun (UCS.mk_noannot_id tv, translate_typ t)
    | Unit -> UCS.Unit
    | Address tlo ->
        UCS.Address
          (Option.map
             ~f:(fun tl ->
               Type.IdLoc_Comp.Map.fold ~init:IdLoc_Comp.Map.empty
                 ~f:(fun ~key:id ~data:t acc ->
                   IdLoc_Comp.Map.set acc ~key:id ~data:(translate_typ t))
                 tl)
             tlo)

  let rec translate_literal = function
    | Literal.StringLit s -> pure @@ UCS.StringLit s
    | IntLit i -> pure @@ UCS.IntLit i
    | UintLit u -> pure @@ UCS.UintLit u
    | BNum s -> pure @@ UCS.BNum s
    | ByStrX bstrx -> pure @@ UCS.ByStrX bstrx
    | ByStr bstr -> pure @@ UCS.ByStr bstr
    | Msg ml ->
        let%bind ml' =
          mapM ml ~f:(fun (s, t, l) ->
              let t' = translate_typ t in
              let%bind l' = translate_literal l in
              pure (s, t', l'))
        in
        pure (UCS.Msg ml')
    | Map ((kt, vt), htbl) ->
        let htbl' = Caml.Hashtbl.create (Caml.Hashtbl.length htbl) in
        let htlist = Caml.Hashtbl.fold (fun k v acc -> (k, v) :: acc) htbl [] in
        let%bind _ =
          forallM
            ~f:(fun (k, v) ->
              let%bind k' = translate_literal k in
              let%bind v' = translate_literal v in
              pure @@ Caml.Hashtbl.add htbl' k' v')
            htlist
        in
        let kt' = translate_typ kt in
        let vt' = translate_typ vt in
        pure @@ UCS.Map ((kt', vt'), htbl')
    (* A constructor in HNF *)
    | ADTValue (tname, tl, ll) ->
        let%bind ll' = mapM ll ~f:translate_literal in
        pure @@ UCS.ADTValue (tname, List.map tl ~f:translate_typ, ll')
    | Clo _ | TAbs _ ->
        fail0 "Uncurry: internal error: cannot translate runtime literal."

  let translate_eannot = function
    | { ExplicitAnnotationSyntax.ea_loc = l; ea_tp = Some t; ea_auxi = ai } ->
        { UCS.ea_loc = l; UCS.ea_tp = Some (translate_typ t); UCS.ea_auxi = ai }
    | { ea_loc = l; ea_tp = None; ea_auxi = ai } ->
        { UCS.ea_loc = l; UCS.ea_tp = None; UCS.ea_auxi = ai }

  let translate_var v =
    let rep' = translate_eannot (Identifier.get_rep v) in
    Identifier.mk_id (Identifier.get_id v) rep'

  let translate_payload = function
    | MLit l ->
        let%bind l' = translate_literal l in
        pure (UCS.MLit l')
    | MVar v -> pure @@ UCS.MVar (translate_var v)

  let translate_spattern_base = function
    | Wildcard -> UCS.Wildcard
    | Binder v -> UCS.Binder (translate_var v)

  let translate_spattern = function
    | Any p -> UCS.Any (translate_spattern_base p)
    | Constructor (s, plist) ->
        UCS.Constructor
          (translate_var s, List.map plist ~f:translate_spattern_base)

  let translate_in_expr newname (e, erep) =
    let rec go_expr (e, erep) =
      match e with
      | Literal l ->
          let%bind l' = translate_literal l in
          pure (UCS.Literal l', translate_eannot erep)
      | Var v -> pure (UCS.Var (translate_var v), translate_eannot erep)
      | Message m ->
          let%bind m' =
            mapM
              ~f:(fun (s, p) ->
                let%bind p' = translate_payload p in
                pure (s, p'))
              m
          in
          pure (UCS.Message m', translate_eannot erep)
      | App (a, l) ->
          let a' = translate_var a in
          (* Split the sequence of applications (which have currying semantics) into
           * multiple UCS.App expressions, each having non-currying semantics. *)
          let rec uncurry_app (previous_temp : UCS.eannot Identifier.t)
              remaining =
            match remaining with
            | [] ->
                let rep : Uncurried_Syntax.eannot =
                  {
                    ea_loc = erep.ea_loc;
                    ea_tp = (Identifier.get_rep previous_temp).ea_tp;
                    ea_auxi = (Identifier.get_rep previous_temp).ea_auxi;
                  }
                in
                pure (UCS.Var previous_temp, rep)
            | next :: remaining' -> (
                match (Identifier.get_rep previous_temp).ea_tp with
                | Some (UCS.FunType (_, pt_ret)) ->
                    let temp_rep : Uncurried_Syntax.eannot =
                      {
                        ea_loc = (Identifier.get_rep previous_temp).ea_loc;
                        ea_tp = Some pt_ret;
                        ea_auxi = (Identifier.get_rep previous_temp).ea_auxi;
                      }
                    in
                    let temp = newname (Identifier.as_string a) temp_rep in
                    let rep : Uncurried_Syntax.eannot =
                      {
                        ea_loc = erep.ea_loc;
                        ea_tp = temp_rep.ea_tp;
                        ea_auxi = erep.ea_auxi;
                      }
                    in
                    let lhs = (UCS.App (previous_temp, [ next ]), temp_rep) in
                    let%bind rhs = uncurry_app temp remaining' in
                    pure (UCS.Let (temp, None, lhs, rhs), rep)
                | _ ->
                    fail1
                      (sprintf
                         "Uncurry: internal error: type mismatch applying %s."
                         (Identifier.as_string a))
                      (Identifier.get_rep a).ea_loc)
          in
          uncurry_app a' (List.map l ~f:translate_var)
      | Constr (s, tl, il) ->
          let tl' = List.map tl ~f:translate_typ in
          let il' = List.map il ~f:translate_var in
          pure (UCS.Constr (translate_var s, tl', il'), translate_eannot erep)
      | Builtin ((i, rep), ts, il) ->
          let il' = List.map il ~f:translate_var in
          pure
            ( UCS.Builtin
                ((i, translate_eannot rep), List.map ~f:translate_typ ts, il'),
              translate_eannot erep )
      | Fixpoint (f, t, body) ->
          let%bind body' = go_expr body in
          pure
            ( UCS.Fixpoint (translate_var f, translate_typ t, body'),
              translate_eannot erep )
      | Fun (i, t, body) ->
          let%bind body' = go_expr body in
          pure
            ( UCS.Fun ([ (translate_var i, translate_typ t) ], body'),
              translate_eannot erep )
      | Let (i, topt, lhs, rhs) ->
          let%bind lhs' = go_expr lhs in
          let%bind rhs' = go_expr rhs in
          pure
            ( UCS.Let
                (translate_var i, Option.map ~f:translate_typ topt, lhs', rhs'),
              translate_eannot erep )
      | TFun (t, e) ->
          let%bind e' = go_expr e in
          pure (UCS.TFun (translate_var t, e'), translate_eannot erep)
      | TApp (i, tl) ->
          let tl' = List.map tl ~f:translate_typ in
          pure (UCS.TApp (translate_var i, tl'), translate_eannot erep)
      | MatchExpr (obj, clauses, joinopt) ->
          let%bind clauses' =
            mapM clauses ~f:(fun (p, rhs) ->
                let p' = translate_spattern p in
                let%bind rhs' = go_expr rhs in
                pure (p', rhs'))
          in
          let%bind joinopt' =
            option_mapM joinopt ~f:(fun (l, je) ->
                let l' = translate_var l in
                let%bind je' = go_expr je in
                pure (l', je'))
          in
          pure
            ( UCS.MatchExpr (translate_var obj, clauses', joinopt'),
              translate_eannot erep )
      | JumpExpr l ->
          pure (UCS.JumpExpr (translate_var l), translate_eannot erep)
      | GasExpr (g, e) ->
          let%bind e' = go_expr e in
          pure @@ (UCS.GasExpr (g, e'), translate_eannot erep)
    in

    go_expr (e, erep)

  let translate_in_stmts newname stmts =
    let rec go_stmts stmts =
      foldrM stmts ~init:[] ~f:(fun acc (stmt, srep) ->
          match stmt with
          | Load (x, m) ->
              let s' = UCS.Load (translate_var x, translate_var m) in
              pure @@ (s', translate_eannot srep) :: acc
          | RemoteLoad (x, addr, m) ->
              let s' =
                UCS.RemoteLoad
                  (translate_var x, translate_var addr, translate_var m)
              in
              pure @@ (s', translate_eannot srep) :: acc
          | Store (m, i) ->
              let s' = UCS.Store (translate_var m, translate_var i) in
              pure @@ (s', translate_eannot srep) :: acc
          | MapUpdate (i, il, io) ->
              let il' = List.map il ~f:translate_var in
              let io' = Option.map io ~f:translate_var in
              let s' = UCS.MapUpdate (translate_var i, il', io') in
              pure @@ (s', translate_eannot srep) :: acc
          | MapGet (i, i', il, b) ->
              let il' = List.map ~f:translate_var il in
              let s' = UCS.MapGet (translate_var i, translate_var i', il', b) in
              pure @@ (s', translate_eannot srep) :: acc
          | RemoteMapGet (i, addr, i', il, b) ->
              let il' = List.map ~f:translate_var il in
              let s' =
                UCS.RemoteMapGet
                  (translate_var i, translate_var addr, translate_var i', il', b)
              in
              pure @@ (s', translate_eannot srep) :: acc
          | ReadFromBC (i, s) ->
              let s' = UCS.ReadFromBC (translate_var i, s) in
              pure @@ (s', translate_eannot srep) :: acc
          | AcceptPayment ->
              let s' = UCS.AcceptPayment in
              pure @@ (s', translate_eannot srep) :: acc
          | SendMsgs m ->
              let s' = UCS.SendMsgs (translate_var m) in
              pure @@ (s', translate_eannot srep) :: acc
          | CreateEvnt e ->
              let s' = UCS.CreateEvnt (translate_var e) in
              pure @@ (s', translate_eannot srep) :: acc
          | Throw t ->
              let s' = UCS.Throw (Option.map ~f:translate_var t) in
              pure @@ (s', translate_eannot srep) :: acc
          | CallProc (p, al) ->
              let s' =
                UCS.CallProc (translate_var p, List.map ~f:translate_var al)
              in
              pure @@ (s', translate_eannot srep) :: acc
          | Iterate (l, p) ->
              let s' = UCS.Iterate (translate_var l, translate_var p) in
              pure @@ (s', translate_eannot srep) :: acc
          | Bind (i, e) ->
              let%bind e' = translate_in_expr newname e in
              let s' = UCS.Bind (translate_var i, e') in
              pure @@ (s', translate_eannot srep) :: acc
          | MatchStmt (obj, clauses, joinopt) ->
              let%bind clauses' =
                mapM clauses ~f:(fun (p, rhs) ->
                    let p' = translate_spattern p in
                    let%bind rhs' = go_stmts rhs in
                    pure (p', rhs'))
              in
              let%bind joinopt' =
                option_mapM joinopt ~f:(fun (l, je) ->
                    let l' = translate_var l in
                    let%bind je' = go_stmts je in
                    pure (l', je'))
              in
              pure
              @@ ( UCS.MatchStmt (translate_var obj, clauses', joinopt'),
                   translate_eannot srep )
                 :: acc
          | JumpStmt j ->
              pure
              @@ (UCS.JumpStmt (translate_var j), translate_eannot srep) :: acc
          | GasStmt g -> pure ((UCS.GasStmt g, translate_eannot srep) :: acc))
    in
    go_stmts stmts

  (* Transform each library entry. *)
  let translate_in_lib_entries newname lentries =
    mapM
      ~f:(fun lentry ->
        match lentry with
        | LibVar (i, topt, lexp) ->
            let%bind lexp' = translate_in_expr newname lexp in
            pure
            @@ UCS.LibVar
                 (translate_var i, Option.map ~f:translate_typ topt, lexp')
        | LibTyp (i, ls) ->
            let ls' =
              List.map ls ~f:(fun t ->
                  {
                    UCS.cname = translate_var t.cname;
                    UCS.c_arg_types = List.map ~f:translate_typ t.c_arg_types;
                  })
            in
            pure @@ UCS.LibTyp (translate_var i, ls'))
      lentries

  (* Function to flatten patterns in a library. *)
  let translate_in_lib newname lib =
    let%bind lentries' = translate_in_lib_entries newname lib.lentries in
    pure @@ { UCS.lname = translate_var lib.lname; lentries = lentries' }

  (* translate_in the library tree. *)
  let rec translate_in_libtree newname libt =
    let%bind deps' =
      mapM ~f:(fun dep -> translate_in_libtree newname dep) libt.deps
    in
    let%bind libn' = translate_in_lib newname libt.libn in
    pure @@ { UCS.libn = libn'; UCS.deps = deps' }

  let translate_in_module (cmod : cmodule) rlibs elibs =
    let newname = LoweringUtils.global_newnamer in

    (* Recursion libs. *)
    let%bind rlibs' = translate_in_lib_entries newname rlibs in
    (* External libs. *)
    let%bind elibs' =
      mapM ~f:(fun elib -> translate_in_libtree newname elib) elibs
    in

    (* Transform contract library. *)
    let%bind clibs' = option_mapM cmod.libs ~f:(translate_in_lib newname) in

    (* Translate fields and their initializations. *)
    let%bind fields' =
      mapM
        ~f:(fun (i, t, fexp) ->
          let%bind fexp' = translate_in_expr newname fexp in
          pure (translate_var i, translate_typ t, fexp'))
        cmod.contr.cfields
    in

    (* Translate all contract components. *)
    let%bind comps' =
      mapM
        ~f:(fun comp ->
          let%bind body' = translate_in_stmts newname comp.comp_body in
          pure
          @@ {
               UCS.comp_type = comp.comp_type;
               UCS.comp_name = translate_var comp.comp_name;
               UCS.comp_params =
                 List.map comp.comp_params ~f:(fun (i, t) ->
                     (translate_var i, translate_typ t));
               UCS.comp_body = body';
             })
        cmod.contr.ccomps
    in

    let contr' =
      {
        UCS.cname = translate_var cmod.contr.cname;
        UCS.cparams =
          List.map cmod.contr.cparams ~f:(fun (i, t) ->
              (translate_var i, translate_typ t));
        UCS.cfields = fields';
        ccomps = comps';
      }
    in
    let cmod' =
      {
        UCS.smver = cmod.smver;
        UCS.elibs =
          List.map cmod.elibs ~f:(fun (i, iopt) ->
              (translate_var i, Option.map ~f:translate_var iopt));
        UCS.libs = clibs';
        UCS.contr = contr';
      }
    in

    (* Return back the whole program, transformed. *)
    pure (cmod', rlibs', elibs')

  let translate_adts () =
    let all_adts = Datatypes.DataTypeDictionary.get_all_adts () in
    forallM all_adts ~f:(fun (a : Datatypes.adt) ->
        let a' : UCS.Datatypes.adt =
          {
            tname = a.tname;
            tparams = List.map a.tparams ~f:UCS.mk_noannot_id;
            tconstr = a.tconstr;
            tmap =
              List.map a.tmap ~f:(fun (s, tl) ->
                  (s, List.map tl ~f:translate_typ));
          }
        in
        UCS.Datatypes.DataTypeDictionary.add_adt a')

  (* ******************************************************** *)
  (********** Types used in UnCurrying analysis    ************)
  (* ******************************************************** *)

  open UCS
  (* TODO: since some code is repeated from Monomorphize.ml
     - Seperate into a seperate file
  *)

  type rev_ref = ExprRef of expr_annot ref | VarRef of eannot Identifier.t

  let elof_exprref = function
    | ExprRef eref -> pure eref
    | _ -> fail0 "Uncurry: elof_exprref: Incorrect value"

  let elof_varref = function
    | VarRef eref -> pure eref
    | _ -> fail0 "Uncurry: elof_varref: Incorrect value"

  (* Data element of the UnCurrying analysis *)
  type uca_el = {
    (* Store arity of the variable - constants have an arity of 0 *)
    arity : int option;
    (* A back reference to who this information belongs to *)
    elof : rev_ref;
        (* To be updated to store whether the variable is partially applied,
           ie. whether it would go through uncurrying
        *)
  }

  let empty_uca_el elof = { arity = None; elof }

  (* Store the analysis data *)
  let uca_data = Array.create ()

  (* ******************************************************** *)
  (**  Adding annotations to perform uncurrying analysis     **)
  (* ******************************************************** *)

  (* Since all functions in Scilla are anonymous, we tag
     all variables with a unique index to a analysis node
     in rep. This index is then mapped to an analysis node
     that will later be used to annotate a variable's arity
     and whether its a candidate for uncurrying.
  *)

  (* Add a new entry to uca_data and return its index *)
  let add_uca_el el =
    let idx = Array.length uca_data in
    let () = Array.add uca_data el in
    idx

  (* Gte the index of the next element to be inserted *)
  let next_index () = Array.length uca_data

  let get_uca_el idx = uca_data.(idx)

  let set_uca_el idx el = uca_data.(idx) <- el

  (* The initialisation environment tracks the variable indices
     list that matches the index to its analysis node. This way,
     we don't have to rewrite the AST with unique names.
  *)
  type init_env = { var_indices : (string * int) list }

  let empty_init_env = { var_indices = [] }

  let resolve_var ienv v =
    match List.Assoc.find ~equal:String.equal ienv.var_indices v with
    | Some i -> pure i
    | None ->
        fail0 ("Uncurrying: initialise_uca: Unable to resolve variable " ^ v)

  (* Attach existing uca_data index to a variable @v already bound in @ienv *)
  let initialise_uca_var ienv v =
    let vrep = Identifier.get_rep v in
    let%bind idx = resolve_var ienv (Identifier.as_error_string v) in
    pure
    @@ Identifier.mk_id (Identifier.get_id v) { vrep with ea_auxi = Some idx }

  (* Attach new uca_data index to a variable @v and append it to @ienv *)
  let initialise_uca_bind ienv v =
    let idx = add_uca_el (empty_uca_el (VarRef v)) in
    let ienv' =
      { var_indices = (Identifier.as_error_string v, idx) :: ienv.var_indices }
    in
    let%bind v' = initialise_uca_var ienv' v in
    (* For consistency, upadte v with v' uca_data *)
    let () = set_uca_el idx { (get_uca_el idx) with elof = VarRef v' } in
    pure (ienv', v')

  (* Sets up a tfa_index for each bound variable and returns a new env. *)
  (* TODO: check if its necessary - can match be pattern matched to a function? *)
  let initialise_uca_match_bind sp =
    let initialise_uca_match_bind_base ienv = function
      | Wildcard -> pure (ienv, Wildcard)
      | Binder b ->
          let%bind ienv', b' = initialise_uca_bind ienv b in
          pure (ienv', Binder b')
    in
    match sp with
    | Any base ->
        let%bind new_binds, base' =
          initialise_uca_match_bind_base empty_init_env base
        in
        pure (new_binds, Any base')
    | Constructor (cname, basel) ->
        let%bind new_binds, basel' =
          fold_mapM ~init:empty_init_env
            ~f:(fun accenv base -> initialise_uca_match_bind_base accenv base)
            basel
        in
        pure (new_binds, Constructor (cname, basel'))

  let rec initialise_uca_expr (ienv : init_env) (e, annot) =
    let%bind e' =
      match e with
      | Literal _ | JumpExpr _ -> pure e
      | Var v ->
          let%bind v' = initialise_uca_var ienv v in
          pure (Var v')
      | Message comps ->
          (* TODO: Do we need to tag free variables here? *)
          let%bind pl' =
            mapM
              ~f:(function
                | s, MLit l -> pure (s, MLit l)
                | s, MVar v ->
                    let%bind v' = initialise_uca_var ienv v in
                    pure (s, MVar v'))
              comps
          in
          pure (Message pl')
      | App (f, alist) ->
          let%bind f' = initialise_uca_var ienv f in
          let%bind alist' = mapM ~f:(initialise_uca_var ienv) alist in
          pure (App (f', alist'))
      | Constr (cname, tlist, vlist) ->
          let%bind vlist' = mapM ~f:(initialise_uca_var ienv) vlist in
          pure @@ Constr (cname, tlist, vlist')
      | Builtin (b, ts, vlist) ->
          let%bind vlist' = mapM ~f:(initialise_uca_var ienv) vlist in
          pure @@ Builtin (b, ts, vlist')
      | MatchExpr (p, blist, jopt) ->
          let%bind p' = initialise_uca_var ienv p in
          let%bind blist' =
            mapM
              ~f:(fun (sp, e) ->
                let%bind new_binds, sp' = initialise_uca_match_bind sp in
                let ienv' =
                  { var_indices = new_binds.var_indices @ ienv.var_indices }
                in
                let%bind e' = initialise_uca_expr ienv' e in
                pure (sp', e'))
              blist
          in
          let%bind jopt' =
            match jopt with
            | None -> pure None
            | Some (l, je) ->
                let%bind e' = initialise_uca_expr ienv je in
                pure (Some (l, e'))
          in
          pure @@ MatchExpr (p', blist', jopt')
      | Fun (atl, sube) ->
          let%bind ienv', atl' =
            fold_mapM ~init:ienv
              ~f:(fun accenv (v, t) ->
                (* Binding of the function's argument *)
                let%bind accenv', v' = initialise_uca_bind accenv v in
                pure (accenv', (v', t)))
              atl
          in
          let%bind sube' = initialise_uca_expr ienv' sube in
          pure @@ Fun (atl', sube')
      | Fixpoint (v, t, sube) ->
          let%bind ienv', v' = initialise_uca_bind ienv v in
          let%bind sube' = initialise_uca_expr ienv' sube in
          pure (Fixpoint (v', t, sube'))
      | Let (x, xtopt, lhs, rhs) ->
          let%bind lhs' = initialise_uca_expr ienv lhs in
          let%bind ienv', x' = initialise_uca_bind ienv x in
          let%bind rhs' = initialise_uca_expr ienv' rhs in
          pure @@ Let (x', xtopt, lhs', rhs')
      | TFun (tv, sube) ->
          (* TODO: Since tv is a type argument and we don't need types - this might be useless *)
          let%bind ienv', tv' = initialise_uca_bind ienv tv in
          let%bind sube' = initialise_uca_expr ienv' sube in
          pure @@ TFun (tv', sube')
      | TApp (tf, targs) ->
          let%bind tf' = initialise_uca_var ienv tf in
          pure (TApp (tf', targs))
      | GasExpr (g, e) ->
          let%bind e' = initialise_uca_expr ienv e in
          pure (GasExpr (g, e'))
    in
    let idx = next_index () in
    let annot' = { annot with ea_auxi = Some idx } in
    let ea = (e', annot') in
    let el = empty_uca_el (ExprRef (ref ea)) in
    let _ = add_uca_el el in
    pure ea

  let rec initialise_uca_stmts (ienv : init_env) stmts =
    match stmts with
    | [] -> pure []
    | (s, annot) :: sts ->
        let%bind s', ienv' =
          match s with
          | AcceptPayment | JumpStmt _ -> pure (s, ienv)
          | Bind (x, e) ->
              let%bind e' = initialise_uca_expr ienv e in
              let%bind ienv', x' = initialise_uca_bind ienv x in
              pure @@ (Bind (x', e'), ienv')
          | Load (x, f) ->
              let%bind ienv', x' = initialise_uca_bind ienv x in
              pure (Load (x', f), ienv')
          | RemoteLoad (x, addr, f) ->
              let%bind ienv', x' = initialise_uca_bind ienv x in
              let%bind addr' = initialise_uca_var ienv' addr in
              pure (RemoteLoad (x', addr', f), ienv')
          | Store (f, x) ->
              let%bind x' = initialise_uca_var ienv x in
              pure @@ (Store (f, x'), ienv)
          | MapGet (x, m, indices, exists) ->
              let%bind ienv', x' = initialise_uca_bind ienv x in
              let%bind indices' = mapM ~f:(initialise_uca_var ienv) indices in
              pure (MapGet (x', m, indices', exists), ienv')
          | RemoteMapGet (x, addr, m, indices, exists) ->
              let%bind ienv', x' = initialise_uca_bind ienv x in
              let%bind indices' = mapM ~f:(initialise_uca_var ienv) indices in
              let%bind addr' = initialise_uca_var ienv addr in
              pure (RemoteMapGet (x', addr', m, indices', exists), ienv')
          | MapUpdate (m, indices, vopt) ->
              let%bind indices' = mapM ~f:(initialise_uca_var ienv) indices in
              let%bind vopt' =
                match vopt with
                | None -> pure None
                | Some v ->
                    let%bind v' = initialise_uca_var ienv v in
                    pure (Some v')
              in
              pure (MapUpdate (m, indices', vopt'), ienv)
          | ReadFromBC (x, bs) ->
              let%bind ienv', x' = initialise_uca_bind ienv x in
              pure (ReadFromBC (x', bs), ienv')
          | Iterate (l, p) ->
              let%bind l' = initialise_uca_var ienv l in
              pure (Iterate (l', p), ienv)
          | CallProc (p, args) ->
              let%bind args' = mapM ~f:(initialise_uca_var ienv) args in
              pure (CallProc (p, args'), ienv)
          | SendMsgs m ->
              let%bind m' = initialise_uca_var ienv m in
              pure (SendMsgs m', ienv)
          | CreateEvnt m ->
              let%bind m' = initialise_uca_var ienv m in
              pure (CreateEvnt m', ienv)
          | Throw mopt ->
              let%bind mopt' =
                match mopt with
                | None -> pure None
                | Some m ->
                    let%bind m' = initialise_uca_var ienv m in
                    pure (Some m')
              in
              pure (Throw mopt', ienv)
          | MatchStmt (p, blist, jopt) ->
              let%bind p' = initialise_uca_var ienv p in
              let%bind blist' =
                mapM
                  ~f:(fun (sp, e) ->
                    let%bind new_binds, sp' = initialise_uca_match_bind sp in
                    let ienv' =
                      { var_indices = new_binds.var_indices @ ienv.var_indices }
                    in
                    let%bind e' = initialise_uca_stmts ienv' e in
                    pure (sp', e'))
                  blist
              in
              let%bind jopt' =
                match jopt with
                | None -> pure None
                | Some (l, je) ->
                    let%bind e' = initialise_uca_stmts ienv je in
                    pure (Some (l, e'))
              in
              pure (MatchStmt (p', blist', jopt'), ienv)
          | GasStmt _ -> pure (s, ienv)
        in
        let%bind sts' = initialise_uca_stmts ienv' sts in
        pure @@ (s', annot) :: sts'

  (* Function to anaylze library entries. *)
  let initialise_uca_lib_entries env lentries =
    fold_mapM
      ~f:(fun accenv lentry ->
        match lentry with
        | LibVar (x, topt, lexp) ->
            let%bind lexp' = initialise_uca_expr accenv lexp in
            let%bind accenv', x' = initialise_uca_bind accenv x in
            pure (accenv', LibVar (x', topt, lexp'))
        | LibTyp _ -> pure (accenv, lentry))
      ~init:env lentries

  (* Function to initialize in external and contract libraries. *)
  let initialise_uca_library env lib =
    let%bind env', lentries' = initialise_uca_lib_entries env lib.lentries in
    pure (env', { lib with lentries = lentries' })

  (* Initialize in full library tree. *)
  let rec initialise_uca_libtree env lib =
    (* first analyze all the dependent libraries. *)
    let%bind env', deps' =
      fold_mapM
        ~f:(fun accenv lib -> initialise_uca_libtree accenv lib)
        ~init:env lib.deps
    in
    (* intialize in this library. *)
    let%bind env'', libn' = initialise_uca_library env' lib.libn in
    pure (env'', { libn = libn'; deps = deps' })

  (* Walk through entire module, initializing AST nodes to a TFA element. *)

  (* Walk through entire module, initializing AST nodes to a TFA element. *)
  let initialize_tfa_module (cmod : cmodule) rlibs elibs =
    (* Note that we do not annotate mutable fields and immutable contract parameters
       as function types are not storable - thus fields and parameters are of no
       interest to us.
    *)

    (* Intialize in recursion library entries. *)
    let%bind rlib_env, rlibs' =
      initialise_uca_lib_entries empty_init_env rlibs
    in

    let%bind elibs_env, elibs' =
      fold_mapM
        ~f:(fun accenv libt -> initialise_uca_libtree accenv libt)
        ~init:rlib_env elibs
    in
    let%bind libs_env, cmod_libs =
      match cmod.libs with
      | Some lib ->
          let%bind libs_env, lib' = initialise_uca_library elibs_env lib in
          pure (libs_env, { cmod with libs = Some lib' })
      | None -> pure (elibs_env, cmod)
    in

    (* Initialize in components. *)
    let%bind cmod_comps =
      let%bind ccomps' =
        mapM
          ~f:(fun comp ->
            let%bind env', comp_params' =
              let tparams' = prepend_implicit_tparams comp in
              fold_mapM ~init:libs_env
                ~f:(fun accenv (v, t) ->
                  let%bind accenv', v' = initialise_uca_bind accenv v in
                  pure (accenv', (v', t)))
                tparams'
            in
            let%bind stmts' = initialise_uca_stmts env' comp.comp_body in
            pure { comp with comp_body = stmts'; comp_params = comp_params' })
          cmod.contr.ccomps
      in
      pure { cmod_libs with contr = { cmod_libs.contr with ccomps = ccomps' } }
    in
    pure (cmod_comps, rlibs', elibs')

  (* Initialising stand alone expressions *)
  let initialise_uca_expr_wrapper rlibs elibs expr =
    (* Intialize in recursion library entries. *)
    let%bind rlib_env, rlibs' = initialise_uca_library empty_init_env rlibs in
    let%bind elibs_env, elibs' =
      fold_mapM
        ~f:(fun accenv libt -> initialise_uca_libtree accenv libt)
        ~init:rlib_env elibs
    in
    let%bind expr' = initialise_uca_expr elibs_env expr in
    pure (rlibs', elibs', expr')

  (* ******************************************************** *)
  (************ Auxiliary Functions to Analysis ***************)
  (* ******************************************************** *)

  (* Find arity of function *)
  let find_function_arity (e, annot) =
    let rec iter_funcs (e', _) acc =
      let%bind res =
        match e' with
        | Fun (_, sube) -> iter_funcs sube (acc + 1)
        | _ -> pure acc
      in
      pure res
    in
    pure @@ iter_funcs (e, annot) 0

  (* ******************************************************** *)
  (* ************** Pretty print analysis ******************* *)
  (* ******************************************************** *)

  (* Used for debugging - does not contain all data *)
  let pp_expr (e, _) =
    match e with
    | Literal l -> "Literal " ^ UCS.pp_literal l
    | Var v -> "Var " ^ Identifier.as_error_string v
    | Let (x, _, _, _) -> "Let " ^ Identifier.as_error_string x
    | Message _ -> "Message "
    | Fun (paraml, _) ->
        "Fun "
        ^ String.concat ~sep:" "
            (List.map paraml ~f:(fun x -> Identifier.as_error_string (fst x)))
    | Fixpoint (iden, _, _) -> "Fixpoint " ^ Identifier.as_error_string iden
    | App (f, args) ->
        "App "
        ^ Identifier.as_error_string f
        ^ String.concat ~sep:" " (List.map args ~f:Identifier.as_error_string)
    | Constr (iden, _, _) -> "Constr " ^ Identifier.as_error_string iden
    | MatchExpr (x, _, _) -> "MatchExpr " ^ Identifier.as_error_string x
    | JumpExpr x -> "JumpExpr " ^ Identifier.as_error_string x
    | Builtin _ -> "Builtin "
    | TFun _ -> "TFun "
    | TApp _ -> "TApp "
    | GasExpr _ -> "GasExpr "

  (* Creates strings of uca_data elements without arity information *)
  let pp_uca_data () =
    let uca_data_l = Array.to_list uca_data in
    let uca_data_str =
      List.mapi uca_data_l ~f:(fun idx uca_el ->
          let idx_s = string_of_int idx in
          let data_s =
            match uca_el.elof with
            | ExprRef expr_ref -> "Expression: " ^ pp_expr !expr_ref
            | VarRef v_annot -> Identifier.as_error_string v_annot
          in
          idx_s ^ ": " ^ data_s)
    in
    String.concat
      ~sep:
        "                                                                               "
      uca_data_str

  (* ******************************************************** *)
  (******************** Uncurrying Analysis *******************)
  (* ******************************************************** *)

  let uncurry_in_module (cmod : FPS.cmodule) rlibs elibs =
    let%bind () = translate_adts () in
    (* TODO: Perform actual uncurrying (combining curried functions and their applications)
     * on the translated AST. *)
    translate_in_module cmod rlibs elibs

  (* A wrapper to uncurry pure expressions. *)
  let uncurry_expr_wrapper rlibs elibs (e, erep) =
    let newname = LoweringUtils.global_newnamer in
    let%bind () = translate_adts () in
    (* TODO: Perform actual uncurrying (combining curried functions and their applications)
     * on the translated AST. *)
    (* Recursion libs. *)
    let%bind rlibs' = translate_in_lib newname rlibs in
    (* External libs. *)
    let%bind elibs' =
      mapM ~f:(fun elib -> translate_in_libtree newname elib) elibs
    in
    let%bind e' = translate_in_expr newname (e, erep) in
    let%bind rlibs'', elibs'', e'' =
      initialise_uca_expr_wrapper rlibs' elibs' e'
    in
    pure (rlibs'', elibs'', e'')
  (* fail0 (pp_uca_data ()) *)

  module OutputSyntax = FPS
end
