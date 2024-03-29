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

open Core
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
    | Address tlo -> (
        match tlo with
        | AnyAddr -> UCS.Address AnyAddr
        | CodeAddr -> UCS.Address CodeAddr
        | LibAddr -> UCS.Address LibAddr
        | ContrAddr fts ->
            UCS.Address
              (ContrAddr
                 (Type.IdLoc_Comp.Map.fold ~init:IdLoc_Comp.Map.empty
                    ~f:(fun ~key:id ~data:t acc ->
                      IdLoc_Comp.Map.set acc ~key:id ~data:(translate_typ t))
                    fts)))

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
        fail0 ~kind:"Uncurry: internal error: cannot translate runtime literal."
          ?inst:None

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

  let translate_bcinfo = function
    | CurBlockNum -> UCS.CurBlockNum
    | ChainID -> UCS.ChainID
    | Timestamp v -> UCS.Timestamp (translate_var v)
    | ReplicateContr (addr, iparams) ->
        UCS.ReplicateContr (translate_var addr, translate_var iparams)

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
                      ~kind:
                        "Uncurry: internal error: type mismatch during \
                         application."
                      ~inst:(Identifier.as_string a)
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
              pure @@ ((s', translate_eannot srep) :: acc)
          | RemoteLoad (x, addr, m) ->
              let s' =
                UCS.RemoteLoad
                  (translate_var x, translate_var addr, translate_var m)
              in
              pure @@ ((s', translate_eannot srep) :: acc)
          | TypeCast (x, a, t) ->
              let s' =
                UCS.TypeCast (translate_var x, translate_var a, translate_typ t)
              in
              pure @@ ((s', translate_eannot srep) :: acc)
          | Store (m, i) ->
              let s' = UCS.Store (translate_var m, translate_var i) in
              pure @@ ((s', translate_eannot srep) :: acc)
          | MapUpdate (i, il, io) ->
              let il' = List.map il ~f:translate_var in
              let io' = Option.map io ~f:translate_var in
              let s' = UCS.MapUpdate (translate_var i, il', io') in
              pure @@ ((s', translate_eannot srep) :: acc)
          | MapGet (i, i', il, b) ->
              let il' = List.map ~f:translate_var il in
              let s' = UCS.MapGet (translate_var i, translate_var i', il', b) in
              pure @@ ((s', translate_eannot srep) :: acc)
          | RemoteMapGet (i, addr, i', il, b) ->
              let il' = List.map ~f:translate_var il in
              let s' =
                UCS.RemoteMapGet
                  (translate_var i, translate_var addr, translate_var i', il', b)
              in
              pure @@ ((s', translate_eannot srep) :: acc)
          | ReadFromBC (i, s) ->
              let s' = UCS.ReadFromBC (translate_var i, translate_bcinfo s) in
              pure @@ ((s', translate_eannot srep) :: acc)
          | AcceptPayment ->
              let s' = UCS.AcceptPayment in
              pure @@ ((s', translate_eannot srep) :: acc)
          | SendMsgs m ->
              let s' = UCS.SendMsgs (translate_var m) in
              pure @@ ((s', translate_eannot srep) :: acc)
          | CreateEvnt e ->
              let s' = UCS.CreateEvnt (translate_var e) in
              pure @@ ((s', translate_eannot srep) :: acc)
          | Throw t ->
              let s' = UCS.Throw (Option.map ~f:translate_var t) in
              pure @@ ((s', translate_eannot srep) :: acc)
          | CallProc (p, al) ->
              let s' =
                UCS.CallProc (translate_var p, List.map ~f:translate_var al)
              in
              pure @@ ((s', translate_eannot srep) :: acc)
          | Iterate (l, p) ->
              let s' = UCS.Iterate (translate_var l, translate_var p) in
              pure @@ ((s', translate_eannot srep) :: acc)
          | Bind (i, e) ->
              let%bind e' = translate_in_expr newname e in
              let s' = UCS.Bind (translate_var i, e') in
              pure @@ ((s', translate_eannot srep) :: acc)
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
              @@ ((UCS.JumpStmt (translate_var j), translate_eannot srep) :: acc)
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
    let%bind cconstraint' = translate_in_expr newname cmod.contr.cconstraint in

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
        UCS.cconstraint = cconstraint';
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

  let uncurry_in_module (cmod : cmodule) rlibs elibs =
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
    pure (rlibs', elibs', e')

  module OutputSyntax = FPS
end
