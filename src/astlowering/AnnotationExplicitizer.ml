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

open Core_kernel
open Scilla_base
open TypeUtil
open Syntax
module Literal = Literal.GlobalLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open MonadUtil
open Core.Result.Let_syntax
open ExplicitAnnotationSyntax
module GC = GasCharge.ScillaGasCharge (Identifier.Name)

(* [AnnotationExplicitizer] Translate ScillaSyntax to EASyntax. *)
module ScillaCG_AnnotationExplicitizer
    (SR : Rep) (ER : sig
      include Rep

      val get_type : rep -> PlainTypes.t inferred_type
    end) =
struct
  module TU = TypeUtilities
  module TypedSyntax = ScillaSyntax (SR) (ER) (Literal)
  module EAS = EASyntax
  open TypedSyntax

  let erep_to_eannot erep =
    let l = ER.get_loc erep in
    let t = (ER.get_type erep).tp in
    { ea_tp = Some t; ea_loc = l; ea_auxi = None }

  let srep_to_eannot srep =
    let l = SR.get_loc srep in
    { ea_tp = None; ea_loc = l; ea_auxi = None }

  let eid_to_eannot id =
    let r = Identifier.get_rep id in
    Identifier.mk_id (Identifier.get_id id) (erep_to_eannot r)

  let sid_to_eannot id =
    let r = Identifier.get_rep id in
    Identifier.mk_id (Identifier.get_id id) (srep_to_eannot r)

  let explicitize_payload = function
    | MLit l -> EAS.MLit l
    | MVar v -> EAS.MVar (eid_to_eannot v)

  let rec explicitize_pattern = function
    | Wildcard -> EAS.Wildcard
    | Binder v -> EAS.Binder (eid_to_eannot v)
    | Constructor (s, plist) ->
        EAS.Constructor (sid_to_eannot s, List.map ~f:explicitize_pattern plist)

  let rec explicitize_gascharge = function
    | SGasCharge.StaticCost i -> GC.StaticCost i
    | SizeOf v -> SizeOf v
    | ValueOf v -> ValueOf v
    | LengthOf v -> LengthOf v
    | MapSortCost m -> MapSortCost m
    | SumOf (g1, g2) ->
        SumOf (explicitize_gascharge g1, explicitize_gascharge g2)
    | ProdOf (g1, g2) ->
        ProdOf (explicitize_gascharge g1, explicitize_gascharge g2)
    | MinOf (g1, g2) ->
        MinOf (explicitize_gascharge g1, explicitize_gascharge g2)
    | DivCeil (g1, g2) ->
        DivCeil (explicitize_gascharge g1, explicitize_gascharge g2)
    | LogOf v -> LogOf v

  let rec explicitize_expr (e, erep) =
    match e with
    | Literal l -> pure (EAS.Literal l, erep_to_eannot erep)
    | Var v -> pure (EAS.Var (eid_to_eannot v), erep_to_eannot erep)
    | Message m ->
        let m' = List.map ~f:(fun (s, p) -> (s, explicitize_payload p)) m in
        pure (EAS.Message m', erep_to_eannot erep)
    | App (a, l) ->
        let l' = List.map ~f:eid_to_eannot l in
        pure (EAS.App (eid_to_eannot a, l'), erep_to_eannot erep)
    | Constr (s, tl, il) ->
        pure
          ( EAS.Constr (sid_to_eannot s, tl, List.map ~f:eid_to_eannot il),
            erep_to_eannot erep )
    | Builtin ((b, r), ts, il) ->
        let b' = (b, erep_to_eannot r) in
        pure
          ( EAS.Builtin (b', ts, List.map ~f:eid_to_eannot il),
            erep_to_eannot erep )
    | Fixpoint (i, t, body) ->
        let%bind body' = explicitize_expr body in
        pure (EAS.Fixpoint (eid_to_eannot i, t, body'), erep_to_eannot erep)
    | Fun (i, t, body) ->
        let%bind body' = explicitize_expr body in
        pure (EAS.Fun (eid_to_eannot i, t, body'), erep_to_eannot erep)
    | Let (i, topt, lhs, rhs) ->
        let%bind lhs' = explicitize_expr lhs in
        let%bind rhs' = explicitize_expr rhs in
        pure (EAS.Let (eid_to_eannot i, topt, lhs', rhs'), erep_to_eannot erep)
    | MatchExpr (i, clauses) ->
        let%bind clauses' =
          mapM
            ~f:(fun (p, cexp) ->
              let%bind cexp' = explicitize_expr cexp in
              pure (explicitize_pattern p, cexp'))
            clauses
        in
        pure (EAS.MatchExpr (eid_to_eannot i, clauses'), erep_to_eannot erep)
    | TFun (v, body) ->
        let%bind body' = explicitize_expr body in
        pure (EAS.TFun (eid_to_eannot v, body'), erep_to_eannot erep)
    | TApp (i, tl) -> pure (EAS.TApp (eid_to_eannot i, tl), erep_to_eannot erep)
    | GasExpr (g, e) ->
        let%bind e' = explicitize_expr e in
        pure (EAS.GasExpr (explicitize_gascharge g, e'), erep_to_eannot erep)

  let rec explicitize_stmts stmts =
    match stmts with
    | [] -> pure []
    | (s, srep) :: sts -> (
        let%bind sts' = explicitize_stmts sts in
        match s with
        | Load (x, m) ->
            let s' = EAS.Load (eid_to_eannot x, eid_to_eannot m) in
            pure ((s', srep_to_eannot srep) :: sts')
        | RemoteLoad (addr, x, m) ->
            let s' =
              EAS.RemoteLoad
                (eid_to_eannot addr, eid_to_eannot x, eid_to_eannot m)
            in
            pure ((s', srep_to_eannot srep) :: sts')
        | Store (m, i) ->
            let s' = EAS.Store (eid_to_eannot m, eid_to_eannot i) in
            pure ((s', srep_to_eannot srep) :: sts')
        | MapUpdate (i, il, io) ->
            let s' =
              EAS.MapUpdate
                ( eid_to_eannot i,
                  List.map ~f:eid_to_eannot il,
                  Option.map ~f:eid_to_eannot io )
            in
            pure ((s', srep_to_eannot srep) :: sts')
        | MapGet (i, i', il, b) ->
            let s' =
              EAS.MapGet
                ( eid_to_eannot i,
                  eid_to_eannot i',
                  List.map ~f:eid_to_eannot il,
                  b )
            in
            pure ((s', srep_to_eannot srep) :: sts')
        | RemoteMapGet (addr, i, i', il, b) ->
            let s' =
              EAS.RemoteMapGet
                ( eid_to_eannot addr,
                  eid_to_eannot i,
                  eid_to_eannot i',
                  List.map ~f:eid_to_eannot il,
                  b )
            in
            pure ((s', srep_to_eannot srep) :: sts')
        | ReadFromBC (i, s) ->
            let s' = EAS.ReadFromBC (eid_to_eannot i, s) in
            pure ((s', srep_to_eannot srep) :: sts')
        | AcceptPayment ->
            let s' = EAS.AcceptPayment in
            pure ((s', srep_to_eannot srep) :: sts')
        | SendMsgs m ->
            let s' = EAS.SendMsgs (eid_to_eannot m) in
            pure ((s', srep_to_eannot srep) :: sts')
        | CreateEvnt e ->
            let s' = EAS.CreateEvnt (eid_to_eannot e) in
            pure ((s', srep_to_eannot srep) :: sts')
        | Throw topt ->
            let s' =
              match topt with
              | Some t -> EAS.Throw (Some (eid_to_eannot t))
              | None -> EAS.Throw None
            in
            pure ((s', srep_to_eannot srep) :: sts')
        | CallProc (p, al) ->
            let s' =
              EAS.CallProc (sid_to_eannot p, List.map ~f:eid_to_eannot al)
            in
            pure ((s', srep_to_eannot srep) :: sts')
        | Iterate (l, p) ->
            let s' = EAS.Iterate (eid_to_eannot l, sid_to_eannot p) in
            pure ((s', srep_to_eannot srep) :: sts')
        | Bind (i, e) ->
            let%bind e' = explicitize_expr e in
            let s' = EAS.Bind (eid_to_eannot i, e') in
            pure ((s', srep_to_eannot srep) :: sts')
        | MatchStmt (i, pslist) ->
            let%bind pslist' =
              mapM
                ~f:(fun (p, ss) ->
                  let%bind ss' = explicitize_stmts ss in
                  pure (explicitize_pattern p, ss'))
                pslist
            in
            let s' = EAS.MatchStmt (eid_to_eannot i, pslist') in
            pure ((s', srep_to_eannot srep) :: sts')
        | GasStmt g ->
            pure
              ((EAS.GasStmt (explicitize_gascharge g), srep_to_eannot srep)
               :: sts')
        | TypeCast (x, a, t) ->
            pure
              (( EAS.TypeCast (eid_to_eannot x, eid_to_eannot a, t),
                 srep_to_eannot srep )
               :: sts'))

  (* Function to explicitize library entries. *)
  let explicitize_lib_entries lentries =
    mapM
      ~f:(fun lentry ->
        match lentry with
        | LibVar (i, topt, lexp) ->
            let%bind lexp' = explicitize_expr lexp in
            pure (EAS.LibVar (eid_to_eannot i, topt, lexp'))
        | LibTyp (i, tdefs) ->
            let tdefs' =
              List.map
                ~f:(fun (t : ctr_def) ->
                  {
                    EAS.cname = eid_to_eannot t.cname;
                    EAS.c_arg_types = t.c_arg_types;
                  })
                tdefs
            in
            pure (EAS.LibTyp (eid_to_eannot i, tdefs')))
      lentries

  (* Function to explicitize a library. *)
  let explicitize_lib lib =
    let%bind lentries' = explicitize_lib_entries lib.lentries in
    let lib' = { EAS.lname = sid_to_eannot lib.lname; lentries = lentries' } in
    pure lib'

  (* Translate the library tree. *)
  let rec explicitize_libtree libt =
    let%bind deps' = mapM ~f:(fun dep -> explicitize_libtree dep) libt.deps in
    let%bind libn' = explicitize_lib libt.libn in
    let libt' = { EAS.libn = libn'; EAS.deps = deps' } in
    pure libt'

  let explicitize_module (cmod : cmodule) rlibs elibs =
    (* Translate recursion libs. *)
    let%bind rlibs' = explicitize_lib_entries rlibs in
    (* Translate external libs. *)
    let%bind elibs' = mapM ~f:(fun elib -> explicitize_libtree elib) elibs in

    (* Translate contract library. *)
    let%bind clibs' =
      match cmod.libs with
      | Some clib ->
          let%bind clib' = explicitize_lib clib in
          pure @@ Some clib'
      | None -> pure None
    in

    (* Translate fields and their initializations. *)
    let%bind fields' =
      mapM
        ~f:(fun (i, t, fexp) ->
          let%bind fexp' = explicitize_expr fexp in
          pure (eid_to_eannot i, t, fexp'))
        cmod.contr.cfields
    in

    (* Translate all contract components. *)
    let%bind comps' =
      mapM
        ~f:(fun comp ->
          let%bind body' = explicitize_stmts comp.comp_body in
          let comp_params' =
            List.map ~f:(fun (i, t) -> (eid_to_eannot i, t)) comp.comp_params
          in
          pure
            {
              EAS.comp_type = comp.comp_type;
              EAS.comp_name = sid_to_eannot comp.comp_name;
              EAS.comp_params = comp_params';
              EAS.comp_body = body';
            })
        cmod.contr.ccomps
    in

    let contr' =
      let params' =
        List.map ~f:(fun (i, t) -> (eid_to_eannot i, t)) cmod.contr.cparams
      in
      {
        EAS.cname = sid_to_eannot cmod.contr.cname;
        EAS.cparams = params';
        EAS.cfields = fields';
        ccomps = comps';
      }
    in
    let cmod' =
      let eliblist =
        List.map
          ~f:(fun (a, b) -> (sid_to_eannot a, Option.map ~f:sid_to_eannot b))
          cmod.elibs
      in
      {
        EAS.smver = cmod.smver;
        EAS.elibs = eliblist;
        EAS.libs = clibs';
        EAS.contr = contr';
      }
    in

    (* Return back the whole program, transformed. *)
    pure (cmod', rlibs', elibs')

  (* For standalone expressions. *)
  let explicitize_expr_wrapper rlibs elibs expr =
    let%bind rlibs' = explicitize_lib rlibs in
    let%bind elibs' = mapM elibs ~f:explicitize_libtree in
    let%bind expr' = explicitize_expr expr in
    pure (rlibs', elibs', expr')

  module OutputSyntax = EAS
end
