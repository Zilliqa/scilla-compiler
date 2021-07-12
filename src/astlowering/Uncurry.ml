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
(* module Array = BatDynArray *)
open Result.Let_syntax
open Scilla_base
module Literal = Literal.GlobalLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open MonadUtil
open FlatPatternSyntax
open UncurriedSyntax
open ErrorUtils
open ExplicitAnnotationSyntax

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
  (******************** Uncurrying Analysis *******************)
  (* ******************************************************** *)

  (* The following analysis finds function candidates for Uncurrying.
     Candidates must fulfill the following criteria to be uncurried:
     * Have an arity of >= 2 
     * Are never partiall applied
     * Are used primarily as first order functions - not as arguments
     of other functions, and do not "escape" into ADTs 
  *)

  (* Collect a list of functions *)
  let to_uncurry = ref []

  (* Find is expressions is a Fun expr*)
  let rec is_fun (e, _) =
    match e with GasExpr (_, e) -> is_fun e | Fun _ -> true | _ -> false

  let dedup_id_pair_list pl =
    List.dedup_and_sort
      ~compare:(fun a a' -> Identifier.compare (fst a) (fst a'))
      pl

  (* Finding the arity of a function
     If a `Fun` expression's immediate subexpression is not `Fun`,
     arity of the expression is 1. Otherwise, if the subexpression
     if `Fun`, then the arity is one more then the immediate `Fun`
     expression.
  *)
  let find_function_arity (e, annot) =
    let rec iter_funcs (e', _) acc =
      let res =
        match e' with
        | Fun (_, _, sube) -> iter_funcs sube (acc + 1)
        (* if Fun is wrapped with GasExpr *)
        | GasExpr (_, e) -> iter_funcs e acc
        | _ -> acc
      in
      res
    in
    iter_funcs (e, annot) 0

  (* Debugging tools TOREMOVE START *)
  let int_list_to_string int_l =
    String.concat ~sep:", " (List.map int_l ~f:(fun i -> string_of_int i))

  let func_int_list_to_string pl =
    String.concat ~sep:", "
      (List.map pl ~f:(fun (iden, i) ->
           sprintf "( %s, %s )" (Identifier.as_string iden) (string_of_int i)))

  let debug_msg = ref []

  (* TOREMOVE ENDS *)

  (* Iterate through expression to find live Fun
     Returns (expr * (Identifier * int)) - expression + the function name + number of arguments its been applied to
     Variables x that are used as arguements are also included as a pair (x,0) -> this is
     used to decipher functions that are also used as arguments in ADTs, App, or Builtin
  *)
  (* TODO: handle new e that are returned 
            pretty much all are wrong rn
    *)
  let rec expr_uca (expr, annot) =
    match expr with
    | Literal _ | Var _ | Message _ | JumpExpr _ | TApp _ -> (expr, annot), []
    | GasExpr (g, e) -> 
      let e', fl = expr_uca e in 
      (GasExpr (g, e'), annot), fl
    | Fixpoint (a, t, e) -> 
      let e', fl = expr_uca e in 
      (Fixpoint (a, t, e'), annot), fl
    | Fun (a, t, e) -> 
      let e', fl = expr_uca e in 
      (Fun (a, t, e'), annot), fl
    | TFun (a, e) -> 
      let e', fl = expr_uca e in 
      (TFun (a, e'), annot), fl 
    | App (f, alist) ->
        let args_pair_0 = List.map alist ~f:(fun arg -> (arg, 0)) in
        ((expr, annot), (f, List.length alist) :: args_pair_0)
    | Constr (_, _, alist) | Builtin (_, _, alist) ->
        let args_pair_0 = List.map alist ~f:(fun arg -> (arg, 0)) in
        ((expr, annot), args_pair_0)
    | Let (x, ty, lhs, rhs) ->
        (* debug_msg := ("Entered a Let expr for: " ^ Identifier.as_error_string x) :: !debug_msg; *)
        let ea_rhs, fv_rhs = expr_uca rhs in
        let ea_lhs, fv_lhs = expr_uca lhs in
        (* Remove the function from fv_rhs *)
        let fv_rhs_no_x =
          List.filter ~f:(fun (i, _) -> not @@ Identifier.equal i x) fv_rhs
        in
        (* if x is a function *)
        if is_fun ea_lhs then 
          let arity_of_f = find_function_arity ea_lhs in
          (* Take out the number of arguments the function has been applied to *)
          let use_x =
            List.filter_map fv_rhs ~f:(fun (name, arg_num) ->
                if Identifier.equal name x then Some arg_num else None)
          in
          (* if a pair (f,0) exists, f already won't be considered for uncurrying *)
           let is_to_uncur =
             List.for_all use_x ~f:(fun arg_num -> arg_num = arity_of_f)
             && (not @@ List.is_empty use_x)
             && arity_of_f >= 2
          in

          (* if x fulfills criteria for uncurrying *)
          if is_to_uncur then (

            (* for debugging - TODO: remove *)
            to_uncurry := Identifier.as_error_string x :: !to_uncurry;

            (* We add the arity into the eannot as ea_auxi *)
            let vrep = Identifier.get_rep x in
            let new_x = 
              Identifier.mk_id (Identifier.get_id x) {vrep with ea_auxi = Some arity_of_f}
            in
            ((Let (new_x, ty, ea_lhs, ea_lhs), annot), fv_rhs_no_x @ fv_lhs)
          )
          else 
          ((Let (x, ty, ea_lhs, ea_lhs), annot), fv_rhs_no_x @ fv_lhs)
        else ((Let (x, ty, ea_lhs, ea_lhs), annot), fv_rhs_no_x @ fv_lhs)
    | MatchExpr (p, spel, join_o) -> (
        let spel', lf = 
          List.unzip 
          @@ List.map spel ~f:( fun (pat, e) ->
            let e', lf = expr_uca e in 
            let bounds = get_spattern_bounds pat in
            (* Remove bound variable from the free functions list *)
            let lf' = 
              List.filter lf ~f:(fun (i, _) -> not @@ Identifier.is_mem_id i bounds)
            in 
            ((pat, e'), lf')
          )
        in
        let lf' = dedup_id_pair_list ((p,0) :: List.concat lf) in 
        match join_o with 
        | None -> ((MatchExpr (p, spel', None), annot), lf') 
        | Some (j_iden, e_o) -> 
          let join_o', lf_join = expr_uca e_o in
          let lf'' = dedup_id_pair_list @@ lf_join @ lf' in
          ((MatchExpr (p, spel', Some (j_iden, join_o')), annot), lf''))

  (* Finding live functions in statements
     Returns function and number of arguments it's applied to
  *)
  let rec stmts_uca stmts =
    match stmts with
    | (s, annot) :: rest_stmts -> (
        let rest', fl = stmts_uca rest_stmts in
        match s with
        | Bind (x, e) ->
            let e' ,fl' = expr_uca e in
            let s' = Bind (x, e'), annot in
            (s' :: rest', dedup_id_pair_list (fl' @ fl)) 
        | MatchStmt (p, spl, join_s_o) -> (
            let spl', fl' = 
              List.unzip 
              @@ List.map spl ~f:(fun (pat, stmts) -> 
                let stmts', fl = stmts_uca stmts in 
                let bounds = get_spattern_bounds pat in
                (* Remove bound variables from the free functions list *)
                let fl' = 
                  List.filter fl ~f:(fun (a,_) ->
                    not @@ Identifier.is_mem_id a bounds
                  ) 
                in
                ((pat, stmts'), fl')
              )
            in
            let fl'' = 
              dedup_id_pair_list @@ (p, 0) :: (fl @ List.concat fl')
            in
            match join_s_o with 
            | None -> 
              (MatchStmt (p, spl', None), annot) :: rest', fl'' 
            | Some (j_iden, s_o) ->
              let join_o', lf_join = stmts_uca s_o in
              let fl''' = dedup_id_pair_list @@ fl'' @ lf_join in
              (MatchStmt (p, spl', Some (j_iden, join_o')), annot) :: rest', fl'''
        )
        | _ -> (s, annot) :: rest', fl)
    | [] -> [], []

  (* Find live functions in libraries *)
  let rec uca_lib_entries lentries free_funcs =
    match lentries with
    | lentry :: rentries -> (
        let rentries', free_funcs' = uca_lib_entries rentries free_funcs in
        match lentry with
        | LibVar (i, topt, lexp) ->
            let lexp', fl = expr_uca lexp in
            let free_funcs_no_i =
              List.filter
                ~f:(fun i' -> not @@ Identifier.equal (fst i') i)
                free_funcs'
            in
            let default_res = (LibVar (i, topt, lexp')) :: rentries', fl @ free_funcs_no_i in
            (* This part is considered pure - functions can be written
               Handle similarly to Let expressions. lexp is the same as lhs
            *)
            if not @@ is_fun lexp' then default_res
            else
              let arity_of_i = find_function_arity lexp in
               (* Take out the number of arguments the function has been applied to *)
               let use_i =
                 List.filter_map free_funcs' ~f:(fun (name, arg_num) ->
                     if Identifier.equal name i then Some arg_num else None)
               in
               (* debug_msg := ("LibVar: Use cases of " ^ Identifier.adebugs_string i ^ ": " ^ int_list_to_string use_i) :: !debug_msg; *)
               let is_to_uncur =
                 List.for_all ~f:(fun arg_num -> arg_num = arity_of_i) use_i
                 && (not @@ List.is_empty use_i)
                 && arity_of_i >= 2
               in
               if not @@ is_to_uncur then default_res
               else
                (
                 to_uncurry := Identifier.as_error_string i :: !to_uncurry;
                let vrep = Identifier.get_rep i in
                let new_i = 
                  Identifier.mk_id (Identifier.get_id i) {vrep with ea_auxi = Some arity_of_i}
                in
                (LibVar (new_i, topt, lexp')) :: rentries', dedup_id_pair_list @@ fl @ free_funcs_no_i)
        | LibTyp _ -> lentry :: rentries' , free_funcs')
    | [] -> [], free_funcs

  let uca_lib lib free_funcs =
    let lentries', free_funcs' = uca_lib_entries lib.lentries free_funcs in
    let libs' = {lib with lentries = lentries'} in 
    libs', free_funcs'

  let rec uca_libtree libt free_funcs =
    let lib', free_funcs' = uca_lib libt.libn free_funcs in
    let lib'', free_funcs'' =
      List.unzip
      @@ List.map ~f:(fun dep -> uca_libtree dep free_funcs') libt.deps
    in
    let free_funcs''' = dedup_id_pair_list @@ free_funcs' @ List.concat free_funcs'' in
    List.concat lib'', free_funcs'''

  let uca_cmod cmod rlibs elibs =
    (* UCA contract components *)
    let ccomps', comps_fl =
      List.unzip
      @@ List.map
           ~f:(fun comp ->
             let body', fl = stmts_uca comp.comp_body in 
             {comp with comp_body = body'}, fl
             (* We do not need to filter out comp_params because
                in Scilla, function types are not storable. *))
           cmod.contr.ccomps
    in
    let comps_fl' = dedup_id_pair_list @@ List.concat comps_fl in

    (* debug_msg := ("comps_fl': " ^ func_int_list_to_string comps_fl') :: !debug_msg; *)

    (* We do not need to run the analysis on fields and contract parameters
       as function types are not storable, thus they won't be functions.
    *)

    (* UCA contract library *)
    let cmod_libs', clibs_fl =
      match cmod.libs with 
      | Some l -> 
        let libs, fl = uca_lib l comps_fl' in 
        Some libs, fl
      | None -> None, comps_fl'
    in

    (* UCA imported libs *)
    let elibs', elibs_fl =
      List.unzip @@ List.map ~f:(fun elib -> uca_libtree elib clibs_fl) elibs
    in
    let elibs_fl' = dedup_id_pair_list @@ List.concat elibs_fl in

    (* UCA recursion libs *)
    let rlibs', rlibs_fl = uca_lib_entries rlibs elibs_fl' in

    (* We're done *)
    (* TODO: rewrite ccomps *)
    let contr' = {cmod.contr with ccomps = ccomps'} in 
    let cmod' = {cmod with contr = contr'; libs = cmod_libs'} in 

    (* Return the whole program + free functions *)
    (cmod', rlibs', elibs'), rlibs_fl


  (* ******************************************************** *)
  (********** Transformation into Unuccurying Syntax **********)
  (* ******************************************************** *)

  (* The following code translates the AST from FPS to UCS *)

  (* Track functions with ea_auxi of their respective arities *)
  (* TODO: Just testing for now *)
  let rec translate_expr (e, annot) = 
    match e with 
    | Let (x, xtopt, lhs, rhs) -> ()
    | _ -> ()
  

  let uncurry_in_module (cmod : FPS.cmodule) rlibs elibs =
    let%bind () = translate_adts () in
    let _ = uca_cmod cmod rlibs elibs in
    if (not @@ List.is_empty !debug_msg) || (not @@ List.is_empty !to_uncurry)
    then
      warn0
        (String.concat ~sep:", "
           (!debug_msg @ [ "Functions to uncurry: " ] @ !to_uncurry))
        0;

    translate_in_module cmod rlibs elibs

  (* A wrapper to uncurry pure expressions. *)
  let uncurry_expr_wrapper rlibs elibs (e, erep) =
    let newname = LoweringUtils.global_newnamer in
    let%bind () = translate_adts () in
    let _ = expr_uca (e, erep) in
    if (not @@ List.is_empty !debug_msg) || (not @@ List.is_empty !to_uncurry)
    then
      warn0
        (String.concat ~sep:", "
           (!debug_msg @ [ "Functions to uncurry: " ] @ !to_uncurry))
        0;
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
