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
open ExplicitAnnotationSyntax
open ErrorUtils

module ScillaCG_Uncurry = struct
  module FPS = FlatPatSyntax
  module UCS = Uncurried_Syntax
  open FPS

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

  let pp_params params =
    String.concat ~sep:", "
      (List.map params ~f:(fun (name, _) -> Identifier.as_string name))

  let pp_iden idens =
    String.concat ~sep:", "
      (List.map idens ~f:(fun name -> Identifier.as_string name))

  let debug_msg = ref []

  let debug_typ typ i =
    match typ with
    | None ->
        debug_msg :=
          ("Type of " ^ Identifier.as_string i ^ " is: None") :: !debug_msg
    | Some typ' ->
        debug_msg :=
          ("Type of " ^ Identifier.as_string i ^ " is: " ^ UCS.pp_typ typ')
          :: !debug_msg

  (* TOREMOVE ENDS *)

  (* Run analysis on whether the variable is a function to uncurry
     Function takes the list of free functions @fl, expression @e, named under @x
     Returns option new_x if we're to uncurry, otherwise None
  *)
  let uca_analysis_wrapper fl e x =
    (* if x is not a function *)
    if not @@ is_fun e then None
    else
      let arity_of_f = find_function_arity e in
      (* Take out the number of arguments the function has been applied to *)
      let use_x =
        List.filter_map fl ~f:(fun (name, arg_num) ->
            if Identifier.equal name x then Some arg_num else None)
      in
      (* if a pair (f,0) exists, f already won't be considered for uncurrying *)
      let is_to_uncur =
        List.for_all use_x ~f:(fun arg_num -> arg_num = arity_of_f)
        && (not @@ List.is_empty use_x)
        && arity_of_f >= 2
      in
      if not is_to_uncur then None
      else (
        to_uncurry := Identifier.as_error_string x :: !to_uncurry;
        let vrep = Identifier.get_rep x in
        let new_x =
          Identifier.mk_id (Identifier.get_id x)
            { vrep with ea_auxi = Some arity_of_f }
        in
        Some new_x)

  (* Iterate through expression to find live Fun
     Returns (expr * (Identifier * int)) - expression + the function name + number of arguments its been applied to
     Variables x that are used as arguements are also included as a pair (x,0) -> this is
     used to decipher functions that are also used as arguments in ADTs, App, or Builtin
  *)
  let rec expr_uca (expr, annot) =
    match expr with
    | Literal _ | Var _ | Message _ | JumpExpr _ | TApp _ -> ((expr, annot), [])
    | GasExpr (g, e) ->
        let e', fl = expr_uca e in
        ((GasExpr (g, e'), annot), fl)
    | Fixpoint (a, t, e) ->
        let e', fl = expr_uca e in
        ((Fixpoint (a, t, e'), annot), fl)
    | Fun (a, t, e) ->
        let e', fl = expr_uca e in
        ((Fun (a, t, e'), annot), fl)
    | TFun (a, e) ->
        let e', fl = expr_uca e in
        ((TFun (a, e'), annot), fl)
    | App (f, alist) ->
        let args_pair_0 = List.map alist ~f:(fun arg -> (arg, 0)) in
        ((expr, annot), (f, List.length alist) :: args_pair_0)
    | Constr (_, _, alist) | Builtin (_, _, alist) ->
        let args_pair_0 = List.map alist ~f:(fun arg -> (arg, 0)) in
        ((expr, annot), args_pair_0)
    | Let (x, ty, lhs, rhs) -> (
        let ea_rhs, fv_rhs = expr_uca rhs in
        let ea_lhs, fv_lhs = expr_uca lhs in
        (* Remove the function from fv_rhs *)
        let fv_rhs_no_x =
          List.filter ~f:(fun (i, _) -> not @@ Identifier.equal i x) fv_rhs
        in
        let default_res =
          ((Let (x, ty, ea_lhs, ea_rhs), annot), fv_rhs_no_x @ fv_lhs)
        in
        match uca_analysis_wrapper fv_rhs ea_lhs x with
        | None -> default_res
        | Some new_x ->
            ((Let (new_x, ty, ea_lhs, ea_rhs), annot), fv_rhs_no_x @ fv_lhs))
    | MatchExpr (p, spel, join_o) -> (
        let spel', lf =
          List.unzip
          @@ List.map spel ~f:(fun (pat, e) ->
                 let e', lf = expr_uca e in
                 let bounds = get_spattern_bounds pat in
                 (* Remove bound variable from the free functions list *)
                 let lf' =
                   List.filter lf ~f:(fun (i, _) ->
                       not @@ Identifier.is_mem_id i bounds)
                 in
                 ((pat, e'), lf'))
        in
        let lf' = dedup_id_pair_list ((p, 0) :: List.concat lf) in
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
        | Bind (x, e) -> (
            let e', fl' = expr_uca e in
            (* Remove the function from fl *)
            let fl_no_x =
              List.filter ~f:(fun (i, _) -> not @@ Identifier.equal i x) fl
            in
            let s' = (Bind (x, e'), annot) in
            let final_fl = dedup_id_pair_list (fl' @ fl_no_x) in
            let default_res = (s' :: rest', final_fl) in
            match uca_analysis_wrapper fl e x with
            | None -> default_res
            | Some new_x ->
                let s' = (Bind (new_x, e'), annot) in
                (s' :: rest', final_fl))
        | MatchStmt (p, spl, join_s_o) -> (
            let spl', fl' =
              List.unzip
              @@ List.map spl ~f:(fun (pat, stmts) ->
                     let stmts', fl = stmts_uca stmts in
                     let bounds = get_spattern_bounds pat in
                     (* Remove bound variables from the free functions list *)
                     let fl' =
                       List.filter fl ~f:(fun (a, _) ->
                           not @@ Identifier.is_mem_id a bounds)
                     in
                     ((pat, stmts'), fl'))
            in
            let fl'' = dedup_id_pair_list @@ (p, 0) :: (fl @ List.concat fl') in
            match join_s_o with
            | None -> ((MatchStmt (p, spl', None), annot) :: rest', fl'')
            | Some (j_iden, s_o) ->
                let join_o', lf_join = stmts_uca s_o in
                let fl''' = dedup_id_pair_list @@ fl'' @ lf_join in
                ( (MatchStmt (p, spl', Some (j_iden, join_o')), annot) :: rest',
                  fl''' ))
        | _ -> ((s, annot) :: rest', fl))
    | [] -> ([], [])

  (* Find live functions in libraries *)
  let rec uca_lib_entries lentries free_funcs =
    match lentries with
    | lentry :: rentries -> (
        let rentries', free_funcs' = uca_lib_entries rentries free_funcs in
        match lentry with
        | LibVar (i, topt, lexp) -> (
            let lexp', fl = expr_uca lexp in
            let free_funcs_no_i =
              List.filter
                ~f:(fun i' -> not @@ Identifier.equal (fst i') i)
                free_funcs'
            in
            let default_res =
              (LibVar (i, topt, lexp') :: rentries', fl @ free_funcs_no_i)
            in
            (* This part is considered pure - functions can be written
               Handle similarly to Let expressions. lexp is the same as lhs
            *)
            match uca_analysis_wrapper free_funcs' lexp i with
            | None -> default_res
            | Some new_i ->
                ( LibVar (new_i, topt, lexp') :: rentries',
                  dedup_id_pair_list @@ fl @ free_funcs_no_i ))
        | LibTyp _ -> (lentry :: rentries', free_funcs'))
    | [] -> ([], free_funcs)

  let uca_lib lib free_funcs =
    let lentries', free_funcs' = uca_lib_entries lib.lentries free_funcs in
    let libs' = { lib with lentries = lentries' } in
    (libs', free_funcs')

  let rec uca_libtree libt free_funcs =
    let libn', free_funcs' = uca_lib libt.libn free_funcs in
    let deps', free_funcs'' =
      List.unzip
      @@ List.map ~f:(fun dep -> uca_libtree dep free_funcs') libt.deps
    in
    let libt' = { libn = libn'; deps = deps' } in
    let free_funcs''' =
      dedup_id_pair_list @@ free_funcs' @ List.concat free_funcs''
    in
    (libt', free_funcs''')

  let uca_cmod cmod rlibs elibs =
    (* UCA contract components *)
    let ccomps', comps_fl =
      List.unzip
      @@ List.map
           ~f:(fun comp ->
             let body', fl = stmts_uca comp.comp_body in
             ({ comp with comp_body = body' }, fl)
             (* We do not need to filter out comp_params because
                in Scilla, function types are not storable. *))
           cmod.contr.ccomps
    in
    let comps_fl' = dedup_id_pair_list @@ List.concat comps_fl in

    (* We do not need to run the analysis on fields and contract parameters
       as function types are not storable, thus they won't be functions.
    *)

    (* UCA contract library *)
    let cmod_libs', clibs_fl =
      match cmod.libs with
      | Some l ->
          let libs, fl = uca_lib l comps_fl' in
          (Some libs, fl)
      | None -> (None, comps_fl')
    in

    (* UCA imported libs *)
    let elibs', elibs_fl =
      List.unzip @@ List.map ~f:(fun elib -> uca_libtree elib clibs_fl) elibs
    in
    let elibs_fl' = dedup_id_pair_list @@ List.concat elibs_fl in

    (* UCA recursion libs *)
    let rlibs', rlibs_fl = uca_lib_entries rlibs elibs_fl' in

    (* We're done *)
    let contr' = { cmod.contr with ccomps = ccomps' } in
    let cmod' = { cmod with contr = contr'; libs = cmod_libs' } in

    (* Return the whole program + free functions *)
    ((cmod', rlibs', elibs'), rlibs_fl)

  (* ******************************************************** *)
  (********** Transformation into Unuccurying Syntax **********)
  (* ******************************************************** *)

  (* Return body of function and consecutive parameters *)
  let rec strip_params (e, erep) params debug_s =
    match e with
    | Fun (i, t, body) ->
        strip_params body ((i, t) :: params) (debug_s @ [ "Fun " ])
    | GasExpr (g, sube) ->
        (* TODO: ask vaivas about gas charge *)
        let body', params' =
          strip_params sube params (debug_s @ [ "GasExpr " ])
        in
        ((GasExpr (g, body'), erep), List.rev params')
    | _ ->
        debug_msg :=
          ("strip_params: " ^ String.concat ~sep:", " debug_s) :: !debug_msg;
        ((e, erep), List.rev params)

  (* Function to uncurry the types of Func Expressions *)
  let uncurry_func_typ typ arity =
    let rec uncurry_iter argt rett arity_left =
      if arity_left <= 1 then (argt, rett)
      else
        match rett with
        | UCS.FunType (argt', rett') ->
            uncurry_iter (argt @ argt') rett' (arity_left - 1)
        | _ -> (argt, rett)
    in
    match typ with
    | UCS.FunType (argt, rett) ->
        let argt', rett' = uncurry_iter argt rett arity in
        UCS.FunType (argt', rett')
    | _ -> typ

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

  (* Environment @ienv contains functions within scope that HAVE been uncurried
     and their uncurried types *)
  (* Function to uncurry Func expressions *)
  let rec uncurry_func_epxr newname ienv fe =
    let body, params = strip_params fe [] [] in
    let%bind body' = translate_expr newname body ienv in
    let%bind params' =
      mapM params ~f:(fun (name, ty) ->
          pure (translate_var name, translate_typ ty))
    in
    let new_rep = translate_eannot (snd fe) in
    let new_rep' =
      {
        new_rep with
        ea_tp =
          Option.map new_rep.ea_tp ~f:(fun tp ->
              uncurry_func_typ tp (List.length params'));
      }
    in
    pure (UCS.Fun (params', body'), new_rep')

  (* Note:
     * Functions are added to the env when they are uncurried
     * Functions are only removed from the environment when the variable name is redefined to
     something else
     * translate_expr does not return an environment because the scope of
     newly defined functions in expr ends there
  *)
  (* If functions that are NOT uncurried, their App will be transformed *)
  (* Note: ienv contains variables in UCS syntax *)
  and translate_expr newname (e, annot) ienv =
    let rec go_expr (e, erep) ienv =
      match e with
      | Let (i, topt, lhs, rhs) ->
          (* If the function is to be uncurried *)
          if Option.is_some (Identifier.get_rep i).ea_auxi then
            let%bind uncurried_lhs = uncurry_func_epxr newname ienv lhs in
            let uncurried_ty = (snd uncurried_lhs).ea_tp in
            let translated_i =
              let rep = translate_eannot (Identifier.get_rep i) in
              let rep' = { rep with ea_tp = uncurried_ty } in
              Identifier.mk_id (Identifier.get_id i) rep'
            in
            (* Add i into ienv to run rhs *)
            let%bind rhs' =
              go_expr rhs ((translated_i, uncurried_ty) :: ienv)
            in
            pure
              ( UCS.Let
                  ( translated_i,
                    Option.map ~f:translate_typ topt,
                    uncurried_lhs,
                    rhs' ),
                translate_eannot erep )
          else
            let translated_i = translate_var i in
            (* We don't uncurry it - and we make sure it's not in the ienv *)
            let ienv' =
              List.filter ienv ~f:(fun (iden, _) ->
                  not @@ Identifier.equal translated_i iden)
            in
            let%bind lhs' = go_expr lhs ienv in
            let%bind rhs' = go_expr rhs ienv' in
            pure
              ( UCS.Let
                  (translated_i, Option.map ~f:translate_typ topt, lhs', rhs'),
                translate_eannot erep )
      | App (a, l) ->
          let a' = translate_var a in
          (* If the function was uncurried *)
          if Identifier.is_mem_id a' (fst @@ List.unzip ienv) then
            (* debug_msg := ("App to: " ^ Identifier.as_string a ^ " kept the same") :: !debug_msg; *)
            let new_typ_a =
              snd
              @@ List.find_exn ienv ~f:(fun (iden, _) ->
                     Identifier.equal iden a')
            in
            let new_a =
              Identifier.mk_id (Identifier.get_id a)
                { (Identifier.get_rep a') with ea_tp = new_typ_a }
            in

            (* debug_typ (Identifier.get_rep new_a).ea_tp new_a;
               debug_typ (translate_eannot erep).ea_tp new_a; *)
            pure
              ( UCS.App (new_a, List.map l ~f:translate_var),
                translate_eannot erep )
          else
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
          let%bind body' = go_expr body ienv in
          pure
            ( UCS.Fixpoint (translate_var f, translate_typ t, body'),
              translate_eannot erep )
      | Fun (i, t, body) ->
          let%bind body' = go_expr body ienv in
          pure
            ( UCS.Fun ([ (translate_var i, translate_typ t) ], body'),
              translate_eannot erep )
      | TFun (t, e) ->
          let%bind e' = go_expr e ienv in
          pure (UCS.TFun (translate_var t, e'), translate_eannot erep)
      | TApp (i, tl) ->
          let tl' = List.map tl ~f:translate_typ in
          pure (UCS.TApp (translate_var i, tl'), translate_eannot erep)
      | MatchExpr (obj, clauses, joinopt) ->
          let%bind clauses' =
            mapM clauses ~f:(fun (p, rhs) ->
                let p' = translate_spattern p in
                (* Remove any bounds from free functions *)
                let bounds = UCS.get_spattern_bounds p' in
                let ienv' =
                  List.filter ienv ~f:(fun (f, _) ->
                      not @@ Identifier.is_mem_id f bounds)
                in
                let%bind rhs' = go_expr rhs ienv' in
                pure (p', rhs'))
          in
          let%bind joinopt' =
            option_mapM joinopt ~f:(fun (l, je) ->
                let l' = translate_var l in
                (* We don't need to exclude bound names because it's a jump identiier *)
                let%bind je' = go_expr je ienv in
                pure (l', je'))
          in
          pure
            ( UCS.MatchExpr (translate_var obj, clauses', joinopt'),
              translate_eannot erep )
      | JumpExpr l ->
          pure (UCS.JumpExpr (translate_var l), translate_eannot erep)
      | GasExpr (g, e) ->
          let%bind e' = go_expr e ienv in
          pure @@ (UCS.GasExpr (g, e'), translate_eannot erep)
    in
    go_expr (e, annot) ienv

  (* Note:
     * All the same from the previous translate - difference in handling only lies in Bind()
     * Returns an updated list of statements
  *)
  let translate_stmts newname stmts ienv =
    let rec go_stmts stmts ienv =
      let%bind stmts_rev, ienv' =
        (* Keep track of ienv as well because Bind might overwrite a function name *)
        foldM stmts ~init:([], ienv)
          ~f:(fun (acc_stmts, acc_ienv) (stmt, srep) ->
            match stmt with
            | Bind (i, e) ->
                (* If the function is to be uncurried *)
                if Option.is_some (Identifier.get_rep i).ea_auxi then
                  let%bind uncurried_e = uncurry_func_epxr newname acc_ienv e in
                  let uncurried_ty = (snd uncurried_e).ea_tp in
                  let translated_i =
                    let rep = translate_eannot (Identifier.get_rep i) in
                    let rep' = { rep with ea_tp = uncurried_ty } in
                    Identifier.mk_id (Identifier.get_id i) rep'
                  in
                  (* debug_typ (snd uncurried_e).ea_tp i; *)
                  let s' = UCS.Bind (translated_i, uncurried_e) in
                  pure
                  @@ ( (s', translate_eannot srep) :: acc_stmts,
                       (translated_i, uncurried_ty) :: acc_ienv )
                else
                  (* We don't uncurry - and we make sure it's not in the ienv *)
                  let translated_i = translate_var i in
                  let acc_ienv' =
                    List.filter acc_ienv ~f:(fun (iden, _) ->
                        not @@ Identifier.equal translated_i iden)
                  in
                  let%bind e' = translate_expr newname e acc_ienv' in
                  let s' = UCS.Bind (translate_var i, e') in
                  pure @@ ((s', translate_eannot srep) :: acc_stmts, acc_ienv')
            | Load (x, m) ->
                let s' = UCS.Load (translate_var x, translate_var m) in
                pure @@ ((s', translate_eannot srep) :: acc_stmts, acc_ienv)
            | RemoteLoad (x, addr, m) ->
                let s' =
                  UCS.RemoteLoad
                    (translate_var x, translate_var addr, translate_var m)
                in
                pure @@ ((s', translate_eannot srep) :: acc_stmts, acc_ienv)
            | Store (m, i) ->
                let s' = UCS.Store (translate_var m, translate_var i) in
                pure @@ ((s', translate_eannot srep) :: acc_stmts, acc_ienv)
            | MapUpdate (i, il, io) ->
                let il' = List.map il ~f:translate_var in
                let io' = Option.map io ~f:translate_var in
                let s' = UCS.MapUpdate (translate_var i, il', io') in
                pure @@ ((s', translate_eannot srep) :: acc_stmts, acc_ienv)
            | MapGet (i, i', il, b) ->
                let il' = List.map ~f:translate_var il in
                let s' =
                  UCS.MapGet (translate_var i, translate_var i', il', b)
                in
                pure @@ ((s', translate_eannot srep) :: acc_stmts, acc_ienv)
            | RemoteMapGet (i, addr, i', il, b) ->
                let il' = List.map ~f:translate_var il in
                let s' =
                  UCS.RemoteMapGet
                    ( translate_var i,
                      translate_var addr,
                      translate_var i',
                      il',
                      b )
                in
                pure @@ ((s', translate_eannot srep) :: acc_stmts, acc_ienv)
            | ReadFromBC (i, s) ->
                let s' = UCS.ReadFromBC (translate_var i, s) in
                pure @@ ((s', translate_eannot srep) :: acc_stmts, acc_ienv)
            | AcceptPayment ->
                let s' = UCS.AcceptPayment in
                pure @@ ((s', translate_eannot srep) :: acc_stmts, acc_ienv)
            | SendMsgs m ->
                let s' = UCS.SendMsgs (translate_var m) in
                pure @@ ((s', translate_eannot srep) :: acc_stmts, acc_ienv)
            | CreateEvnt e ->
                let s' = UCS.CreateEvnt (translate_var e) in
                pure @@ ((s', translate_eannot srep) :: acc_stmts, acc_ienv)
            | Throw t ->
                let s' = UCS.Throw (Option.map ~f:translate_var t) in
                pure @@ ((s', translate_eannot srep) :: acc_stmts, acc_ienv)
            | CallProc (p, al) ->
                let s' =
                  UCS.CallProc (translate_var p, List.map ~f:translate_var al)
                in
                pure @@ ((s', translate_eannot srep) :: acc_stmts, acc_ienv)
            | Iterate (l, p) ->
                let s' = UCS.Iterate (translate_var l, translate_var p) in
                pure @@ ((s', translate_eannot srep) :: acc_stmts, acc_ienv)
            | MatchStmt (obj, clauses, joinopt) ->
                let%bind clauses' =
                  mapM clauses ~f:(fun (p, rhs) ->
                      let p' = translate_spattern p in
                      (* Don't use env cause function defined in pattern stmt is local in that scope *)
                      let%bind rhs', _ = go_stmts rhs acc_ienv in
                      pure (p', rhs'))
                in
                let%bind joinopt' =
                  option_mapM joinopt ~f:(fun (l, je) ->
                      let l' = translate_var l in
                      (* Don't use env cause function defined in pattern stmt is local in that scope *)
                      let%bind je', _ = go_stmts je acc_ienv in
                      pure (l', je'))
                in
                pure
                  ( ( UCS.MatchStmt (translate_var obj, clauses', joinopt'),
                      translate_eannot srep )
                    :: acc_stmts,
                    acc_ienv )
            | JumpStmt j ->
                pure
                  ( (UCS.JumpStmt (translate_var j), translate_eannot srep)
                    :: acc_stmts,
                    acc_ienv )
            | GasStmt g ->
                pure
                  ((UCS.GasStmt g, translate_eannot srep) :: acc_stmts, acc_ienv)
            | TypeCast (x, a, t) ->
                let x' = translate_var x in
                let a' = translate_var a in
                let t' = translate_typ t in
                pure
                  ( (UCS.TypeCast (x', a', t'), translate_eannot srep)
                    :: acc_stmts,
                    acc_ienv ))
      in
      pure (List.rev stmts_rev, ienv')
    in
    let%bind stmts', _ = go_stmts stmts ienv in
    pure stmts'

  let translate_lib_entries newname lentries ienv =
    let%bind lentries_rev, ienv' =
      foldM lentries ~init:([], ienv) ~f:(fun (acc_lentries, acc_ienv) lentry ->
          match lentry with
          | LibVar (i, topt, lexp) ->
              (* If the function is to be uncurried *)
              if Option.is_some (Identifier.get_rep i).ea_auxi then
                (* debug_msg := ("LibVar: " ^ Identifier.as_string i ^ " is uncurried") :: !debug_msg; *)
                let%bind uncurried_lexp =
                  uncurry_func_epxr newname acc_ienv lexp
                in
                let uncurried_ty = (snd uncurried_lexp).ea_tp in
                let translated_i =
                  let rep = translate_eannot (Identifier.get_rep i) in
                  let rep' = { rep with ea_tp = uncurried_ty } in
                  Identifier.mk_id (Identifier.get_id i) rep'
                in
                (* debug_typ (snd uncurried_lexp).ea_tp i; *)
                let lentry' =
                  UCS.LibVar
                    ( translated_i,
                      Option.map ~f:translate_typ topt,
                      uncurried_lexp )
                in
                pure
                @@ ( lentry' :: acc_lentries,
                     (translated_i, uncurried_ty) :: acc_ienv )
              else
                (* We don't uncurry - and we make sure it's not in the ienv *)
                let translated_i = translate_var i in
                let acc_ienv' =
                  List.filter acc_ienv ~f:(fun (iden, _) ->
                      not @@ Identifier.equal translated_i iden)
                in
                let%bind lexp' = translate_expr newname lexp acc_ienv in
                let lentry' =
                  UCS.LibVar
                    (translated_i, Option.map ~f:translate_typ topt, lexp')
                in
                pure @@ (lentry' :: acc_lentries, acc_ienv')
          | LibTyp (i, ls) ->
              let ls' =
                List.map ls ~f:(fun t ->
                    {
                      UCS.cname = translate_var t.cname;
                      UCS.c_arg_types = List.map ~f:translate_typ t.c_arg_types;
                    })
              in
              let lentry' = UCS.LibTyp (translate_var i, ls') in
              pure @@ (lentry' :: acc_lentries, acc_ienv))
    in
    pure (List.rev lentries_rev, ienv')

  let translate_lib newname lib ienv =
    let%bind lentries', ienv' =
      translate_lib_entries newname lib.lentries ienv
    in
    let lib' = { UCS.lname = translate_var lib.lname; lentries = lentries' } in
    pure (lib', ienv')

  let rec translate_libtree newname libt =
    let%bind deps_ienv =
      mapM ~f:(fun dep -> translate_libtree newname dep) libt.deps
    in
    let deps', ienv_l = List.unzip deps_ienv in
    let ienv' = List.concat ienv_l in
    let%bind libn', ienv'' = translate_lib newname libt.libn ienv' in
    let libt' = { UCS.libn = libn'; UCS.deps = deps' } in
    pure (libt', ienv'')

  let translate_cmod (cmod : cmodule) rlibs elibs =
    let newname = LoweringUtils.global_newnamer in

    (* Recursion libs. *)
    let%bind rlibs', rlib_ienv = translate_lib_entries newname rlibs [] in
    (* External libs. *)
    let%bind elib_ienv =
      mapM ~f:(fun elib -> translate_libtree newname elib) elibs
    in
    let elibs', elib_ienv =
      let unz = List.unzip elib_ienv in
      (fst unz, List.concat @@ snd unz)
    in

    (* Transform contract library *)
    let%bind clibs', clib_ienv =
      match cmod.libs with
      | None -> pure (None, elib_ienv @ rlib_ienv)
      | Some lib ->
          let%bind lib', ienv =
            translate_lib newname lib (elib_ienv @ rlib_ienv)
          in
          pure (Some lib', ienv)
    in

    (* Translate fields and their init *)
    let%bind fields' =
      mapM
        ~f:(fun (i, t, fexp) ->
          let%bind fexp' = translate_expr newname fexp clib_ienv in
          pure (translate_var i, translate_typ t, fexp'))
        cmod.contr.cfields
    in

    let%bind comps' =
      mapM
        ~f:(fun comp ->
          let%bind body' = translate_stmts newname comp.comp_body clib_ienv in
          pure
            {
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

  let uncurry_in_module (cmod : FPS.cmodule) rlibs elibs =
    let%bind () = translate_adts () in
    let (cmod', rlibs', elibs'), _ = uca_cmod cmod rlibs elibs in
    let%bind cmod'', rlibs'', elibs'' = translate_cmod cmod' rlibs' elibs' in
    (* if (not @@ List.is_empty !debug_msg) || (not @@ List.is_empty !to_uncurry)
       then
         warn0
           (String.concat ~sep:", "
              (!debug_msg @ [ "Functions to uncurry: " ] @ !to_uncurry))
           0; *)
    (* let elibs_s = String.concat ~sep:"\n\n\n"
         (List.map elibs'' ~f:(fun elib -> UCS.pp_library elib.libn)) in
       let lib =
         match cmod''.libs with
         | None -> "None"
         | Some lib -> UCS.pp_library lib
       in
       let pout_msg = "Elibs: " ^ elibs_s ^ "\n\n\n"
                 ^ "Library: " ^ lib ^ "\n\n\n"
                 ^ "Contract: " ^ UCS.pp_contract cmod''.contr ^ "\n\n\n"
       in
       DebugMessage.pout (pout_msg); *)
    pure (cmod'', rlibs'', elibs'')

  (* A wrapper to uncurry pure expressions. *)
  let uncurry_expr_wrapper rlibs elibs (e, erep) =
    let newname = LoweringUtils.global_newnamer in
    let%bind () = translate_adts () in
    let e', _ = expr_uca (e, erep) in

    (* Recursion libs. *)
    let%bind rlibs', ienv0 = translate_lib newname rlibs [] in

    (* External libs. *)
    let%bind elibs', ienv1 =
      let%bind elib0 =
        mapM ~f:(fun elib -> translate_libtree newname elib) elibs
      in
      let elib1, ienv_l = List.unzip elib0 in
      pure (elib1, List.concat ienv_l)
    in
    let%bind e'' = translate_expr newname e' (ienv0 @ ienv1) in
    if (not @@ List.is_empty !debug_msg) || (not @@ List.is_empty !to_uncurry)
    then
      warn0
        (String.concat ~sep:", "
           (!debug_msg @ [ "Functions to uncurry: " ] @ !to_uncurry))
        0;
    let pout_msg = "Expression now: " ^ UCS.pp_expr e'' ^ "\n" in
    DebugMessage.pout pout_msg;
    pure (rlibs', elibs', e'')

  module OutputSyntax = FPS
end
