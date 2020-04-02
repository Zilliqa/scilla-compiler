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
open! Int.Replace_polymorphic_compare
open Syntax
open ExplicitAnnotationSyntax
open MonomorphicSyntax
open FlatPatternSyntax
open MonadUtil
open Result.Let_syntax
open TypeUtil.TypeUtilities
open Datatypes

(* Convert nested patterns into flat ones. For the algorithm, see Chapter 5 of 
 * "The implementation of functional programming languages - Simon Peyton Jones". *)
module ScillaCG_FlattenPat = struct
  module FPS = FlatPatSyntax
  module MMS = MmphSyntax
  open MMS

  let translate_payload = function MLit l -> FPS.MLit l | MVar v -> FPS.MVar v

  (* Reorder patterns so that same constructors are grouped.
   * It is safe to reorder different `Constructor`s.
   * It is unsafe to reorder two same `Constructor`s.
   * The input shouldn't contain `Any` patterns. *)
  let reorder_group_patterns pats =
    let eq_cn (el1, _) (el2, _) =
      match (el1, el2) with
      | Constructor (cn1, _), Constructor (cn2, _) when String.(cn1 = cn2) ->
          true
      | _ -> false
    in
    let rec go res rem =
      match rem with
      | [] -> res
      | curp :: rem' ->
          let same_cns, other_cns = List.partition_tf rem' ~f:(eq_cn curp) in
          (* Accummulate the result in reverse order as that's more efficient. *)
          let res' = List.rev (curp :: same_cns) @ res in
          go res' other_cns
    in
    let pats' = List.rev @@ go [] pats in
    List.group pats' ~break:(fun a b -> not (eq_cn a b))

  (* A template of functions to enable re-use of the simplifier for expr and stmts. *)
  type 'a join_t = eannot ident * 'a

  type ('a, 'b, 'rep) match_handlers = {
    match_extractor :
      'b ->
      (eannot ident * (FPS.spattern * 'b) list * 'b join_t option) option * 'rep;
    match_constructor :
      (eannot ident * (FPS.spattern * 'b) list * 'b join_t option) * 'rep -> 'b;
    jump_constructor : eannot ident * 'rep -> 'b;
    renamer : 'a -> eannot ident -> eannot ident -> 'a;
  }

  let match_handlers_expr =
    {
      match_extractor =
        (fun (e, rep) ->
          match e with
          | FPS.MatchExpr (o, clauses, joinopt) ->
              (Some (o, clauses, joinopt), rep)
          | _ -> (None, rep));
      match_constructor =
        (fun ((o, clauses, joinopt), rep) ->
          (FPS.MatchExpr (o, clauses, joinopt), rep));
      jump_constructor = (fun (label, rep) -> (FPS.JumpExpr label, rep));
      renamer = rename_free_var;
    }

  let match_handlers_stmt =
    {
      match_extractor =
        (fun stmt ->
          match stmt with
          | [ (FPS.MatchStmt (o, clauses, joinopt), rep) ] ->
              (Some (o, clauses, joinopt), rep)
          | _ -> (None, empty_annot));
      match_constructor =
        (fun ((o, clauses, joinopt), rep) ->
          [ (FPS.MatchStmt (o, clauses, joinopt), rep) ]);
      jump_constructor = (fun (label, rep) -> [ (FPS.JumpStmt label, rep) ]);
      renamer = rename_free_var_stmts;
    }

  (* The simplifier keeps applying the rules as is described in the reference book. *)
  let match_simplifier subsimplifier newname handlers mrep obj_l clauses_l =
    let rec simplifier joinstack obj_l clauses_l =
      let is_cn (el, _) = match el with Constructor _ -> true | _ -> false in
      let pat_kind_eq p1 p2 =
        (is_cn p1 && is_cn p2) || ((not (is_cn p1)) && not (is_cn p2))
      in
      match clauses_l with
      | [] -> (
          (* No-Clauses Rule. Rule not in book. See errata on the webpage. *)
          match joinstack with
          | top :: _ -> pure (handlers.jump_constructor (top, get_rep top))
          (* If there are no clauses, then we must have a fallback path. *)
          | [] ->
              fail0
                "FlattenPatterns: Internal error: No join point for match \
                 without clauses." )
      | (_, first_clause_rhs) :: _ -> (
          match obj_l with
          | [] ->
              (* Empty rule *)
              subsimplifier first_clause_rhs
          | curobj :: remobjs -> (
              (* We need curobj type and location for use later. *)
              let curobj_tp, curobj_lc =
                ((get_rep curobj).ea_tp, (get_rep curobj).ea_loc)
              in
              (* Extract out the first pattern in each clause, those are the ones first matched. *)
              let%bind curclauses =
                mapM clauses_l ~f:(fun (plist, rhs) ->
                    match plist with
                    | p :: prest -> pure (p, (prest, rhs))
                    | [] ->
                        fail1
                          (Printf.sprintf
                             "FlattenPatterns: Internal error: No pattern to \
                              match against.")
                          mrep.ea_loc)
              in
              let ((first_pat, _) as first_clause), rest_clauses =
                (* we know that clauses is not empty. *)
                (List.hd_exn curclauses, List.tl_exn curclauses)
              in
              (* decide on which of Constructor Rule, Variable Rule or Mixture Rule to apply. *)
              let now_clauses', rem_clauses =
                List.split_while rest_clauses ~f:(pat_kind_eq first_clause)
              in
              let now_clauses = first_clause :: now_clauses' in
              (* Pre-process the join point, if we need it. *)
              let%bind joinopt, joinstack' =
                if List.is_empty rem_clauses then pure (None, joinstack)
                else
                  (* Mixture rule. Generate a join point. *)
                  let jlabel = newname "joinp" mrep in
                  let rem_clauses_l =
                    List.map rem_clauses ~f:(fun (p, (pl, rhs)) ->
                        (p :: pl, rhs))
                  in
                  let%bind join_block =
                    simplifier joinstack obj_l rem_clauses_l
                  in
                  pure (Some (jlabel, join_block), jlabel :: joinstack)
              in
              match first_pat with
              | Constructor (first_cname, _) ->
                  (* Constructor Rule. *)
                  let now_grouped = reorder_group_patterns now_clauses in
                  let%bind spats_rhs =
                    mapM now_grouped ~f:(fun cur_cn_group ->
                        (* First compute the pattern for each branch of the new match. *)
                        let%bind spat, subobjs =
                          match cur_cn_group with
                          | [] ->
                              fail0
                                "FlatternPatterns: Internal error: empty group \
                                 of constructors."
                          | (cur_cn, _) :: _ -> (
                              (* We just look at the first one as they all have same constructor. *)
                              match cur_cn with
                              | Constructor (cname, cargs) ->
                                  (* If "pat" is a Binder, use that name, otherwise the new one provided. *)
                                  let newname' pat (newid, newannot) =
                                    match pat with
                                    | Binder v -> v
                                    | _ -> newname newid newannot
                                  in
                                  let%bind subobjs =
                                    match curobj_tp with
                                    | Some tp ->
                                        let%bind arg_types =
                                          constr_pattern_arg_types tp cname
                                        in
                                        pure
                                        @@ List.map2_exn cargs arg_types
                                             ~f:(fun p tp ->
                                               (* We approximate location of the new binders to curobj's loc. *)
                                               (* See https://github.com/Zilliqa/scilla/issues/456 *)
                                               newname' p
                                                 ( get_id curobj,
                                                   {
                                                     ea_tp = Some tp;
                                                     ea_loc = curobj_lc;
                                                   } ))
                                    | None ->
                                        fail0
                                          ( "FlattenPatterns: Internal error: "
                                          ^ "Unable to determine type of \
                                             object to be matched" )
                                  in
                                  let spat =
                                    FPS.Constructor
                                      ( cname,
                                        List.map subobjs ~f:(fun o ->
                                            FPS.Binder o) )
                                  in
                                  pure (spat, subobjs)
                              | _ ->
                                  fail0
                                    ( "FlattenPatterns: Internal error: "
                                    ^ "Found non constructor pattern when \
                                       handling Constructor rule." ) )
                        in
                        (* Compute the body of each branch of the new match. *)
                        let%bind subclauses =
                          mapM cur_cn_group ~f:(fun (p, (plist, e)) ->
                              match p with
                              | Constructor (_, cargs) -> pure (cargs @ plist, e)
                              | _ ->
                                  fail0
                                    ( "FlattenPatterns: Internal error: "
                                    ^ "Found non constructor pattern when \
                                       handling constructor group." ))
                        in
                        let%bind cur_group_body =
                          simplifier joinstack' (subobjs @ remobjs) subclauses
                        in
                        pure (spat, cur_group_body))
                  in
                  (* If all constructors don't span the entire type, insert a `_` pattern. *)
                  let%bind adtd, _ =
                    DataTypeDictionary.lookup_constructor first_cname
                  in
                  let%bind spats_rhs' =
                    if List.length spats_rhs < List.length adtd.tconstr then
                      let%bind empty_match = simplifier joinstack' [] [] in
                      pure @@ spats_rhs
                      @ [ (FPS.Any FPS.Wildcard, empty_match) ]
                    else pure spats_rhs
                  in
                  pure
                  @@ handlers.match_constructor
                       ((curobj, spats_rhs', joinopt), mrep)
              | Wildcard | Binder _ -> (
                  (* Variable Rule. *)
                  let%bind clauses' =
                    mapM now_clauses ~f:(fun (p, (plist, e)) ->
                        match p with
                        | Wildcard -> pure (plist, e)
                        | Binder v ->
                            let bound_vars_in_rempats =
                              List.fold plist ~init:[] ~f:(fun acc p ->
                                  get_pattern_bounds p @ acc)
                            in
                            if is_mem_id v bound_vars_in_rempats then
                              pure (plist, e)
                              (* We just substitute v directly with curobj. That's the rule. *)
                            else pure (plist, handlers.renamer e v curobj)
                        | Constructor _ ->
                            fail0
                              ( "FlattenPatterns: Internal error: "
                              ^ "Found constructor pattern when handling \
                                 Variable rule." ))
                  in
                  let%bind simplified =
                    simplifier joinstack' remobjs clauses'
                  in
                  let simplified_extracted, r =
                    handlers.match_extractor simplified
                  in
                  match (joinopt, simplified_extracted) with
                  | None, _ ->
                      pure simplified (* There is no possibility of a join. *)
                  | Some _, Some (o, clauses, None) ->
                      pure
                      @@ handlers.match_constructor ((o, clauses, joinopt), r)
                  (* TODO: Can below situation occur at all? assuming that the program
                   * has passed the PatternChecker. If it can, how to handle? *)
                  | _ ->
                      fail0
                        "FlattenPatterns: Internal error: unhandled pattern." )
              ) )
    in
    simplifier [] obj_l clauses_l

  let flatpat_in_expr newname (e, erep) =
    let rec go_expr (e, erep) =
      match e with
      | Literal l -> pure (FPS.Literal l, erep)
      | Var v -> pure (FPS.Var v, erep)
      | Message m ->
          let m' = List.map ~f:(fun (s, p) -> (s, translate_payload p)) m in
          pure (FPS.Message m', erep)
      | App (a, l) -> pure (FPS.App (a, l), erep)
      | Constr (s, tl, il) -> pure (FPS.Constr (s, tl, il), erep)
      | Builtin (i, il) -> pure (FPS.Builtin (i, il), erep)
      | Fixpoint (i, t, body) ->
          let%bind body' = go_expr body in
          pure (FPS.Fixpoint (i, t, body'), erep)
      | Fun (i, t, body) ->
          let%bind body' = go_expr body in
          pure (FPS.Fun (i, t, body'), erep)
      | Let (i, topt, lhs, rhs) ->
          let%bind lhs' = go_expr lhs in
          let%bind rhs' = go_expr rhs in
          pure (FPS.Let (i, topt, lhs', rhs'), erep)
      | TFunMap texprl ->
          let%bind texprl' =
            mapM
              ~f:(fun (t, e) ->
                let%bind e' = go_expr e in
                pure (t, e'))
              texprl
          in
          pure (FPS.TFunMap texprl', erep)
      | TFunSel (i, tl) -> pure (FPS.TFunSel (i, tl), erep)
      | MatchExpr (obj, clauses) ->
          (* Prepare the original match object and clauses as arguments for simplifier. *)
          let obj_l = [ obj ] in
          let clauses_l = List.map clauses ~f:(fun (p, rhs) -> ([ p ], rhs)) in
          match_simplifier go_expr newname match_handlers_expr erep obj_l
            clauses_l
    in

    go_expr (e, erep)

  let flatpat_in_stmts newname stmts =
    let rec go_stmts stmts =
      foldrM stmts ~init:[] ~f:(fun acc (stmt, srep) ->
          match stmt with
          | Load (x, m) ->
              let s' = FPS.Load (x, m) in
              pure @@ ((s', srep) :: acc)
          | Store (m, i) ->
              let s' = FPS.Store (m, i) in
              pure @@ ((s', srep) :: acc)
          | MapUpdate (i, il, io) ->
              let s' = FPS.MapUpdate (i, il, io) in
              pure @@ ((s', srep) :: acc)
          | MapGet (i, i', il, b) ->
              let s' = FPS.MapGet (i, i', il, b) in
              pure @@ ((s', srep) :: acc)
          | ReadFromBC (i, s) ->
              let s' = FPS.ReadFromBC (i, s) in
              pure @@ ((s', srep) :: acc)
          | AcceptPayment ->
              let s' = FPS.AcceptPayment in
              pure @@ ((s', srep) :: acc)
          | SendMsgs m ->
              let s' = FPS.SendMsgs m in
              pure @@ ((s', srep) :: acc)
          | CreateEvnt e ->
              let s' = FPS.CreateEvnt e in
              pure @@ ((s', srep) :: acc)
          | Throw t ->
              let s' = FPS.Throw t in
              pure @@ ((s', srep) :: acc)
          | CallProc (p, al) ->
              let s' = FPS.CallProc (p, al) in
              pure @@ ((s', srep) :: acc)
          | Iterate (l, p) ->
              let s' = FPS.Iterate (l, p) in
              pure @@ ((s', srep) :: acc)
          | Bind (i, e) ->
              let%bind e' = flatpat_in_expr newname e in
              let s' = FPS.Bind (i, e') in
              pure @@ ((s', srep) :: acc)
          | MatchStmt (obj, clauses) -> (
              (* Prepare the original match object and clauses as arguments for simplifier. *)
              let obj_l = [ obj ] in
              let clauses_l =
                List.map clauses ~f:(fun (p, rhs) -> ([ p ], rhs))
              in
              let%bind slist =
                match_simplifier go_stmts newname match_handlers_stmt srep obj_l
                  clauses_l
              in
              match slist with
              | [ s' ] ->
                  pure @@ (s' :: acc)
                  (* match_handlers_stmt guarantees a single element list. *)
              | _ ->
                  fail1
                    ( "FlattenPatterns: Internal error: "
                    ^ "match stmt not translated to a list of one match stmt" )
                    srep.ea_loc ))
    in
    go_stmts stmts

  let flatpat_in_module (cmod : cmodule) rlibs elibs =
    let newname = CodegenUtils.global_newnamer in

    (* Transform each library entry. *)
    let flatpat_in_lib_entries lentries =
      mapM
        ~f:(fun lentry ->
          match lentry with
          | LibVar (i, topt, lexp) ->
              let%bind lexp' = flatpat_in_expr newname lexp in
              pure (FPS.LibVar (i, topt, lexp'))
          | LibTyp (i, ls) ->
              let ls' =
                List.map ls ~f:(fun t ->
                    { FPS.cname = t.cname; FPS.c_arg_types = t.c_arg_types })
              in
              pure (FPS.LibTyp (i, ls')))
        lentries
    in

    (* Recursion libs. *)
    let%bind rlibs' = flatpat_in_lib_entries rlibs in

    (* Function to flatten patterns in a library. *)
    let flatpat_in_lib lib =
      let%bind lentries' = flatpat_in_lib_entries lib.lentries in
      let lib' = { FPS.lname = lib.lname; lentries = lentries' } in
      pure lib'
    in

    (* flatpat_in the library tree. *)
    let rec flatpat_in_libtree libt =
      let%bind deps' = mapM ~f:(fun dep -> flatpat_in_libtree dep) libt.deps in
      let%bind libn' = flatpat_in_lib libt.libn in
      let libt' = { FPS.libn = libn'; FPS.deps = deps' } in
      pure libt'
    in
    let%bind elibs' = mapM ~f:(fun elib -> flatpat_in_libtree elib) elibs in

    (* Transform contract library. *)
    let%bind clibs' =
      match cmod.libs with
      | Some clib ->
          let%bind clib' = flatpat_in_lib clib in
          pure @@ Some clib'
      | None -> pure None
    in

    (* Translate fields and their initializations. *)
    let%bind fields' =
      mapM
        ~f:(fun (i, t, fexp) ->
          let%bind fexp' = flatpat_in_expr newname fexp in
          pure (i, t, fexp'))
        cmod.contr.cfields
    in

    (* Translate all contract components. *)
    let%bind comps' =
      mapM
        ~f:(fun comp ->
          let%bind body' = flatpat_in_stmts newname comp.comp_body in
          pure
            {
              FPS.comp_type = comp.comp_type;
              FPS.comp_name = comp.comp_name;
              FPS.comp_params = comp.comp_params;
              FPS.comp_body = body';
            })
        cmod.contr.ccomps
    in

    let contr' =
      {
        FPS.cname = cmod.contr.cname;
        FPS.cparams = cmod.contr.cparams;
        FPS.cfields = fields';
        ccomps = comps';
      }
    in
    let cmod' =
      {
        FPS.smver = cmod.smver;
        FPS.cname = cmod.cname;
        FPS.elibs = cmod.elibs;
        FPS.libs = clibs';
        FPS.contr = contr';
      }
    in

    (* Return back the whole program, transformed. *)
    pure (cmod', rlibs', elibs')

  (* A wrapper to translate pure expressions. *)
  let flatpat_expr_wrapper ((e, erep) : expr_annot) =
    let newname = CodegenUtils.global_newnamer in
    flatpat_in_expr newname (e, erep)

  module OutputSyntax = FPS
end
