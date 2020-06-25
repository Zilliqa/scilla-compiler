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
  Closure conversion, along with lifting functions to a global scope
  also flattens the AST into statements, with only primitive expressions
  (not let-in bindings) allowed as RHS of statements.

  As a consequence of flattening the AST, it is important to avoid name clashes.

  Examples:
    1. When the below let-in bindings are flattened to statements, we don't
       want the inner "x"'s definition to shadow the outer one's.
        let x = Int32 1 in
        let y =
          let x = Int32 2 in (* We don't want this x to shadow the outer one. *)
          x
        in
        let z = x in
        ...
    2. Here, the definitions of y inside the match should not shadow the outer y.
      (* This isn't as critical as (1) though as the scopes are nested. *)
        y = Int32 31;
        match c with
        | True =>
          y = Int32 101;
          create_event y
        | False =>
          y = Int32 102;
          create_event y
        end;
        create_event y
*)

open Core_kernel
open! Int.Replace_polymorphic_compare
open ExplicitAnnotationSyntax

(* The algorithm:
  A top down traversal of the module / expression with two components in the environment:
    1. A list of variables in scope.
    2. A list of variables to be renamed (and their new name).
  Each new binding is checked to see if it already is in (1). If it is, a new name is
  created for it and an entry is (re)placed in (2).
  Each use of a variable is renamed if it has an entry in (2).
*)

module ScillaCG_ScopingRename = struct
  open EASyntax

  type srenv = {
    (* Variables in scope. *)
    inscope : eannot Identifier.t list;
    (* Renamed variables and their new names. *)
    renamed : (eannot Identifier.t * eannot Identifier.t) list;
  }

  let pp_srnv env =
    "inscope: "
    ^ String.concat ~sep:" " (List.map env.inscope ~f:Identifier.get_id)
    ^ "\n" ^ "renamed: "
    ^ String.concat ~sep:" "
        (List.map env.renamed ~f:(fun (a, b) ->
             "(" ^ Identifier.get_id a ^ "," ^ Identifier.get_id b ^ ")"))
    ^ "\n"

  (* Rename a variable use if its definition has been renamed. *)
  let renamer env var =
    match List.Assoc.find env.renamed ~equal:Identifier.equal var with
    (* When renaming a use, retain its annotation.
     * (the types will be same, but location matters. *)
    | Some newname ->
        Identifier.mk_id (Identifier.get_id newname) (Identifier.get_rep var)
    | None -> var

  (* Check if a new binding is in scope, if it is, mark for it to be renamed. *)
  let handle_new_bind newname env x =
    if Identifier.is_mem_id x env.inscope then
      let x' = newname (Identifier.get_id x) (Identifier.get_rep x) in
      let renamed' = List.Assoc.add env.renamed ~equal:Identifier.equal x x' in
      (* We don't bother to put x' inscope because it's a unique name
       * and we're sure that it won't be rebound later. *)
      (x', { env with renamed = renamed' })
    else (x, { env with inscope = x :: env.inscope })

  let rec scoping_rename_pattern newname env p =
    match p with
    | Wildcard -> (Wildcard, env)
    | Binder v ->
        let v', env' = handle_new_bind newname env v in
        (Binder v', env')
    | Constructor (sname, spblist) ->
        let spblist'_rev, env' =
          List.fold spblist ~init:([], env) ~f:(fun (spblist_rev, env) spb ->
              let spb', env' = scoping_rename_pattern newname env spb in
              (spb' :: spblist_rev, env'))
        in
        (Constructor (sname, List.rev spblist'_rev), env')

  let rec scoping_rename_expr newname env (e, erep) =
    match e with
    | Literal _ -> ((e, erep), env)
    | Var v -> ((Var (renamer env v), erep), env)
    | Message pllist ->
        let pllist' =
          List.map pllist ~f:(fun (s, pl) ->
              match pl with
              | MLit _ -> (s, pl)
              | MVar v -> (s, MVar (renamer env v)))
        in
        ((Message pllist', erep), env)
    | Constr (cname, ts, ilist) ->
        ((Constr (cname, ts, List.map ilist ~f:(renamer env)), erep), env)
    | Builtin (fname, ilist) ->
        ((Builtin (fname, List.map ilist ~f:(renamer env)), erep), env)
    | App (fname, ilist) ->
        ((App (renamer env fname, List.map ilist ~f:(renamer env)), erep), env)
    | Let (i, topt, lhs, rhs) ->
        let lhs', env_lhs = scoping_rename_expr newname env lhs in
        let i', env' = handle_new_bind newname env_lhs i in
        let rhs', env_rhs = scoping_rename_expr newname env' rhs in
        (* We shouldn't rename variables bound in this expression, outside of it. *)
        let env_ret = { env_rhs with renamed = env.renamed } in
        ((Let (i', topt, lhs', rhs'), erep), env_ret)
    | MatchExpr (i, clauses) ->
        let i' = renamer env i in
        let clauses' =
          List.map clauses ~f:(fun (sp, branche) ->
              let sp', env' = scoping_rename_pattern newname env sp in
              let branche', _ = scoping_rename_expr newname env' branche in
              (sp', branche'))
        in
        ((MatchExpr (i', clauses'), erep), env)
    | Fun (i, t, body) ->
        let i', env' = handle_new_bind newname env i in
        let body', _ = scoping_rename_expr newname env' body in
        ((Fun (i', t, body'), erep), env)
    | TFun (tv, body) ->
        ((TFun (tv, fst (scoping_rename_expr newname env body)), erep), env)
    | Fixpoint (i, t, body) ->
        let i', env' = handle_new_bind newname env i in
        let body', _ = scoping_rename_expr newname env' body in
        ((Fixpoint (i', t, body'), erep), env)
    | TApp (tf, targs) -> ((TApp (renamer env tf, targs), erep), env)

  let rec scoping_rename_stmts newname env stmts =
    List.rev @@ fst
    @@ (* Fold over all statements, accumulating an environment and building
        * the renamed list of statements (in reverse order). *)
    List.fold stmts ~init:([], env) ~f:(fun (stmts_rev, env) (stmt, srep) ->
        match stmt with
        | Load (x, m) ->
            let x', env' = handle_new_bind newname env x in
            ((Load (x', m), srep) :: stmts_rev, env')
        | Store (m, i) -> ((Store (m, renamer env i), srep) :: stmts_rev, env)
        | MapUpdate (i, il, io) ->
            let s' =
              MapUpdate
                ( renamer env i,
                  List.map il ~f:(renamer env),
                  Option.map io ~f:(renamer env) )
            in
            ((s', srep) :: stmts_rev, env)
        | MapGet (x, i, il, b) ->
            let x', env' = handle_new_bind newname env x in
            let s' =
              MapGet (x', renamer env i, List.map il ~f:(renamer env), b)
            in
            ((s', srep) :: stmts_rev, env')
        | ReadFromBC (x, s) ->
            let x', env' = handle_new_bind newname env x in
            ((ReadFromBC (x', s), srep) :: stmts_rev, env')
        | AcceptPayment -> ((stmt, srep) :: stmts_rev, env)
        | SendMsgs m -> ((SendMsgs (renamer env m), srep) :: stmts_rev, env)
        | CreateEvnt e -> ((CreateEvnt (renamer env e), srep) :: stmts_rev, env)
        | Throw t ->
            ((Throw (Option.map t ~f:(renamer env)), srep) :: stmts_rev, env)
        | CallProc (p, al) ->
            ( (CallProc (renamer env p, List.map al ~f:(renamer env)), srep)
              :: stmts_rev,
              env )
        | Iterate (l, p) ->
            ((Iterate (renamer env l, renamer env p), srep) :: stmts_rev, env)
        | Bind (x, e) ->
            let e', env_rhs = scoping_rename_expr newname env e in
            let x', env' = handle_new_bind newname env_rhs x in
            ((Bind (x', e'), srep) :: stmts_rev, env')
        | MatchStmt (i, clauses) ->
            let i' = renamer env i in
            let clauses' =
              List.map clauses ~f:(fun (sp, branchs) ->
                  let sp', env' = scoping_rename_pattern newname env sp in
                  let branchs' = scoping_rename_stmts newname env' branchs in
                  (sp', branchs'))
            in
            ((MatchStmt (i', clauses'), srep) :: stmts_rev, env))

  let rename_lib_entries newname env lentries =
    let lentries'_rev, env' =
      List.fold ~init:([], env)
        ~f:(fun (lentries_rev, env) lentry ->
          match lentry with
          | LibVar (i, t, lexp) ->
              let lexp', env_rhs = scoping_rename_expr newname env lexp in
              let i', env' = handle_new_bind newname env_rhs i in
              (LibVar (i', t, lexp') :: lentries_rev, env')
          | LibTyp _ -> (lentry :: lentries_rev, env))
        lentries
    in
    (List.rev lentries'_rev, env')

  let rename_lib newname env lib =
    let lentries', env' = rename_lib_entries newname env lib.lentries in
    ({ lib with lentries = lentries' }, env')

  (* Rename external libraries (libtree). *)
  let rec rename_libtree newname env libt =
    let deps'_rev, env' =
      List.fold ~init:([], env)
        ~f:(fun (deps_rev, env) dep ->
          let dep', env' = rename_libtree newname env dep in
          (dep' :: deps_rev, env'))
        libt.deps
    in
    let libn', env' = rename_lib newname env' libt.libn in
    ({ libn = libn'; deps = List.rev deps'_rev }, env')

  let scoping_rename_module (cmod : cmodule) rlibs elibs =
    let newname = CodegenUtils.global_newnamer in

    let env_empty = { inscope = []; renamed = [] } in
    (* recursion libs are the first definitions, start with them. *)
    let rlibs', rlib_env = rename_lib_entries newname env_empty rlibs in

    let elibs'_rev, env_elibs =
      List.fold elibs ~init:([], rlib_env) ~f:(fun (elibs_rev, env) elib ->
          let elib', env' = rename_libtree newname env elib in
          (elib' :: elibs_rev, env'))
    in

    (* Rename contract library. *)
    let clib', env_clib =
      match cmod.libs with
      | Some clib ->
          let clib', env' = rename_lib newname env_elibs clib in
          (Some clib', env')
      | None -> (None, env_elibs)
    in

    (* Translate field initialization expressions to statements. *)
    let cfields'_rev, env_cfields =
      List.fold cmod.contr.cfields ~init:([], env_clib)
        ~f:(fun (cfields_rev, env) (f, t, fexp) ->
          let fexp', env_rhs = scoping_rename_expr newname env fexp in
          let f', env' = handle_new_bind newname env_rhs f in
          ((f', t, fexp') :: cfields_rev, env'))
    in

    (* Rename all transitions / procedures. They're all independent. *)
    let ccomps' =
      List.map cmod.contr.ccomps ~f:(fun comp ->
          let comp_body' =
            scoping_rename_stmts newname env_cfields comp.comp_body
          in
          {
            comp_type = comp.comp_type;
            comp_name = comp.comp_name;
            comp_params = comp.comp_params;
            comp_body = comp_body';
          })
    in

    let contr' =
      {
        cname = cmod.contr.cname;
        cparams = cmod.contr.cparams;
        cfields = List.rev cfields'_rev;
        ccomps = ccomps';
      }
    in

    let cmod' =
      { smver = cmod.smver; elibs = cmod.elibs; libs = clib'; contr = contr' }
    in

    (cmod', rlibs', List.rev elibs'_rev)

  (* A wrapper to translate pure expressions. *)
  let scoping_rename_expr_wrapper rlibs elibs e =
    let newname = CodegenUtils.global_newnamer in
    let env_empty = { inscope = []; renamed = [] } in

    (* recursion libs are the first definitions, start with them. *)
    let rlibs', rlib_env = rename_lib newname env_empty rlibs in
    let elibs'_rev, env_elibs =
      List.fold elibs ~init:([], rlib_env) ~f:(fun (elibs_rev, env) elib ->
          let elib', env' = rename_libtree newname env elib in
          (elib' :: elibs_rev, env'))
    in
    let e', _env_v = scoping_rename_expr newname env_elibs e in
    (rlibs', List.rev elibs'_rev, e')

  module OutputSyntax = ExplicitAnnotationSyntax
end
