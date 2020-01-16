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

open Syntax
open ExplicitAnnotationSyntax
open Core

(* Scilla AST without parametric polymorphism. *)
module MmphSyntax = struct
  type payload = MLit of literal | MVar of eannot ident

  type pattern =
    | Wildcard
    | Binder of eannot ident
    | Constructor of string * pattern list

  (* This is identical to ScillaSyntax.expr except for
   *  - TFun replaced with TFunMap.
   *  - TApp replaced with TFunSel.
   *)
  type expr_annot = expr * eannot

  and expr =
    | Literal of literal
    | Var of eannot ident
    | Let of eannot ident * typ option * expr_annot * expr_annot
    | Message of (string * payload) list
    | Fun of eannot ident * typ * expr_annot
    | App of eannot ident * eannot ident list
    | Constr of string * typ list * eannot ident list
    | MatchExpr of eannot ident * (pattern * expr_annot) list
    | Builtin of eannot builtin_annot * eannot ident list
    (* Rather than one polymorphic function, we have expr for each instantiated type. *)
    | TFunMap of (typ * expr_annot) list
    (* Select an already instantiated expression of id based on the typ.
     * It is expected that id resolves to a TFunMap. *)
    | TFunSel of eannot ident * typ list
    (* Fixpoint combinator: used to implement recursion principles *)
    | Fixpoint of eannot ident * typ * expr_annot

  (***************************************************************)
  (* All definions below are identical to the ones in Syntax.ml. *)
  (***************************************************************)

  type stmt_annot = stmt * eannot

  and stmt =
    | Load of eannot ident * eannot ident
    | Store of eannot ident * eannot ident
    | Bind of eannot ident * expr_annot
    (* m[k1][k2][..] := v OR delete m[k1][k2][...] *)
    | MapUpdate of eannot ident * eannot ident list * eannot ident option
    (* v <- m[k1][k2][...] OR b <- exists m[k1][k2][...] *)
    (* If the bool is set, then we interpret this as value retrieve, 
         otherwise as an "exists" query. *)
    | MapGet of eannot ident * eannot ident * eannot ident list * bool
    | MatchStmt of eannot ident * (pattern * stmt_annot list) list
    | ReadFromBC of eannot ident * string
    | AcceptPayment
    | SendMsgs of eannot ident
    | CreateEvnt of eannot ident
    | CallProc of eannot ident * eannot ident list
    | Throw of eannot ident option

  type component = {
    comp_type : component_type;
    comp_name : eannot ident;
    comp_params : (eannot ident * typ) list;
    comp_body : stmt_annot list;
  }

  type ctr_def = { cname : eannot ident; c_arg_types : typ list }

  type lib_entry =
    | LibVar of eannot ident * typ option * expr_annot
    | LibTyp of eannot ident * ctr_def list

  type library = { lname : eannot ident; lentries : lib_entry list }

  type contract = {
    cname : eannot ident;
    cparams : (eannot ident * typ) list;
    cfields : (eannot ident * typ * expr_annot) list;
    ccomps : component list;
  }

  (* Contract module: libary + contract definiton *)
  type cmodule = {
    smver : int;
    (* Scilla major version of the contract. *)
    cname : eannot ident;
    libs : library option;
    (* lib functions defined in the module *)
    (* List of imports / external libs with an optional namespace. *)
    elibs : (eannot ident * eannot ident option) list;
    contr : contract;
  }

  (* Library module *)
  type lmodule = {
    (* List of imports / external libs with an optional namespace. *)
    elibs : (eannot ident * eannot ident option) list;
    libs : library; (* lib functions defined in the module *)
  }

  (* A tree of libraries linked to their dependents *)
  type libtree = {
    libn : library;
    (* The library this node represents *)
    deps : libtree list; (* List of dependent libraries *)
  }

  (* get variables that get bound in pattern. *)
  let get_pattern_bounds p =
    let rec accfunc p acc =
      match p with
      | Wildcard -> acc
      | Binder i -> i :: acc
      | Constructor (_, plist) ->
          List.fold plist ~init:acc ~f:(fun acc p' -> accfunc p' acc)
    in
    accfunc p []

  (* Returns a list of free variables in expr. *)
  let free_vars_in_expr erep =
    (* get elements in "l" that are not in bound_vars. *)
    let get_free l bound_vars =
      List.filter l ~f:(fun i -> not (is_mem_id i bound_vars))
    in

    (* The main function that does the job. *)
    let rec recurser erep bound_vars acc =
      let e, _ = erep in
      match e with
      | Literal _ -> acc
      | Var v -> if is_mem_id v bound_vars then acc else v :: acc
      | TFunMap te -> (
          (* Assuming that the free variables are identical across instantiations. *)
          match te with
          | (_, e) :: _ -> recurser e bound_vars acc
          | [] -> acc )
      | Fun (f, _, body) | Fixpoint (f, _, body) ->
          recurser body (f :: bound_vars) acc
      | TFunSel (f, _) -> if is_mem_id f bound_vars then acc else f :: acc
      | Constr (_, _, es) -> get_free es bound_vars @ acc
      | App (f, args) -> get_free (f :: args) bound_vars @ acc
      | Builtin (_f, args) -> get_free args bound_vars @ acc
      | Let (i, _, lhs, rhs) ->
          let acc_lhs = recurser lhs bound_vars acc in
          recurser rhs (i :: bound_vars) acc_lhs
      | Message margs ->
          List.fold margs ~init:acc ~f:(fun acc (_, x) ->
              match x with
              | MLit _ -> acc
              | MVar v -> if is_mem_id v bound_vars then acc else v :: acc)
      | MatchExpr (v, cs) ->
          let fv = if is_mem_id v bound_vars then acc else v :: acc in
          List.fold cs ~init:fv ~f:(fun acc (p, e) ->
              (* bind variables in pattern and recurse for expression. *)
              let bound_vars' = get_pattern_bounds p @ bound_vars in
              recurser e bound_vars' acc)
    in
    let fvs = recurser erep [] [] in
    Core.List.dedup_and_sort
      ~compare:(fun a b -> String.compare (get_id a) (get_id b))
      fvs

  (* Rename free variable "fromv" to "tov". *)
  let rename_free_var (e, erep) fromv tov =
    let switcher v =
      (* Retain old annotation, but change the name. *)
      if get_id v = get_id fromv then asIdL (get_id tov) (get_rep v) else v
    in
    let rec recurser (e, erep) =
      match e with
      | Literal _ -> (e, erep)
      | Var v -> (Var (switcher v), erep)
      | TFunMap tbodyl ->
          let tbodyl' =
            List.map tbodyl ~f:(fun (t, body) -> (t, recurser body))
          in
          (TFunMap tbodyl', erep)
      | Fun (f, t, body) ->
          (* If a new bound is created for "fromv", don't recurse. *)
          if get_id f = get_id fromv then (e, erep)
          else (Fun (f, t, recurser body), erep)
      | Fixpoint (f, t, body) ->
          (* If a new bound is created for "fromv", don't recurse. *)
          if get_id f = get_id fromv then (e, erep)
          else (Fixpoint (f, t, recurser body), erep)
      | TFunSel (f, tl) -> (TFunSel (switcher f, tl), erep)
      | Constr (cn, cts, es) ->
          let es' =
            List.map es ~f:(fun i -> if get_id i = get_id fromv then tov else i)
          in
          (Constr (cn, cts, es'), erep)
      | App (f, args) ->
          let args' = List.map args ~f:switcher in
          (App (switcher f, args'), erep)
      | Builtin (f, args) ->
          let args' = List.map args ~f:switcher in
          (Builtin (f, args'), erep)
      | Let (i, t, lhs, rhs) ->
          let lhs' = recurser lhs in
          (* If a new bound is created for "fromv", don't recurse. *)
          let rhs' = if get_id i = get_id fromv then rhs else recurser rhs in
          (Let (i, t, lhs', rhs'), erep)
      | Message margs ->
          let margs' =
            List.map margs ~f:(fun (s, x) ->
                match x with
                | MLit _ -> (s, x)
                | MVar v -> (s, MVar (switcher v)))
          in
          (Message margs', erep)
      | MatchExpr (v, cs) ->
          let cs' =
            List.map cs ~f:(fun (p, e) ->
                let bound_vars = get_pattern_bounds p in
                (* If a new bound is created for "fromv", don't recurse. *)
                if is_mem_id fromv bound_vars then (p, e) else (p, recurser e))
          in
          (MatchExpr (switcher v, cs'), erep)
    in
    recurser (e, erep)

  let rename_free_var_stmts stmts fromv tov =
    let switcher v =
      (* Retain old annotation, but change the name. *)
      if get_id v = get_id fromv then asIdL (get_id tov) (get_rep v) else v
    in
    let rec recurser stmts =
      match stmts with
      | [] -> []
      | ((stmt, srep) as astmt) :: remstmts -> (
          match stmt with
          | Load (x, _) | ReadFromBC (x, _) ->
              (* if fromv is redefined, we stop. *)
              if equal_id fromv x then astmt :: remstmts
              else astmt :: recurser remstmts
          | Store (m, i) -> (Store (m, switcher i), srep) :: recurser remstmts
          | MapUpdate (m, il, io) ->
              let il' = List.map il ~f:switcher in
              let io' = Option.map io ~f:switcher in
              (MapUpdate (m, il', io'), srep) :: recurser remstmts
          | MapGet (i, m, il, b) ->
              let il' = List.map il ~f:switcher in
              let mg' = (MapGet (i, m, il', b), srep) in
              (* if "i" is equal to fromv, that's a redef. Don't rename further. *)
              if equal_id fromv i then mg' :: remstmts
              else mg' :: recurser remstmts
          | AcceptPayment -> astmt :: recurser remstmts
          | SendMsgs m -> (SendMsgs (switcher m), srep) :: recurser remstmts
          | CreateEvnt e -> (CreateEvnt (switcher e), srep) :: recurser remstmts
          | Throw t ->
              (Throw (Option.map t ~f:switcher), srep) :: recurser remstmts
          | CallProc (p, al) ->
              let al' = List.map al ~f:switcher in
              (CallProc (p, al'), srep) :: recurser remstmts
          | Bind (i, e) ->
              let e' = rename_free_var e fromv tov in
              let bs' = (Bind (i, e'), srep) in
              (* if "i" is equal to fromv, that's a redef. Don't rename further. *)
              if equal_id fromv i then bs' :: remstmts
              else bs' :: recurser remstmts
          | MatchStmt (obj, clauses) ->
              let cs' =
                List.map clauses ~f:(fun (p, stmts) ->
                    let bound_vars = get_pattern_bounds p in
                    (* If a new bound is created for "fromv", don't recurse. *)
                    if is_mem_id fromv bound_vars then (p, stmts)
                    else (p, recurser stmts))
              in
              (MatchStmt (switcher obj, cs'), srep) :: recurser remstmts )
    in
    recurser stmts
end
