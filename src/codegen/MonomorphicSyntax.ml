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

(* Scilla AST without parametric polymorphism. *)
module MmphSyntax = struct
  type payload = MLit of Literal.t | MVar of eannot Identifier.t

  type pattern =
    | Wildcard
    | Binder of eannot Identifier.t
    | Constructor of string * pattern list

  (* This is identical to ScillaSyntax.expr except for
   *  - TFun replaced with TFunMap.
   *  - TApp replaced with TFunSel.
   *)
  type expr_annot = expr * eannot

  and expr =
    | Literal of Literal.t
    | Var of eannot Identifier.t
    | Let of eannot Identifier.t * Type.t option * expr_annot * expr_annot
    | Message of (string * payload) list
    | Fun of eannot Identifier.t * Type.t * expr_annot
    | App of eannot Identifier.t * eannot Identifier.t list
    | Constr of string * Type.t list * eannot Identifier.t list
    | MatchExpr of eannot Identifier.t * (pattern * expr_annot) list
    | Builtin of eannot builtin_annot * eannot Identifier.t list
    (* Rather than one polymorphic function, we have expr for each instantiated type. *)
    | TFunMap of (Type.t * expr_annot) list
    (* Select an already instantiated expression of id based on the Type.t.
     * It is expected that id resolves to a TFunMap. *)
    | TFunSel of eannot Identifier.t * Type.t list
    (* Fixpoint combinator: used to implement recursion principles *)
    | Fixpoint of eannot Identifier.t * Type.t * expr_annot

  (***************************************************************)
  (* All definions below are identical to the ones in Syntax.ml. *)
  (***************************************************************)

  type stmt_annot = stmt * eannot

  and stmt =
    | Load of eannot Identifier.t * eannot Identifier.t
    | Store of eannot Identifier.t * eannot Identifier.t
    | Bind of eannot Identifier.t * expr_annot
    (* m[k1][k2][..] := v OR delete m[k1][k2][...] *)
    | MapUpdate of
        eannot Identifier.t
        * eannot Identifier.t list
        * eannot Identifier.t option
    (* v <- m[k1][k2][...] OR b <- exists m[k1][k2][...] *)
    (* If the bool is set, then we interpret this as value retrieve,
         otherwise as an "exists" query. *)
    | MapGet of
        eannot Identifier.t
        * eannot Identifier.t
        * eannot Identifier.t list
        * bool
    | MatchStmt of eannot Identifier.t * (pattern * stmt_annot list) list
    | ReadFromBC of eannot Identifier.t * string
    | AcceptPayment
    | SendMsgs of eannot Identifier.t
    | CreateEvnt of eannot Identifier.t
    | CallProc of eannot Identifier.t * eannot Identifier.t list
    | Iterate of eannot Identifier.t * eannot Identifier.t
    | Throw of eannot Identifier.t option

  type component = {
    comp_type : component_type;
    comp_name : eannot Identifier.t;
    comp_params : (eannot Identifier.t * Type.t) list;
    comp_body : stmt_annot list;
  }

  type ctr_def = { cname : eannot Identifier.t; c_arg_types : Type.t list }

  type lib_entry =
    | LibVar of eannot Identifier.t * Type.t option * expr_annot
    | LibTyp of eannot Identifier.t * ctr_def list

  type library = { lname : eannot Identifier.t; lentries : lib_entry list }

  type contract = {
    cname : eannot Identifier.t;
    cparams : (eannot Identifier.t * Type.t) list;
    cfields : (eannot Identifier.t * Type.t * expr_annot) list;
    ccomps : component list;
  }

  (* Contract module: libary + contract definiton *)
  type cmodule = {
    smver : int;
    (* Scilla major version of the contract. *)
    cname : eannot Identifier.t;
    libs : library option;
    (* lib functions defined in the module *)
    (* List of imports / external libs with an optional namespace. *)
    elibs : (eannot Identifier.t * eannot Identifier.t option) list;
    contr : contract;
  }

  (* Library module *)
  type lmodule = {
    (* List of imports / external libs with an optional namespace. *)
    elibs : (eannot Identifier.t * eannot Identifier.t option) list;
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
      List.filter l ~f:(fun i -> not (Identifier.is_mem_id i bound_vars))
    in

    (* The main function that does the job. *)
    let rec recurser erep bound_vars acc =
      let e, _ = erep in
      match e with
      | Literal _ -> acc
      | Var v -> if Identifier.is_mem_id v bound_vars then acc else v :: acc
      | TFunMap te -> (
          (* Assuming that the free variables are identical across instantiations. *)
          match te with
          | (_, e) :: _ -> recurser e bound_vars acc
          | [] -> acc )
      | Fun (f, _, body) | Fixpoint (f, _, body) ->
          recurser body (f :: bound_vars) acc
      | TFunSel (f, _) ->
          if Identifier.is_mem_id f bound_vars then acc else f :: acc
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
              | MVar v ->
                  if Identifier.is_mem_id v bound_vars then acc else v :: acc)
      | MatchExpr (v, cs) ->
          let fv =
            if Identifier.is_mem_id v bound_vars then acc else v :: acc
          in
          List.fold cs ~init:fv ~f:(fun acc (p, e) ->
              (* bind variables in pattern and recurse for expression. *)
              let bound_vars' = get_pattern_bounds p @ bound_vars in
              recurser e bound_vars' acc)
    in
    let fvs = recurser erep [] [] in
    Core.List.dedup_and_sort
      ~compare:(fun a b ->
        String.compare (Identifier.get_id a) (Identifier.get_id b))
      fvs

  (* Rename free variable "fromv" to "tov". *)
  let rename_free_var (e, erep) fromv tov =
    let switcher v =
      (* Retain old annotation, but change the name. *)
      if Identifier.equal_id v fromv then
        Identifier.asIdL (Identifier.get_id tov) (Identifier.get_rep v)
      else v
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
          if Identifier.equal_id f fromv then (e, erep)
          else (Fun (f, t, recurser body), erep)
      | Fixpoint (f, t, body) ->
          (* If a new bound is created for "fromv", don't recurse. *)
          if Identifier.equal_id f fromv then (e, erep)
          else (Fixpoint (f, t, recurser body), erep)
      | TFunSel (f, tl) -> (TFunSel (switcher f, tl), erep)
      | Constr (cn, cts, es) ->
          let es' =
            List.map es ~f:(fun i ->
                if Identifier.equal_id i fromv then tov else i)
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
          let rhs' =
            if Identifier.equal_id i fromv then rhs else recurser rhs
          in
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
                if Identifier.is_mem_id fromv bound_vars then (p, e)
                else (p, recurser e))
          in
          (MatchExpr (switcher v, cs'), erep)
    in
    recurser (e, erep)

  let rename_free_var_stmts stmts fromv tov =
    let switcher v =
      (* Retain old annotation, but change the name. *)
      if Identifier.equal_id v fromv then
        Identifier.asIdL (Identifier.get_id tov) (Identifier.get_rep v)
      else v
    in
    let rec recurser stmts =
      match stmts with
      | [] -> []
      | ((stmt, srep) as astmt) :: remstmts -> (
          match stmt with
          | Load (x, _) | ReadFromBC (x, _) ->
              (* if fromv is redefined, we stop. *)
              if Identifier.equal_id fromv x then astmt :: remstmts
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
              if Identifier.equal_id fromv i then mg' :: remstmts
              else mg' :: recurser remstmts
          | AcceptPayment -> astmt :: recurser remstmts
          | SendMsgs m -> (SendMsgs (switcher m), srep) :: recurser remstmts
          | CreateEvnt e -> (CreateEvnt (switcher e), srep) :: recurser remstmts
          | Throw t ->
              (Throw (Option.map t ~f:switcher), srep) :: recurser remstmts
          | CallProc (p, al) ->
              let al' = List.map al ~f:switcher in
              (CallProc (p, al'), srep) :: recurser remstmts
          | Iterate (l, p) ->
              (Iterate (switcher l, p), srep) :: recurser remstmts
          | Bind (i, e) ->
              let e' = rename_free_var e fromv tov in
              let bs' = (Bind (i, e'), srep) in
              (* if "i" is equal to fromv, that's a redef. Don't rename further. *)
              if Identifier.equal_id fromv i then bs' :: remstmts
              else bs' :: recurser remstmts
          | MatchStmt (obj, clauses) ->
              let cs' =
                List.map clauses ~f:(fun (p, stmts) ->
                    let bound_vars = get_pattern_bounds p in
                    (* If a new bound is created for "fromv", don't recurse. *)
                    if Identifier.is_mem_id fromv bound_vars then (p, stmts)
                    else (p, recurser stmts))
              in
              (MatchStmt (switcher obj, cs'), srep) :: recurser remstmts )
    in
    recurser stmts
end
