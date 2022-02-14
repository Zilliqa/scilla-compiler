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
open Syntax
open ErrorUtils
module Literal = Literal.GlobalLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier

open GasCharge.ScillaGasCharge (Identifier.Name)

(* Explicit annotation, with an index into optional auxiliary information. 
 * The auxiliary information is for use in analyses. *)
type eannot = { ea_tp : Type.t option; ea_loc : loc; ea_auxi : int option }
[@@deriving sexp]

let empty_annot =
  { ea_tp = None; ea_loc = ErrorUtils.dummy_loc; ea_auxi = None }

(* Scilla AST with explicit annotations. While having functors is useful
 * when the AST remains same but we expect different annotations, here we have
 * different ASTs at each stage of compilation, making functors harder to work
 * with. So just translate the AST to a simple non-parameterized definition.
 * (The actual coversion is performed by the [AnnotationExplicitizer] pass. *)
module EASyntax = struct
  type payload = MLit of Literal.t | MVar of eannot Identifier.t
  [@@deriving sexp]

  type pattern =
    | Wildcard
    | Binder of eannot Identifier.t
    | Constructor of eannot Identifier.t * pattern list
  [@@deriving sexp]

  type expr_annot = expr * eannot

  and expr =
    | Literal of Literal.t
    | Var of eannot Identifier.t
    | Let of eannot Identifier.t * Type.t option * expr_annot * expr_annot
    | Message of (string * payload) list
    | Fun of eannot Identifier.t * Type.t * expr_annot
    | App of eannot Identifier.t * eannot Identifier.t list
    | Constr of eannot Identifier.t * Type.t list * eannot Identifier.t list
    | MatchExpr of eannot Identifier.t * (pattern * expr_annot) list
    | Builtin of eannot builtin_annot * Type.t list * eannot Identifier.t list
    | TFun of eannot Identifier.t * expr_annot
    | TApp of eannot Identifier.t * Type.t list
    (* Fixpoint combinator: used to implement recursion principles *)
    | Fixpoint of eannot Identifier.t * Type.t * expr_annot
    | GasExpr of gas_charge * expr_annot
  [@@deriving sexp]

  (***************************************************************)
  (* All definions below are identical to the ones in Syntax.ml. *)
  (***************************************************************)

  type bcinfo_query = CurBlockNum | ChainID | Timestamp of eannot Identifier.t
  [@@deriving sexp]

  type stmt_annot = stmt * eannot

  and stmt =
    | Load of eannot Identifier.t * eannot Identifier.t
    | RemoteLoad of
        eannot Identifier.t * eannot Identifier.t * eannot Identifier.t
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
    (* v <-- adr.m[k1][k2][...] OR b <- exists adr.m[k1][k2][...] *)
    (* If the bool is set, then we interpret this as value retrieve,
       otherwise as an "exists" query. *)
    | RemoteMapGet of
        eannot Identifier.t
        * eannot Identifier.t
        * eannot Identifier.t
        * eannot Identifier.t list
        * bool
    | MatchStmt of eannot Identifier.t * (pattern * stmt_annot list) list
    | ReadFromBC of eannot Identifier.t * bcinfo_query
    | AcceptPayment
    | SendMsgs of eannot Identifier.t
    | CreateEvnt of eannot Identifier.t
    | CallProc of eannot Identifier.t * eannot Identifier.t list
    | Iterate of eannot Identifier.t * eannot Identifier.t
    | Throw of eannot Identifier.t option
    | GasStmt of gas_charge
    | TypeCast of eannot Identifier.t * eannot Identifier.t * Type.t

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
    cconstraint : expr_annot;
    cfields : (eannot Identifier.t * Type.t * expr_annot) list;
    ccomps : component list;
  }

  (* Contract module: libary + contract definiton *)
  type cmodule = {
    smver : int;
    (* Scilla major version of the contract. *)
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

  let rec subst_type_in_expr tvar tp (e, rep') =
    (* Function to substitute in a rep. *)
    let subst_rep r =
      let t' = Option.map r.ea_tp ~f:(Type.subst_type_in_type' tvar tp) in
      { r with ea_tp = t' }
    in
    (* Function to substitute in an id. *)
    let subst_id id =
      Identifier.mk_id (Identifier.get_id id)
        (subst_rep (Identifier.get_rep id))
    in
    (* Substitute in rep of the expression itself. *)
    let rep = subst_rep rep' in
    (* Substitute in the expression: *)
    match e with
    | Literal l -> (Literal (Literal.subst_type_in_literal tvar tp l), rep)
    | Var i -> (Var (subst_id i), rep)
    | Fun (f, t, body) ->
        let t_subst = Type.subst_type_in_type' tvar tp t in
        let body_subst = subst_type_in_expr tvar tp body in
        (Fun (subst_id f, t_subst, body_subst), rep)
    | TFun (tv, body) as tf ->
        if Identifier.equal tv tvar then (tf, rep)
        else
          let body_subst = subst_type_in_expr tvar tp body in
          (TFun (tv, body_subst), rep)
    | Constr (n, ts, es) ->
        let ts' =
          List.map ts ~f:(fun t -> Type.subst_type_in_type' tvar tp t)
        in
        let es' = List.map es ~f:subst_id in
        (Constr (n, ts', es'), rep)
    | App (f, args) ->
        let args' = List.map args ~f:subst_id in
        (App (subst_id f, args'), rep)
    | Builtin (b, ts, args) ->
        let args' = List.map args ~f:subst_id in
        (Builtin (b, ts, args'), rep)
    | Let (i, tann, lhs, rhs) ->
        let tann' =
          Option.map tann ~f:(fun t -> Type.subst_type_in_type' tvar tp t)
        in
        let lhs' = subst_type_in_expr tvar tp lhs in
        let rhs' = subst_type_in_expr tvar tp rhs in
        (Let (subst_id i, tann', lhs', rhs'), rep)
    | Message splist ->
        let m' =
          List.map splist ~f:(fun (s, p) ->
              let p' =
                match p with
                | MLit l -> MLit (Literal.subst_type_in_literal tvar tp l)
                | MVar v -> MVar (subst_id v)
              in
              (s, p'))
        in
        (Message m', rep)
    | MatchExpr (e, cs) ->
        let rec subst_pattern p =
          match p with
          | Wildcard -> Wildcard
          | Binder v -> Binder (subst_id v)
          | Constructor (s, pl) -> Constructor (s, List.map pl ~f:subst_pattern)
        in
        let cs' =
          List.map cs ~f:(fun (p, b) ->
              (subst_pattern p, subst_type_in_expr tvar tp b))
        in
        (MatchExpr (subst_id e, cs'), rep)
    | TApp (tf, tl) ->
        let tl' =
          List.map tl ~f:(fun t -> Type.subst_type_in_type' tvar tp t)
        in
        (TApp (subst_id tf, tl'), rep)
    | Fixpoint (f, t, body) ->
        let t' = Type.subst_type_in_type' tvar tp t in
        let body' = subst_type_in_expr tvar tp body in
        (Fixpoint (subst_id f, t', body'), rep)
    | GasExpr (g, e) -> (GasExpr (g, subst_type_in_expr tvar tp e), rep)

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
      | TFun (_, body) -> recurser body bound_vars acc
      | TApp (f, _) ->
          if Identifier.is_mem_id f bound_vars then acc else f :: acc
      | Fun (f, _, body) | Fixpoint (f, _, body) ->
          recurser body (f :: bound_vars) acc
      | Constr (_, _, es) -> get_free es bound_vars @ acc
      | App (f, args) -> get_free (f :: args) bound_vars @ acc
      | Builtin (_f, _ts, args) -> get_free args bound_vars @ acc
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
      | GasExpr (_, sube) -> recurser sube bound_vars acc
    in
    let fvs = recurser erep [] [] in
    Core.List.dedup_and_sort
      ~compare:(fun a b ->
        String.compare (Identifier.as_string a) (Identifier.as_string b))
      fvs

  (* Rename free variable "fromv" to "tov". *)
  let rename_free_var (e, erep) fromv tov =
    let switcher v =
      (* Retain old annotation, but change the name. *)
      if Identifier.equal v fromv then
        Identifier.mk_id (Identifier.get_id tov) (Identifier.get_rep v)
      else v
    in
    let rec recurser (e, erep) =
      match e with
      | Literal _ -> (e, erep)
      | Var v -> (Var (switcher v), erep)
      | TFun (tv, body) -> (TFun (tv, recurser body), erep)
      | TApp (f, tl) -> (TApp (switcher f, tl), erep)
      | Fun (f, t, body) ->
          (* If a new bound is created for "fromv", don't recurse. *)
          if Identifier.equal f fromv then (e, erep)
          else (Fun (f, t, recurser body), erep)
      | Fixpoint (f, t, body) ->
          (* If a new bound is created for "fromv", don't recurse. *)
          if Identifier.equal f fromv then (e, erep)
          else (Fixpoint (f, t, recurser body), erep)
      | Constr (cn, cts, es) ->
          let es' =
            List.map es ~f:(fun i ->
                if Identifier.equal i fromv then tov else i)
          in
          (Constr (cn, cts, es'), erep)
      | App (f, args) ->
          let args' = List.map args ~f:switcher in
          (App (switcher f, args'), erep)
      | Builtin (f, ts, args) ->
          let args' = List.map args ~f:switcher in
          (Builtin (f, ts, args'), erep)
      | Let (i, t, lhs, rhs) ->
          let lhs' = recurser lhs in
          (* If a new bound is created for "fromv", don't recurse. *)
          let rhs' = if Identifier.equal i fromv then rhs else recurser rhs in
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
      | GasExpr (g, e) ->
          let f str =
            Identifier.get_id (switcher (Identifier.mk_id str erep))
          in
          let g' = replace_variable_name ~f g in
          let e' = recurser e in
          (GasExpr (g', e'), erep)
    in

    recurser (e, erep)

  let rename_free_var_stmts stmts fromv tov =
    let switcher v =
      (* Retain old annotation, but change the name. *)
      if Identifier.equal v fromv then
        Identifier.mk_id (Identifier.get_id tov) (Identifier.get_rep v)
      else v
    in
    let rec recurser stmts =
      match stmts with
      | [] -> []
      | ((stmt, srep) as astmt) :: remstmts -> (
          match stmt with
          | Load (x, _) | ReadFromBC (x, _) ->
              (* if fromv is redefined, we stop. *)
              if Identifier.equal fromv x then astmt :: remstmts
              else astmt :: recurser remstmts
          | RemoteLoad (x, addr, f) ->
              let stmt' = (RemoteLoad (x, switcher addr, f), srep) in
              (* if fromv is redefined, we stop. *)
              if Identifier.equal fromv x then stmt' :: remstmts
              else stmt' :: recurser remstmts
          | TypeCast (x, a, t) ->
              let stmt' = (TypeCast (x, switcher a, t), srep) in
              (* if fromv is redefined, we stop. *)
              if Identifier.equal fromv x then stmt' :: remstmts
              else stmt' :: recurser remstmts
          | Store (m, i) -> (Store (m, switcher i), srep) :: recurser remstmts
          | MapUpdate (m, il, io) ->
              let il' = List.map il ~f:switcher in
              let io' = Option.map io ~f:switcher in
              (MapUpdate (m, il', io'), srep) :: recurser remstmts
          | MapGet (i, m, il, b) ->
              let il' = List.map il ~f:switcher in
              let mg' = (MapGet (i, m, il', b), srep) in
              (* if "i" is equal to fromv, that's a redef. Don't rename further. *)
              if Identifier.equal fromv i then mg' :: remstmts
              else mg' :: recurser remstmts
          | RemoteMapGet (i, addr, m, il, b) ->
              let il' = List.map il ~f:switcher in
              let mg' = (RemoteMapGet (i, switcher addr, m, il', b), srep) in
              (* if "i" is equal to fromv, that's a redef. Don't rename further. *)
              if Identifier.equal fromv i then mg' :: remstmts
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
              if Identifier.equal fromv i then bs' :: remstmts
              else bs' :: recurser remstmts
          | MatchStmt (obj, clauses) ->
              let cs' =
                List.map clauses ~f:(fun (p, stmts) ->
                    let bound_vars = get_pattern_bounds p in
                    (* If a new bound is created for "fromv", don't recurse. *)
                    if Identifier.is_mem_id fromv bound_vars then (p, stmts)
                    else (p, recurser stmts))
              in
              (MatchStmt (switcher obj, cs'), srep) :: recurser remstmts
          | GasStmt g ->
              let f str =
                Identifier.get_id (switcher (Identifier.mk_id str srep))
              in
              let g' = replace_variable_name ~f g in
              (GasStmt g', srep) :: recurser remstmts)
    in
    recurser stmts
end
