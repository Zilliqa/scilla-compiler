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

open Core
open Result.Let_syntax
open Scilla_base
module PrimType = Type.PrimType
module Literal = Literal.GlobalLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open MonadUtil
open Syntax
open ErrorUtils
open GasCharge.ScillaGasCharge (Identifier.Name)
module IdLoc_Comp = Scilla_base.Type.IdLoc_Comp (Identifier)

(* This file defines an AST, which is a variation of FlatPatternSyntax
 * with uncurried semantics for functions and their applications.
 *)
module Uncurried_Syntax = struct
  (* The types of addresses we care about.
   * Lattice:
        AnyAddr
           |
        CodeAddr
          / \
    LibAddr ContrAddr
   *)
  type 'a addr_kind =
    (* Any address in use. *)
    | AnyAddr
    (* Address containing a library or contract. *)
    | CodeAddr
    (* Address containing a library. *)
    | LibAddr
    (* Address containing a contract. *)
    | ContrAddr of 'a IdLoc_Comp.Map.t
  [@@deriving sexp]

  (* Same as Syntax.typ, except for FunType *)
  type typ =
    | PrimType of PrimType.t
    | MapType of typ * typ
    (* A function can take more than one argument. *)
    | FunType of typ list * typ
    | ADT of loc Identifier.t * typ list
    (* Type variables only have a possible auxiliary annotation *)
    | TypeVar of eannot Identifier.t
    | PolyFun of eannot Identifier.t * typ
    (* Some fts if a contract address, None if any address in use *)
    | Address of typ addr_kind
    | Unit

  (* Explicit annotation. *)
  and eannot = { ea_tp : typ option; ea_loc : loc; ea_auxi : int option }
  [@@deriving sexp]

  type mtype = typ * typ

  (* Same as Syntax.literal, but Syntax.typ is replaced with typ.
   * Clo and TAbs are removed too as we don't need them for the compiler. *)
  type literal =
    | StringLit of string
    (* Cannot have different integer literals here directly as Stdint does not derive sexp. *)
    | IntLit of Literal.int_lit
    | UintLit of Literal.uint_lit
    | BNum of Scilla_base.Literal.BNumLit.t
    (* Byte string with a statically known length. *)
    | ByStrX of Literal.Bystrx.t
    (* Byte string without a statically known length. *)
    | ByStr of Literal.Bystr.t
    (* Message: an associative array *)
    | Msg of (string * typ * literal) list
    (* A dynamic map of literals *)
    | Map of mtype * (literal, literal) Caml.Hashtbl.t
    (* A constructor in HNF *)
    | ADTValue of Name.t * typ list * literal list

  let empty_annot =
    { ea_tp = None; ea_loc = ErrorUtils.dummy_loc; ea_auxi = None }

  let mk_noannot_id s =
    Identifier.mk_id (Identifier.Name.parse_simple_name s) empty_annot

  let mk_annot_id s ea =
    Identifier.mk_id (Identifier.Name.parse_simple_name s) ea

  type payload = MLit of literal | MVar of eannot Identifier.t
  type spattern_base = Wildcard | Binder of eannot Identifier.t

  type spattern =
    | Any of spattern_base
    | Constructor of eannot Identifier.t * spattern_base list

  type expr_annot = expr * eannot
  and join_e = eannot Identifier.t * expr_annot

  and expr =
    | Literal of literal
    | Var of eannot Identifier.t
    | Let of eannot Identifier.t * typ option * expr_annot * expr_annot
    | Message of (string * payload) list
    (* A function can take more than one argument. *)
    | Fun of (eannot Identifier.t * typ) list * expr_annot
    | Fixpoint of eannot Identifier.t * typ * expr_annot
    (* Uncurried semantics for App. *)
    | App of eannot Identifier.t * eannot Identifier.t list
    | Constr of eannot Identifier.t * typ list * eannot Identifier.t list
    (* A match expr can optionally have a join point. *)
    | MatchExpr of
        eannot Identifier.t * (spattern * expr_annot) list * join_e option
    (* Transfers control to a (not necessarily immediate) enclosing match's join. *)
    | JumpExpr of eannot Identifier.t
    | Builtin of eannot builtin_annot * typ list * eannot Identifier.t list
    | TFun of eannot Identifier.t * expr_annot
    | TApp of eannot Identifier.t * typ list
    | GasExpr of gas_charge * expr_annot

  (***************************************************************)
  (* All definions below are identical to the ones in Syntax.ml. *)
  (***************************************************************)
  type bcinfo_query =
    | CurBlockNum
    | ChainID
    | Timestamp of eannot Identifier.t
    (* REPLICATE_CONTRACT(addr, init_params) *)
    | ReplicateContr of (eannot Identifier.t * eannot Identifier.t)
  [@@deriving sexp]

  type stmt_annot = stmt * eannot
  and join_s = eannot Identifier.t * stmt_annot list

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
    (* A match statement can optionally have a join point. *)
    | MatchStmt of
        eannot Identifier.t * (spattern * stmt_annot list) list * join_s option
    (* Transfers control to a (not necessarily immediate) enclosing match's join. *)
    | JumpStmt of eannot Identifier.t
    | ReadFromBC of eannot Identifier.t * bcinfo_query
    | AcceptPayment
    | SendMsgs of eannot Identifier.t
    | CreateEvnt of eannot Identifier.t
    | CallProc of eannot Identifier.t * eannot Identifier.t list
    (* forall l p *)
    | Iterate of eannot Identifier.t * eannot Identifier.t
    | Throw of eannot Identifier.t option
    | GasStmt of gas_charge
    | TypeCast of eannot Identifier.t * eannot Identifier.t * typ

  type component = {
    comp_type : component_type;
    comp_name : eannot Identifier.t;
    comp_params : (eannot Identifier.t * typ) list;
    comp_body : stmt_annot list;
  }

  type ctr_def = { cname : eannot Identifier.t; c_arg_types : typ list }

  type lib_entry =
    | LibVar of eannot Identifier.t * typ option * expr_annot
    | LibTyp of eannot Identifier.t * ctr_def list

  type library = { lname : eannot Identifier.t; lentries : lib_entry list }

  type contract = {
    cname : eannot Identifier.t;
    cparams : (eannot Identifier.t * typ) list;
    cconstraint : expr_annot;
    cfields : (eannot Identifier.t * typ * expr_annot) list;
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
  let get_spattern_base_bounds = function Wildcard -> [] | Binder i -> [ i ]

  let get_spattern_bounds p =
    match p with
    | Any b -> get_spattern_base_bounds b
    | Constructor (_, plist) ->
        List.fold plist ~init:[] ~f:(fun acc p' ->
            get_spattern_base_bounds p' @ acc)

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
      | Fun (arglist, body) ->
          recurser body ((List.unzip arglist |> fst) @ bound_vars) acc
      | Fixpoint (f, _, body) -> recurser body (f :: bound_vars) acc
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
      | MatchExpr (v, cs, jopt) ->
          let fv =
            if Identifier.is_mem_id v bound_vars then acc else v :: acc
          in
          let acc' =
            match jopt with
            | Some (_lbl, e) ->
                (* The label isn't considered a free variable. *)
                recurser e bound_vars fv
            | None -> fv
          in
          List.fold cs ~init:acc' ~f:(fun acc (p, e) ->
              (* bind variables in pattern and recurse for expression. *)
              let bound_vars' = get_spattern_bounds p @ bound_vars in
              recurser e bound_vars' acc)
      | JumpExpr _ -> acc
      (* Free variables in the jump target aren't considered here. *)
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
      | Fun (arg_typ_l, body) ->
          let arg_l, _ = List.unzip arg_typ_l in
          (* If a new bound is created for "fromv", don't recurse. *)
          if Identifier.is_mem_id fromv arg_l then (e, erep)
          else (Fun (arg_typ_l, recurser body), erep)
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
      | MatchExpr (v, cs, jopt) ->
          let cs' =
            List.map cs ~f:(fun (p, e) ->
                let bound_vars = get_spattern_bounds p in
                (* If a new bound is created for "fromv", don't recurse. *)
                if Identifier.is_mem_id fromv bound_vars then (p, e)
                else (p, recurser e))
          in
          let jopt' =
            match jopt with
            | Some (lbl, e) -> Some (lbl, recurser e)
            | None -> jopt
          in
          (MatchExpr (switcher v, cs', jopt'), erep)
      | JumpExpr _ as je ->
          (* Renaming for target will happen from it's parent match. *)
          (je, erep)
      | GasExpr (g, e) ->
          let f str =
            Identifier.get_id (switcher (Identifier.mk_id str erep))
          in
          let g' = replace_variable_name ~f g in
          let e' = recurser e in
          (GasExpr (g', e'), erep)
    in
    recurser (e, erep)

  let pp_typ_helper is_error t =
    let rec recurser = function
      | PrimType t -> PrimType.pp_prim_typ t
      | MapType (kt, vt) -> sprintf "Map (%s) (%s)" (recurser kt) (recurser vt)
      | ADT (name, targs) ->
          let elems =
            (if is_error then Identifier.as_error_string name
            else Identifier.as_string name)
            :: List.map targs ~f:(fun t -> sprintf "(%s)" (recurser t))
          in
          String.concat ~sep:" " elems
      | FunType (at, vt) ->
          let at' = List.map at ~f:recurser in
          sprintf "[%s] -> %s" (String.concat ~sep:"," at') (with_paren vt)
      | TypeVar tv -> Identifier.as_string tv
      | PolyFun (tv, bt) ->
          sprintf "forall %s. %s" (Identifier.as_string tv) (recurser bt)
      | Unit -> sprintf "()"
      | Address AnyAddr -> "ByStr20 with end"
      | Address CodeAddr -> "ByStr20 with _codehash end"
      | Address LibAddr -> "ByStr20 with library end"
      | Address (ContrAddr fts) ->
          let elems =
            List.map (IdLoc_Comp.Map.to_alist fts) ~f:(fun (f, t) ->
                sprintf "field %s : %s"
                  (if is_error then Identifier.as_error_string f
                  else Identifier.as_string f)
                  (recurser t))
            |> String.concat ~sep:", "
          in
          sprintf "ByStr20 with contract %s%send" elems
            (if IdLoc_Comp.Map.is_empty fts then "" else " ")
    and with_paren t =
      match t with
      | FunType _ | PolyFun _ -> sprintf "(%s)" (recurser t)
      | _ -> recurser t
    in
    recurser t

  let pp_typ = pp_typ_helper false
  let pp_typ_error = pp_typ_helper true

  (* This is pretty much a redefinition of pp_literal for Syntax.literal. *)
  let rec pp_literal l =
    let open Stdint in
    match l with
    | StringLit s -> "(String " ^ "\"" ^ s ^ "\"" ^ ")"
    (* (bit-width, value) *)
    | IntLit i ->
        "(Int"
        ^ Int.to_string (Literal.int_lit_width i)
        ^ " "
        ^ Literal.string_of_int_lit i
        ^ ")"
    (* (bit-width, value) *)
    | UintLit i ->
        "(Uint"
        ^ Int.to_string (Literal.uint_lit_width i)
        ^ " "
        ^ Literal.string_of_uint_lit i
        ^ ")"
    | BNum b -> "(BNum " ^ Scilla_base.Literal.BNumLit.get b ^ ")"
    | ByStr bs -> "(ByStr " ^ Literal.Bystr.hex_encoding bs ^ ")"
    | ByStrX bsx ->
        "(ByStr"
        ^ Int.to_string (Literal.Bystrx.width bsx)
        ^ " "
        ^ Literal.Bystrx.hex_encoding bsx
        ^ ")"
    | Msg m ->
        let items =
          "["
          ^ List.fold_left m ~init:"" ~f:(fun a (s, t, l') ->
                let t =
                  "(" ^ s ^ " : " ^ pp_typ t ^ " : " ^ pp_literal l' ^ ")"
                in
                if String.is_empty a then t else a ^ " ; " ^ t)
          ^ "]"
        in
        "(Message " ^ items ^ ")"
    | Map ((kt, vt), kv) ->
        let items =
          "["
          ^ Caml.Hashtbl.fold
              (fun k v a ->
                let t = "(" ^ pp_literal k ^ " => " ^ pp_literal v ^ ")" in
                if String.is_empty a then t else a ^ "; " ^ t)
              kv ""
          ^ "]"
        in
        "(Map " ^ pp_typ kt ^ " " ^ pp_typ vt ^ " " ^ items ^ ")"
    | ADTValue (cn, _, al) -> (
        match cn with
        | _ when Datatypes.is_cons_ctr_name cn ->
            (* Print non-empty lists in a readable way. *)
            let list_buffer = Buffer.create 1024 in
            let rec plist = function
              | ADTValue (cn_nil, _, []) when Datatypes.is_nil_ctr_name cn_nil
                ->
                  Buffer.add_string list_buffer "(Nil)"
              | ADTValue (cn_cons, _, [ head; tail ])
                when Datatypes.is_cons_ctr_name cn_cons ->
                  let head_str = pp_literal head ^ ", " in
                  Buffer.add_string list_buffer head_str;
                  plist tail
              | _ ->
                  Buffer.clear list_buffer;
                  Buffer.add_string list_buffer "(Malformed List)"
            in
            plist l;
            "(List " ^ Buffer.contents list_buffer ^ ")"
        | _ when Datatypes.is_zero_ctr_name cn || Datatypes.is_succ_ctr_name cn
          ->
            let rec counter nat acc =
              match nat with
              | ADTValue (cn_zero, _, [])
                when Datatypes.is_zero_ctr_name cn_zero ->
                  Some acc
              | ADTValue (cn_succ, _, [ pred ])
                when Datatypes.is_succ_ctr_name cn_succ ->
                  counter pred (Uint32.succ acc)
              | _ -> None
            in
            let res = Option.map (counter l Uint32.zero) ~f:Uint32.to_string in
            "(Nat " ^ Option.value res ~default:"(Malformed Nat)" ^ ")"
        | _ ->
            (* Generic printing for other ADTs. *)
            "(" ^ Name.as_error_string cn
            ^ List.fold_left al ~init:"" ~f:(fun a l' ->
                  a ^ " " ^ pp_literal l')
            ^ ")")

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
          | MatchStmt (obj, clauses, jopt) ->
              let cs' =
                List.map clauses ~f:(fun (p, stmts) ->
                    let bound_vars = get_spattern_bounds p in
                    (* If a new bound is created for "fromv", don't recurse. *)
                    if Identifier.is_mem_id fromv bound_vars then (p, stmts)
                    else (p, recurser stmts))
              in
              let jopt' =
                match jopt with
                | Some (lbl, jsts) -> Some (lbl, recurser jsts)
                | None -> jopt
              in
              (MatchStmt (switcher obj, cs', jopt'), srep) :: recurser remstmts
          | JumpStmt i -> (JumpStmt (switcher i), srep) :: recurser remstmts
          | GasStmt g ->
              let f str =
                Identifier.get_id (switcher (Identifier.mk_id str srep))
              in
              let g' = replace_variable_name ~f g in
              (GasStmt g', srep) :: recurser remstmts)
    in
    recurser stmts

  let pp_bcinfo_query = Fn.compose Sexp.to_string sexp_of_bcinfo_query

  (* Pretty much a clone from Datatypes.ml *)
  module Datatypes = struct
    module DTName = Identifier.Name

    (* A tagged constructor *)
    type constructor = Scilla_base.Datatypes.constructor

    (* An Algebraic Data Type *)
    type adt = {
      tname : DTName.t;
      (* type name *)
      tparams : eannot Identifier.t list;
      (* type parameters *)
      (* supported constructors *)
      tconstr : constructor list;
      (* Mapping for constructors' types
         The arity of the constructor is the same as the length
         of the list, so the types are mapped correspondingly. *)
      tmap : (DTName.t * typ list) list;
    }

    module DataTypeDictionary = struct
      (* adt.tname -> adt *)
      let adt_name_dict = Caml.Hashtbl.create 5

      (* tconstr -> (adt * constructor) *)
      let adt_cons_dict = Caml.Hashtbl.create 10

      let reset () =
        Caml.Hashtbl.reset adt_name_dict;
        Caml.Hashtbl.reset adt_cons_dict

      let add_adt (new_adt : adt) =
        let open Caml in
        match Hashtbl.find_opt adt_name_dict new_adt.tname with
        | Some _ ->
            fail0 ~kind:"Multiple declarations of type"
              ~inst:(DTName.as_error_string new_adt.tname)
        | None ->
            let _ = Hashtbl.add adt_name_dict new_adt.tname new_adt in
            foldM new_adt.tconstr ~init:() ~f:(fun () (ctr : constructor) ->
                match Hashtbl.find_opt adt_cons_dict ctr.cname with
                | Some _ ->
                    fail0
                      ~kind:
                        (sprintf "Multiple declarations of type constructor %s"
                           (DTName.as_error_string ctr.cname))
                      ?inst:None
                | None ->
                    pure @@ Hashtbl.add adt_cons_dict ctr.cname (new_adt, ctr))

      (*  Get ADT by name *)
      let lookup_name ?(sloc = ErrorUtils.dummy_loc) name =
        let open Caml in
        match Hashtbl.find_opt adt_name_dict name with
        | None ->
            fail1 ~kind:"ADT not found" ~inst:(DTName.as_error_string name) sloc
        | Some a -> pure a

      (*  Get ADT by the constructor *)
      let lookup_constructor ?(sloc = ErrorUtils.dummy_loc) cn =
        let open Caml in
        match Hashtbl.find_opt adt_cons_dict cn with
        | None ->
            fail1 ~kind:"No data type found for constructor"
              ~inst:(DTName.as_error_string cn)
              sloc
        | Some dt -> pure dt

      (* Get typing map for a constructor *)
      let constr_tmap adt cn =
        List.find adt.tmap ~f:(fun (n, _) -> DTName.equal n cn)
        |> Option.map ~f:snd
    end

    (* End of DataTypeDictionary *)
  end

  (* End of Datatypes *)

  (* Pretty much a clone of functions in Syntax, TypeUtilities. *)
  module TypeUtilities = struct
    module PrimTypes = struct
      let int32_typ = PrimType (Int_typ Bits32)
      let int64_typ = PrimType (Int_typ Bits64)
      let int128_typ = PrimType (Int_typ Bits128)
      let int256_typ = PrimType (Int_typ Bits256)
      let uint32_typ = PrimType (Uint_typ Bits32)
      let uint64_typ = PrimType (Uint_typ Bits64)
      let uint128_typ = PrimType (Uint_typ Bits128)
      let uint256_typ = PrimType (Uint_typ Bits256)
      let string_typ = PrimType String_typ
      let bnum_typ = PrimType Bnum_typ
      let msg_typ = PrimType Msg_typ
      let event_typ = PrimType Event_typ
      let exception_typ = PrimType Exception_typ
      let bystr_typ = PrimType Bystr_typ
      let bystrx_typ b = PrimType (Bystrx_typ b)
    end

    (* ENd of PrimTypes *)

    open Datatypes

    (* Return free tvars in tp
       The return list doesn't contain duplicates *)
    let free_tvars tp =
      let add vs tv = tv :: List.filter ~f:(Fn.non (Identifier.equal tv)) vs in
      let rem vs tv = List.filter ~f:(Fn.non (Identifier.equal tv)) vs in
      let rec go t acc =
        match t with
        | PrimType _ | Unit -> acc
        | MapType (kt, vt) -> go kt acc |> go vt
        | FunType (at, rt) ->
            let acc' = List.fold_left at ~init:acc ~f:(Fn.flip go) in
            go rt acc'
        | TypeVar n -> add acc n
        | ADT (_, ts) -> List.fold_left ts ~init:acc ~f:(Fn.flip go)
        | PolyFun (arg, bt) ->
            let acc' = go bt acc in
            rem acc' arg
        | Address AnyAddr | Address CodeAddr | Address LibAddr -> acc
        | Address (ContrAddr fts) ->
            IdLoc_Comp.Map.fold fts ~init:acc ~f:(fun ~key:_ ~data acc ->
                go data acc)
      in
      go tp []

    let mk_fresh_var taken init =
      let tmp = ref init in
      let counter = ref 1 in
      while List.mem taken !tmp ~equal:Identifier.equal do
        tmp := mk_noannot_id (Identifier.as_string init ^ Int.to_string !counter);
        Int.incr counter
      done;
      !tmp

    (* tm[tvar := tp] *)
    let rec subst_type_in_type tvar tp tm =
      match tm with
      | PrimType _ | Unit -> tm
      (* Make sure the map's type is still primitive! *)
      | MapType (kt, vt) ->
          let kts = subst_type_in_type tvar tp kt in
          let vts = subst_type_in_type tvar tp vt in
          MapType (kts, vts)
      | FunType (at, rt) ->
          let at' = List.map at ~f:(subst_type_in_type tvar tp) in
          let rts = subst_type_in_type tvar tp rt in
          FunType (at', rts)
      | TypeVar n -> if Identifier.(equal tvar n) then tp else tm
      | ADT (s, ts) ->
          let ts' = List.map ts ~f:(subst_type_in_type tvar tp) in
          ADT (s, ts')
      | PolyFun (arg, t) ->
          if Identifier.(equal tvar arg) then tm
          else PolyFun (arg, subst_type_in_type tvar tp t)
      | Address AnyAddr | Address CodeAddr | Address LibAddr -> tm
      | Address (ContrAddr fts) ->
          Address
            (ContrAddr (IdLoc_Comp.Map.map fts ~f:(subst_type_in_type tvar tp)))

    (* note: this is sequential substitution of multiple variables,
              _not_ simultaneous substitution *)
    let subst_types_in_type sbst tm =
      List.fold_left sbst ~init:tm ~f:(fun acc (tvar, tp) ->
          subst_type_in_type tvar tp acc)

    let rec subst_type_in_literal tvar tp l =
      match l with
      | Map ((kt, vt), ls) ->
          let open Caml in
          let kts = subst_type_in_type tvar tp kt in
          let vts = subst_type_in_type tvar tp vt in
          let ls' = Hashtbl.create (Hashtbl.length ls) in
          let _ =
            Hashtbl.iter
              (fun k v ->
                let k' = subst_type_in_literal tvar tp k in
                let v' = subst_type_in_literal tvar tp v in
                Hashtbl.add ls' k' v')
              ls
          in
          Map ((kts, vts), ls')
      | ADTValue (n, ts, ls) ->
          let ts' = List.map ts ~f:(subst_type_in_type tvar tp) in
          let ls' = List.map ls ~f:(subst_type_in_literal tvar tp) in
          ADTValue (n, ts', ls')
      | _ -> l

    let rec subst_type_in_expr tvar tp (e, rep') =
      (* Function to substitute in a rep. *)
      let subst_rep r =
        let t' = Option.map r.ea_tp ~f:(subst_type_in_type tvar tp) in
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
      | Literal l -> (Literal (subst_type_in_literal tvar tp l), rep)
      | Var i -> (Var (subst_id i), rep)
      | Fun (args, body) ->
          let args_subst =
            List.map args ~f:(fun (f, t) ->
                (subst_id f, subst_type_in_type tvar tp t))
          in
          let body_subst = subst_type_in_expr tvar tp body in
          (Fun (args_subst, body_subst), rep)
      | TFun (tv, body) as tf ->
          if Identifier.equal tv tvar then (tf, rep)
          else
            let body_subst = subst_type_in_expr tvar tp body in
            (TFun (tv, body_subst), rep)
      | Constr (n, ts, es) ->
          let ts' = List.map ts ~f:(fun t -> subst_type_in_type tvar tp t) in
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
            Option.map tann ~f:(fun t -> subst_type_in_type tvar tp t)
          in
          let lhs' = subst_type_in_expr tvar tp lhs in
          let rhs' = subst_type_in_expr tvar tp rhs in
          (Let (subst_id i, tann', lhs', rhs'), rep)
      | Message splist ->
          let m' =
            List.map splist ~f:(fun (s, p) ->
                let p' =
                  match p with
                  | MLit l -> MLit (subst_type_in_literal tvar tp l)
                  | MVar v -> MVar (subst_id v)
                in
                (s, p'))
          in
          (Message m', rep)
      | JumpExpr l -> (JumpExpr (subst_id l), rep)
      | MatchExpr (e, cs, join_clause_opt) ->
          let subst_spattern_base = function
            | Wildcard -> Wildcard
            | Binder v -> Binder (subst_id v)
          in
          let subst_pattern = function
            | Any a -> Any (subst_spattern_base a)
            | Constructor (s, pl) ->
                Constructor (s, List.map pl ~f:subst_spattern_base)
          in
          let cs' =
            List.map cs ~f:(fun (p, b) ->
                (subst_pattern p, subst_type_in_expr tvar tp b))
          in
          let join_clause_opt' =
            match join_clause_opt with
            | Some (l, b) -> Some (subst_id l, subst_type_in_expr tvar tp b)
            | None -> None
          in
          (MatchExpr (subst_id e, cs', join_clause_opt'), rep)
      | TApp (tf, tl) ->
          let tl' = List.map tl ~f:(fun t -> subst_type_in_type tvar tp t) in
          (TApp (subst_id tf, tl'), rep)
      | Fixpoint (f, t, body) ->
          let t' = subst_type_in_type tvar tp t in
          let body' = subst_type_in_expr tvar tp body in
          (Fixpoint (subst_id f, t', body'), rep)
      | GasExpr (g, e) -> (GasExpr (g, subst_type_in_expr tvar tp e), rep)

    let rename_bound_vars mk_new_name update_taken =
      let rec recursor t taken =
        match t with
        | MapType (kt, vt) -> MapType (kt, recursor vt taken)
        | FunType (at, rt) ->
            let at' = List.map at ~f:(fun w -> recursor w taken) in
            FunType (at', recursor rt taken)
        | ADT (n, ts) ->
            let ts' = List.map ts ~f:(fun w -> recursor w taken) in
            ADT (n, ts')
        | PrimType _ | TypeVar _ | Unit -> t
        | PolyFun (arg, bt) ->
            let arg' = mk_new_name taken arg in
            let tv_new = TypeVar arg' in
            let bt1 = subst_type_in_type arg tv_new bt in
            let bt2 = recursor bt1 (update_taken arg' taken) in
            PolyFun (arg', bt2)
        | Address AnyAddr | Address CodeAddr | Address LibAddr -> t
        | Address (ContrAddr fts) ->
            Address
              (ContrAddr (IdLoc_Comp.Map.map fts ~f:(fun t -> recursor t taken)))
      in
      recursor

    let refresh_tfun = rename_bound_vars mk_fresh_var List.cons

    let canonicalize_tfun t =
      (* The parser doesn't allow type names to begin with '_'. *)
      let mk_new_name counter _ =
        mk_noannot_id ("'_A" ^ Int.to_string counter)
      in
      rename_bound_vars mk_new_name (const @@ Int.succ) t 1

    let rec subst_type_in_literal tvar tp l =
      match l with
      | Map ((kt, vt), ls) ->
          let kts = subst_type_in_type tvar tp kt in
          let vts = subst_type_in_type tvar tp vt in
          let ls' = Caml.Hashtbl.create (Caml.Hashtbl.length ls) in
          let _ =
            Caml.Hashtbl.iter
              (fun k v ->
                let k' = subst_type_in_literal tvar tp k in
                let v' = subst_type_in_literal tvar tp v in
                Caml.Hashtbl.add ls' k' v')
              ls
          in
          Map ((kts, vts), ls')
      | ADTValue (n, ts, ls) ->
          let ts' = List.map ts ~f:(subst_type_in_type tvar tp) in
          let ls' = List.map ls ~f:(subst_type_in_literal tvar tp) in
          ADTValue (n, ts', ls')
      | _ -> l

    let int_width = function
      | PrimType (Int_typ bits) | PrimType (Uint_typ bits) ->
          Some (PrimType.int_bit_width_to_int bits)
      | _ -> None

    (* Given a ByStrX string, return integer X *)
    let bystrx_width = function PrimType (Bystrx_typ w) -> Some w | _ -> None
    let is_prim_type = function PrimType _ -> true | _ -> false
    let is_address_type = function Address _ -> true | _ -> false
    let is_string_type = function PrimType String_typ -> true | _ -> false
    let is_int_type = function PrimType (Int_typ _) -> true | _ -> false
    let is_uint_type = function PrimType (Uint_typ _) -> true | _ -> false
    let is_bystrx_type = function PrimType (Bystrx_typ _) -> true | _ -> false

    (* Type equivalence *)
    let equal_typ t1 t2 =
      let t1' = canonicalize_tfun t1 in
      let t2' = canonicalize_tfun t2 in
      let rec equiv t1 t2 =
        match (t1, t2) with
        | PrimType p1, PrimType p2 -> [%equal: PrimType.t] p1 p2
        | TypeVar v1, TypeVar v2 -> Identifier.equal v1 v2
        | Unit, Unit -> true
        | ADT (tname1, tl1), ADT (tname2, tl2) ->
            Identifier.equal tname1 tname2
            (* Cannot call type_equiv_list because we don't want to canonicalize_tfun again. *)
            && List.length tl1 = List.length tl2
            && List.for_all2_exn ~f:equiv tl1 tl2
        | MapType (kt1, vt1), MapType (kt2, vt2) ->
            equiv kt1 kt2 && equiv vt1 vt2
        | FunType (argts1, bodyt1), FunType (argts2, bodyt2) ->
            equiv bodyt1 bodyt2
            (* Cannot call type_equiv_list because we don't want to canonicalize_tfun again. *)
            && List.length argts1 = List.length argts2
            && List.for_all2_exn ~f:equiv argts1 argts2
        | Address AnyAddr, Address AnyAddr
        | Address CodeAddr, Address CodeAddr
        | Address LibAddr, Address LibAddr ->
            true
        | Address (ContrAddr fts1), Address (ContrAddr fts2) ->
            IdLoc_Comp.Map.equal equiv fts1 fts2
        | _ -> false
      in
      equiv t1' t2'

    (* Type comparator *)
    let compare t1 t2 =
      let t1' = canonicalize_tfun t1 in
      let t2' = canonicalize_tfun t2 in
      let ttag = function
        | PrimType _ -> 0
        | MapType _ -> 1
        | FunType _ -> 2
        | ADT _ -> 3
        | TypeVar _ -> 4
        | PolyFun _ -> 5
        | Unit -> 6
        | Address (ContrAddr _) -> 7
        | Address AnyAddr -> 8
        | Address CodeAddr -> 9
        | Address LibAddr -> 10
      in
      let rec comp t1 t2 =
        match (t1, t2) with
        | PrimType p1, PrimType p2 -> PrimType.compare p1 p2
        | TypeVar v1, TypeVar v2 -> Identifier.compare v1 v2
        | ADT (tname1, tl1), ADT (tname2, tl2) ->
            let tc = Identifier.compare tname1 tname2 in
            if tc <> 0 then tc
            else
              let lc = Int.compare (List.length tl1) (List.length tl2) in
              if lc <> 0 then lc else List.compare comp tl1 tl2
        | MapType (kt1, vt1), MapType (kt2, vt2) ->
            let kc = comp kt1 kt2 in
            if kc <> 0 then kc else comp vt1 vt2
        | FunType (argts1, bodyt1), FunType (argts2, bodyt2) ->
            let lc = List.compare comp argts1 argts2 in
            if lc <> 0 then lc else comp bodyt1 bodyt2
        | PolyFun (v1, t1''), PolyFun (v2, t2'') ->
            let sc = Identifier.compare v1 v2 in
            if sc <> 0 then sc else comp t1'' t2''
        | Address (ContrAddr tl1), Address (ContrAddr tl2) ->
            IdLoc_Comp.Map.compare comp tl1 tl2
        | t1', t2' -> Int.compare (ttag t1') (ttag t2')
      in
      comp t1' t2'

    let type_assignable ~expected ~actual =
      let to_typ' = canonicalize_tfun expected in
      let from_typ' = canonicalize_tfun actual in
      let rec assignable to_typ from_typ =
        match (to_typ, from_typ) with
        | Address AnyAddr, Address _ ->
            (* Any address is assignable to an address in use *)
            true
        | Address LibAddr, Address LibAddr -> true
        | Address CodeAddr, Address CodeAddr
        | Address CodeAddr, Address LibAddr
        | Address CodeAddr, Address (ContrAddr _) ->
            (* Any address containing code, library or contract is a code address. *)
            true
        | Address (ContrAddr tfts), Address (ContrAddr ffts) ->
            (* Check that tfts is a subset of ffts, and that types are assignable/equivalent. *)
            IdLoc_Comp.Map.for_alli tfts ~f:(fun ~key:tf ~data:tft ->
                match IdLoc_Comp.Map.find ffts tf with
                | None ->
                    (* to field does not appear in from type *)
                    false
                | Some fft ->
                    (* Matching field name. Types must be assignable. *)
                    assignable tft fft)
        | PrimType (Bystrx_typ len), Address _
          when len = Scilla_base.Type.address_length ->
            (* Any address is assignable to ByStr20. *)
            true
        | MapType (kt1, vt1), MapType (kt2, vt2) ->
            assignable kt1 kt2 && assignable vt1 vt2
        | FunType (at1, vt1), FunType (at2, vt2) ->
            (* Contravariant in argument type! *)
            List.length at1 = List.length at2
            && List.for_all2_exn at2 at1 ~f:assignable
            && assignable vt1 vt2
        | ADT (n1, tlist1), ADT (n2, tlist2) -> (
            Identifier.equal n1 n2
            &&
            (* We can assume that type parameters only occur in covariant positions *)
            match List.for_all2 tlist1 tlist2 ~f:assignable with
            | Ok res -> res
            | Unequal_lengths -> false)
        | PolyFun (targ1, vt1), PolyFun (targ2, vt2) ->
            equal_typ (TypeVar targ1) (TypeVar targ2) && assignable vt1 vt2
        | _, _ ->
            (* PrimType, Unit and TypeVar require equality up to canonicalisation. *)
            equal_typ to_typ from_typ
      in
      assignable to_typ' from_typ'

    (* Return True if corresponding elements are `type_equiv`,
       False otherwise, or if unequal lengths. *)
    let type_equiv_list tlist1 tlist2 =
      List.length tlist1 = List.length tlist2
      && not
           (List.exists2_exn tlist1 tlist2 ~f:(fun t1 t2 ->
                not ([%equal: typ] t1 t2)))

    let rec is_ground_type t =
      match t with
      | FunType (a, r) -> List.for_all a ~f:is_ground_type && is_ground_type r
      | MapType (k, v) -> is_ground_type k && is_ground_type v
      | ADT (_, ts) -> List.for_all ~f:(fun t -> is_ground_type t) ts
      | PolyFun _ | TypeVar _ -> false
      | _ -> true

    (* Are all type variables bound. *)
    let is_closed_type t =
      let rec go bounds = function
        | FunType (a, r) -> List.for_all a ~f:(go bounds) && go bounds r
        | MapType (k, v) -> go bounds k && go bounds v
        | ADT (_, ts) -> List.for_all ~f:(go bounds) ts
        | PolyFun (tv, subt) -> go (tv :: bounds) subt
        | TypeVar v -> Identifier.is_mem_id v bounds
        | PrimType _ | Unit -> true
        | Address AnyAddr | Address CodeAddr | Address LibAddr -> true
        | Address (ContrAddr tl) -> IdLoc_Comp.Map.for_all tl ~f:(go bounds)
      in
      go [] t

    let rec is_non_map_ground_type t =
      match t with
      | FunType (a, r) ->
          List.for_all a ~f:is_non_map_ground_type && is_non_map_ground_type r
      | MapType (_, _) -> false
      | ADT (_, ts) -> List.for_all ~f:(fun t -> is_non_map_ground_type t) ts
      | PolyFun _ | TypeVar _ -> false
      | _ -> true

    let rec is_serializable_storable_helper accept_maps allow_unserializable
        check_addresses t seen_adts =
      let rec recurser t seen_adts =
        match t with
        | FunType (a, r) ->
            allow_unserializable
            && List.for_all a ~f:(fun ael -> recurser ael seen_adts)
            && recurser r seen_adts
        | PolyFun (_, t) -> allow_unserializable && recurser t seen_adts
        | Unit -> allow_unserializable
        | MapType (kt, vt) ->
            accept_maps && recurser kt seen_adts && recurser vt seen_adts
        | TypeVar _ ->
            (* If we are inside an ADT, then type variable
               instantiations are handled outside *)
            not @@ List.is_empty seen_adts
        | PrimType _ ->
            (* Messages and Events are not serialisable in terms of contract parameters *)
            allow_unserializable
            || (not @@ [%equal: typ] t (PrimType Msg_typ))
            || [%equal: typ] t (PrimType Event_typ)
        | ADT (tname, ts) -> (
            let open DataTypeDictionary in
            if List.mem seen_adts tname ~equal:Identifier.equal then true
              (* Inductive ADT - ignore this branch *)
            else
              (* Check that ADT is serializable *)
              match
                lookup_name ~sloc:(Identifier.get_rep tname)
                  (Identifier.get_id tname)
              with
              | Error _ -> false (* Handle errors outside *)
              | Ok adt ->
                  let adt_serializable =
                    List.for_all adt.tmap ~f:(fun (_, carg_list) ->
                        List.for_all carg_list ~f:(fun carg ->
                            recurser carg (tname :: seen_adts)))
                  in
                  adt_serializable
                  && List.for_all ts ~f:(fun t -> recurser t seen_adts))
        | Address (ContrAddr fts) when check_addresses ->
            (* If check_addresses is true, then all field types in the address type should be legal field types.
               No need to check for serialisability or storability, since addresses are stored and passed as ByStr20. *)
            IdLoc_Comp.Map.for_all fts ~f:is_legal_field_type
        | Address _ -> true
      in
      recurser t seen_adts

    and is_legal_message_field_type t =
      (* Maps are not allowed. Address values are considered ByStr20 when used as message field value. *)
      is_serializable_storable_helper false false false t []

    and is_legal_transition_parameter_type t =
      (* Maps are not allowed. Address values should be checked for storable field types. *)
      is_serializable_storable_helper false false true t []

    and is_legal_procedure_parameter_type t =
      (* Like transition parametes, except that polymorphic parameters are allowed,
         since parameters do not need to be serializable. *)
      is_serializable_storable_helper false true true t []

    and is_legal_contract_parameter_type t =
      (* Like fields. Maps are allowed. Address values should be checked for storable field types. *)
      is_serializable_storable_helper true false true t []

    and is_legal_field_type t =
      (* Maps are allowed. Address values should be checked for storable field types. *)
      is_serializable_storable_helper true false true t []

    let is_legal_map_key_type t = is_prim_type t || is_address_type t

    let get_msgevnt_type m =
      let open ContractUtil.MessagePayload in
      if List.exists ~f:(fun (s, _, _) -> String.(s = tag_label)) m then
        pure PrimTypes.msg_typ
      else if List.exists ~f:(fun (s, _, _) -> String.(s = eventname_label)) m
      then pure PrimTypes.event_typ
      else if List.exists ~f:(fun (s, _, _) -> String.(s = exception_label)) m
      then pure PrimTypes.exception_typ
      else
        fail0
          ~kind:
            "Invalid message construct. Not any of send, event or exception."
          ?inst:None

    let literal_type l =
      let open PrimTypes in
      match l with
      | IntLit (Int32L _) -> pure int32_typ
      | IntLit (Int64L _) -> pure int64_typ
      | IntLit (Int128L _) -> pure int128_typ
      | IntLit (Int256L _) -> pure int256_typ
      | UintLit (Uint32L _) -> pure uint32_typ
      | UintLit (Uint64L _) -> pure uint64_typ
      | UintLit (Uint128L _) -> pure uint128_typ
      | UintLit (Uint256L _) -> pure uint256_typ
      | StringLit _ -> pure string_typ
      | BNum _ -> pure bnum_typ
      | ByStr _ -> pure bystr_typ
      | ByStrX bs -> pure (bystrx_typ (Literal.Bystrx.width bs))
      (* Check that messages and events have storable parameters. *)
      | Msg bs -> get_msgevnt_type bs
      | Map ((kt, vt), _) -> pure (MapType (kt, vt))
      | ADTValue (cname, ts, _) ->
          let%bind adt, _ = DataTypeDictionary.lookup_constructor cname in
          pure @@ ADT (Identifier.mk_loc_id adt.tname, ts)

    let apply_type_subst tmap tp =
      List.fold_left tmap ~init:tp ~f:(fun acc_tp (tv, tp) ->
          subst_type_in_type tv tp acc_tp)

    let validate_param_length cn plen alen =
      if plen <> alen then
        fail0 ~kind:"Incorrect number of arguments to constructor"
          ~inst:
            (sprintf "Constructor %s expects %d but got %d"
               (DTName.as_error_string cn)
               plen alen)
      else pure ()

    (* Avoid variable clashes *)
    let refresh_adt adt taken =
      let { tparams; tmap; _ } = adt in
      let tkn = tparams @ taken in
      let subst = List.map tparams ~f:(fun tp -> (tp, mk_fresh_var tkn tp)) in
      let tparams' = List.unzip subst |> snd in
      let subst =
        List.zip_exn tparams @@ List.map tparams' ~f:(fun s -> TypeVar s)
      in
      let tmap' =
        List.map tmap ~f:(fun (cn, tls) ->
            let tls' = List.map tls ~f:(subst_types_in_type subst) in
            (cn, tls'))
      in
      { adt with tparams = tparams'; tmap = tmap' }

    let extract_targs cn (adt : adt) atyp =
      match atyp with
      | ADT (name, targs) ->
          if DTName.equal adt.tname (Identifier.get_id name) then
            let plen = List.length adt.tparams in
            let alen = List.length targs in
            let%bind _ = validate_param_length cn plen alen in
            pure targs
          else
            fail1 ~kind:"Types mismatch"
              ~inst:
                (sprintf
                   "pattern uses a constructor of type %s, but value of type \
                    %s is given."
                   (DTName.as_error_string adt.tname)
                   (Identifier.as_string name))
              (Identifier.get_rep name)
      | _ -> fail0 ~kind:"Not an algebraic data type" ~inst:(pp_typ atyp)

    let constr_pattern_arg_types atyp cn =
      let open DataTypeDictionary in
      let%bind adt', _ = lookup_constructor cn in
      let taken = free_tvars atyp in
      let adt = refresh_adt adt' taken in
      let%bind targs = extract_targs cn adt atyp in
      match constr_tmap adt cn with
      | None -> pure []
      | Some tms ->
          let subst = List.zip_exn adt.tparams targs in
          pure @@ List.map ~f:(apply_type_subst subst) tms

    (* Replace address types with ByStr20 *)
    let rec erase_address_in_type (t : typ) =
      match t with
      | PrimType _ | TypeVar _ | PolyFun _ | Unit -> t
      | Address _ -> PrimTypes.bystrx_typ Scilla_base.Type.address_length
      | MapType (kt, vt) ->
          MapType (erase_address_in_type kt, erase_address_in_type vt)
      | FunType (argts, t2) ->
          FunType
            (List.map argts ~f:erase_address_in_type, erase_address_in_type t2)
      | ADT (tname, targs) ->
          ADT (tname, List.map targs ~f:erase_address_in_type)
  end

  (* End of TypeUtilities *)
end

let prepend_implicit_tparams (comp : Uncurried_Syntax.component) =
  let open Uncurried_Syntax in
  let amount_typ = PrimType (Uint_typ Bits128) in
  let address_typ = Address AnyAddr in
  let comp_loc = (Identifier.get_rep comp.comp_name).ea_loc in
  ( Identifier.mk_id
      (Identifier.Name.parse_simple_name
         ContractUtil.MessagePayload.amount_label)
      { ea_tp = Some amount_typ; ea_loc = comp_loc; ea_auxi = None },
    amount_typ )
  :: ( Identifier.mk_id
         (Identifier.Name.parse_simple_name
            ContractUtil.MessagePayload.origin_label)
         { ea_tp = Some address_typ; ea_loc = comp_loc; ea_auxi = None },
       address_typ )
  :: ( Identifier.mk_id
         (Identifier.Name.parse_simple_name
            ContractUtil.MessagePayload.sender_label)
         { ea_tp = Some address_typ; ea_loc = comp_loc; ea_auxi = None },
       address_typ )
  :: comp.comp_params

let prepend_implicit_cparams (contr : Uncurried_Syntax.contract) =
  let open Uncurried_Syntax in
  let open TypeUtilities.PrimTypes in
  let comp_loc = (Identifier.get_rep contr.cname).ea_loc in
  ( Identifier.mk_id ContractUtil.scilla_version_label
      { ea_tp = Some uint32_typ; ea_loc = comp_loc; ea_auxi = None },
    uint32_typ )
  :: ( Identifier.mk_id ContractUtil.this_address_label
         {
           ea_tp = Some (bystrx_typ Scilla_base.Type.address_length);
           ea_loc = comp_loc;
           ea_auxi = None;
         },
       bystrx_typ Scilla_base.Type.address_length )
  :: ( Identifier.mk_id ContractUtil.creation_block_label
         { ea_tp = Some bnum_typ; ea_loc = comp_loc; ea_auxi = None },
       bnum_typ )
  :: contr.cparams

(* End of Uncurried_Syntax *)
