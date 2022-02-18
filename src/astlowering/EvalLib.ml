(*
  This file is part of scilla.

  Copyright (c) 2021 - present Zilliqa Research Pvt. Ltd.
  
  scilla is free software: you can redistribute it and/or modify it under the
  terms of the GNU General Public License as published by the Free Software
  Foundation, either version 3 of the License, or (at your option) any later
  version.
 
  scilla is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
  A PARTICULAR PURPOSE.  See the GNU General Public License for more details.
 
  You should have received a copy of the GNU General Public License along with
*)

(* Evaluate library entries to the extent possible, so that we have less to
 * do during an actual execution. Returns evaluated library with entries
 * replaced by their evaluated literal. 
 *)

open Scilla_base
open Core_kernel
open Syntax
open TypeUtil
module Literal = Literal.GlobalLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open MonadUtil
open Core.Result.Let_syntax
open ExplicitAnnotationSyntax
module GC = GasCharge.ScillaGasCharge (Identifier.Name)
open Scilla_eval
open ErrorUtils
open EvalUtil
open EvalIdentifier
open EvalLiteral
open EvalTypeUtilities

module ScillaCG_EvalLib
    (SR : Rep) (ER : sig
      include Rep

      val get_type : rep -> PlainTypes.t inferred_type

      val mk_rep : loc -> PlainTypes.t inferred_type -> rep
    end) =
struct
  module TU = TypeUtilities
  module TypedSyntax = ScillaSyntax (SR) (ER) (Literal)
  module SGas = Gas.ScillaGas (SR) (ER)
  module EAS = EASyntax
  open TypedSyntax

  type libeval_literal =
    | StringLit of string
    (* Cannot have different integer literals here directly as Stdint does not derive sexp. *)
    | IntLit of int_lit
    | UintLit of uint_lit
    | BNum of Scilla_base.Literal.BNumLit.t
    (* Byte string with a statically known length. *)
    | ByStrX of Bystrx.t
    (* Byte string without a statically known length. *)
    | ByStr of Bystr.t
    (* Message: an associative array *)
    | Msg of (string * LType.t * libeval_literal) list
    (* A dynamic map of literals *)
    | Map of mtype * (libeval_literal, libeval_literal) Caml.Hashtbl.t
    (* A constructor in HNF *)
    | ADTValue of LType.TIdentifier.Name.t * LType.t list * libeval_literal list
    (* An embedded closure *)
    | Clo of (expr_annot * libeval_env)
    (* A type abstraction *)
    | TAbs of (expr_annot * libeval_env)

  and libeval_env = (Name.t * libeval_literal) list

  let rec literal_eq l1 l2 =
    let open TULiteral in
    let open Stdint in
    let open Scilla_base.Literal in
    match (l1, l2) with
    | IntLit (Int32L i1), IntLit (Int32L i2) -> Int32.compare i1 i2 = 0
    | IntLit (Int64L i1), IntLit (Int64L i2) -> Int64.compare i1 i2 = 0
    | IntLit (Int128L i1), IntLit (Int128L i2) -> Int128.compare i1 i2 = 0
    | IntLit (Int256L i1), IntLit (Int256L i2) ->
        Integer256.Int256.compare i1 i2 = 0
    | UintLit (Uint32L i1), UintLit (Uint32L i2) -> Uint32.compare i1 i2 = 0
    | UintLit (Uint64L i1), UintLit (Uint64L i2) -> Uint64.compare i1 i2 = 0
    | UintLit (Uint128L i1), UintLit (Uint128L i2) -> Uint128.compare i1 i2 = 0
    | UintLit (Uint256L i1), UintLit (Uint256L i2) ->
        Integer256.Uint256.compare i1 i2 = 0
    | StringLit s1, StringLit s2 -> String.equal s1 s2
    | BNum b1, BNum b2 -> String.equal (BNumLit.get b1) (BNumLit.get b2)
    | ByStr b1, ByStr b2 -> Bystr.equal b1 b2
    | ByStrX b1, ByStrX b2 -> Bystrx.equal b1 b2
    | Msg b1, Msg b2 ->
        List.equal
          (fun (n1, t1, l1) (n2, t2, l2) ->
            String.equal n1 n2 && SType.equal t1 t2 && literal_eq l1 l2)
          b1 b2
    | Map ((kt1, vt1), m1), Map ((kt2, vt2), m2) ->
        SType.equal kt1 kt2 && SType.equal vt1 vt2
        && Caml.Hashtbl.length m1 = Caml.Hashtbl.length m2
        && Caml.Hashtbl.fold
             (fun k1 v1 res ->
               match Caml.Hashtbl.find_opt m2 k1 with
               | Some v2 -> res && literal_eq v1 v2
               | None -> false)
             m1 true
    | ADTValue (cname1, ts1, args1), ADTValue (cname2, ts2, args2) ->
        Name.equal cname1 cname2
        && List.equal SType.equal ts1 ts2
        && List.equal literal_eq args1 args2
    | Clo _, Clo _ | TAbs _, TAbs _ ->
        (* We don't know how to deal with these. *)
        false
    | _ -> false

  let rec expr_eq e1 e2 =
    match (e1, e2) with
    | Literal l1, Literal l2 -> literal_eq l1 l2
    | Var i1, Var i2 -> SIdentifier.equal i1 i2
    | ( Let (i1, topt1, (lhs1, _), (rhs1, _)),
        Let (i2, topt2, (lhs2, _), (rhs2, _)) ) ->
        SIdentifier.equal i1 i2
        && Option.equal SType.equal topt1 topt2
        && expr_eq lhs1 lhs2 && expr_eq rhs1 rhs2
    | Message bs1, Message bs2 ->
        List.equal
          (fun (n1, pl1) (n2, pl2) ->
            String.equal n1 n2
            &&
            match (pl1, pl2) with
            | MLit l1, MLit l2 -> literal_eq l1 l2
            | MVar v1, MVar v2 -> SIdentifier.equal v1 v2
            | _ -> false)
          bs1 bs2
    | App (f1, actuals1), App (f2, actuals2) ->
        equal f1 f2
        && List.equal (fun i1 i2 -> SIdentifier.equal i1 i2) actuals1 actuals2
    | Constr (cname1, ts1, actuals1), Constr (cname2, ts2, actuals2) ->
        SIdentifier.equal cname1 cname2
        && List.equal SType.equal ts1 ts2
        && List.equal SIdentifier.equal actuals1 actuals2
    | MatchExpr (x1, clauses1), MatchExpr (x2, clauses2) ->
        SIdentifier.equal x1 x2
        && List.equal
             (fun (pat1, (sube1, _)) (pat2, (sube2, _)) ->
               let rec pattern_eq pat1 pat2 =
                 match (pat1, pat2) with
                 | Wildcard, Wildcard -> true
                 | Binder b1, Binder b2 -> SIdentifier.equal b1 b2
                 | Constructor (c1, pl1), Constructor (c2, pl2) ->
                     SIdentifier.equal c1 c2 && List.equal pattern_eq pl1 pl2
                 | _ -> false
               in
               pattern_eq pat1 pat2 && expr_eq sube1 sube2)
             clauses1 clauses2
    | Builtin ((b1, _), targs1, actuals1), Builtin ((b2, _), targs2, actuals2)
      ->
        Poly.equal b1 b2
        && List.equal SType.equal targs1 targs2
        && List.equal SIdentifier.equal actuals1 actuals2
    | TApp (tf1, arg_types1), TApp (tf2, arg_types2) ->
        SIdentifier.equal tf1 tf2
        && List.equal SType.equal arg_types1 arg_types2
    | GasExpr (g1, (e1', _)), GasExpr (g2, (e2', _)) ->
        String.equal (SGasCharge.pp_gas_charge g1) (SGasCharge.pp_gas_charge g2)
        && expr_eq e1' e2'
    | Fun (a1, t1, (e1', _)), Fun (a2, t2, (e2', _))
    | Fixpoint (a1, t1, (e1', _)), Fixpoint (a2, t2, (e2', _)) ->
        SIdentifier.equal a1 a2 && SType.equal t1 t2 && expr_eq e1' e2'
    | TFun (a1, (e1', _)), TFun (a2, (e2', _)) ->
        SIdentifier.equal a1 a2 && expr_eq e1' e2'
    | _ -> false

  (* This is a copy of the one in PatternMatching.ml
   * but works on libeval_literal instead, supports Clo and TAbs. *)
  let libeval_literal_type ?(lc = dummy_loc) l =
    let open TULiteral.LType in
    let open Datatypes in
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
    | ByStrX bs -> pure (bystrx_typ (Bystrx.width bs))
    (* Check that messages and events have storable parameters. *)
    | Msg bs -> get_msgevnt_type bs lc
    | Map ((kt, vt), _) -> pure (MapType (kt, vt))
    | ADTValue (cname, ts, _) ->
        let%bind adt, _ = DataTypeDictionary.lookup_constructor cname in
        pure @@ ADT (mk_loc_id adt.tname, ts)
    | Clo ((_, rep), _) | TAbs ((_, rep), _) -> pure (ER.get_type rep).tp

  (* Same as literal_eq, except that this handles Clo and TAbs. *)
  let rec libeval_literal_eq l1 l2 =
    let open Stdint in
    let open Scilla_base.Literal in
    match (l1, l2) with
    | IntLit (Int32L i1), IntLit (Int32L i2) -> Int32.compare i1 i2 = 0
    | IntLit (Int64L i1), IntLit (Int64L i2) -> Int64.compare i1 i2 = 0
    | IntLit (Int128L i1), IntLit (Int128L i2) -> Int128.compare i1 i2 = 0
    | IntLit (Int256L i1), IntLit (Int256L i2) ->
        Integer256.Int256.compare i1 i2 = 0
    | UintLit (Uint32L i1), UintLit (Uint32L i2) -> Uint32.compare i1 i2 = 0
    | UintLit (Uint64L i1), UintLit (Uint64L i2) -> Uint64.compare i1 i2 = 0
    | UintLit (Uint128L i1), UintLit (Uint128L i2) -> Uint128.compare i1 i2 = 0
    | UintLit (Uint256L i1), UintLit (Uint256L i2) ->
        Integer256.Uint256.compare i1 i2 = 0
    | StringLit s1, StringLit s2 -> String.equal s1 s2
    | BNum b1, BNum b2 -> String.equal (BNumLit.get b1) (BNumLit.get b2)
    | ByStr b1, ByStr b2 -> Bystr.equal b1 b2
    | ByStrX b1, ByStrX b2 -> Bystrx.equal b1 b2
    | Msg b1, Msg b2 ->
        List.equal
          (fun (n1, t1, l1) (n2, t2, l2) ->
            String.equal n1 n2 && SType.equal t1 t2 && libeval_literal_eq l1 l2)
          b1 b2
    | Map ((kt1, vt1), m1), Map ((kt2, vt2), m2) ->
        SType.equal kt1 kt2 && SType.equal vt1 vt2
        && Caml.Hashtbl.length m1 = Caml.Hashtbl.length m2
        && Caml.Hashtbl.fold
             (fun k1 v1 res ->
               match Caml.Hashtbl.find_opt m2 k1 with
               | Some v2 -> res && libeval_literal_eq v1 v2
               | None -> false)
             m1 true
    | ADTValue (cname1, ts1, args1), ADTValue (cname2, ts2, args2) ->
        Name.equal cname1 cname2
        && List.equal SType.equal ts1 ts2
        && List.equal libeval_literal_eq args1 args2
    | Clo ((e1, _), env1), Clo ((e2, _), env2) ->
        List.equal
          (fun (n1, l1) (n2, l2) ->
            Name.equal n1 n2 && libeval_literal_eq l1 l2)
          env1 env2
        && expr_eq e1 e2
    | _ -> false

  (* This is a copy of the one in PatternMatching.ml
   * but works on libeval_literal instead. *)
  let rec match_with_pattern v p =
    let open Datatypes in
    match p with
    | Wildcard -> pure []
    | Binder x -> pure @@ [ (x, v) ]
    | Constructor (cn, ps) -> (
        let%bind _, ctr =
          DataTypeDictionary.lookup_constructor
            ~sloc:(SR.get_loc (get_rep cn))
            (get_id cn)
        in
        (* Check that the pattern is well-formed *)
        if ctr.arity <> List.length ps then
          fail0 ~kind:"Required constructor parameters not provided"
            ~inst:
              (sprintf
                 "Constructor %s requires %d parameters, but %d are provided."
                 (EvalName.as_error_string ctr.cname)
                 ctr.arity (List.length ps))
        else
          (* Pattern is well-formed, processing the value *)
          (* In this branch ctr.arity = List.length ps *)
          match v with
          | ADTValue (cn', _, ls')
            when [%equal: EvalName.t] cn' ctr.cname
                 && List.length ls' = ctr.arity ->
              (* The value structure matches the pattern *)
              (* In this branch ctr.arity = List.length ps = List.length ls', so we can use zip_exn *)
              let%bind res_list =
                map2M ls' ps ~f:match_with_pattern ~msg:(fun () -> assert false)
              in
              (* Careful: there might be duplicate bindings! *)
              (* We will need to catch this statically. *)
              pure @@ List.concat res_list
          | _ -> fail0 ~kind:"Cannot match value againts pattern." ?inst:None)

  let rec to_libeval_literal = function
    | SLiteral.StringLit s -> pure @@ StringLit s
    | IntLit i -> pure @@ IntLit i
    | UintLit i -> pure @@ UintLit i
    | BNum b -> pure @@ BNum b
    | ByStrX b -> pure @@ ByStrX b
    | ByStr b -> pure @@ ByStr b
    | Msg mlist ->
        let%bind mlist' =
          mapM mlist ~f:(fun (m, t, l) ->
              let%bind l' = to_libeval_literal l in
              pure (m, t, l'))
        in
        pure @@ Msg mlist'
    | Map (mt, t) ->
        let open Caml in
        let t' = Hashtbl.create (Hashtbl.length t) in
        let tlist = Hashtbl.to_seq t |> List.of_seq in
        let%bind () =
          forallM tlist ~f:(fun (k, v) ->
              let%bind k' = to_libeval_literal k in
              let%bind v' = to_libeval_literal v in
              let () = Hashtbl.replace t' k' v' in
              pure ())
        in
        pure @@ Map (mt, t')
    | ADTValue (name, types, args) ->
        let%bind args' = mapM args ~f:to_libeval_literal in
        pure @@ ADTValue (name, types, args')
    | Clo _ ->
        fail0 ~kind:"Cannot convert OCaml closures to Scilla closures"
          ?inst:None
    | TAbs _ ->
        fail0 ~kind:"Cannot convert OCaml closures to Scilla type closures"
          ?inst:None

  let rec from_libeval_literal = function
    | StringLit s -> pure @@ SLiteral.StringLit s
    | IntLit i -> pure @@ SLiteral.IntLit i
    | UintLit i -> pure @@ SLiteral.UintLit i
    | BNum b -> pure @@ SLiteral.BNum b
    | ByStrX b -> pure @@ SLiteral.ByStrX b
    | ByStr b -> pure @@ SLiteral.ByStr b
    | Msg mlist ->
        let%bind mlist' =
          mapM mlist ~f:(fun (m, t, l) ->
              let%bind l' = from_libeval_literal l in
              pure (m, t, l'))
        in
        pure @@ SLiteral.Msg mlist'
    | Map (mt, t) ->
        let open Caml in
        let t' = Hashtbl.create (Hashtbl.length t) in
        let tlist = Hashtbl.to_seq t |> List.of_seq in
        let%bind () =
          forallM tlist ~f:(fun (k, v) ->
              let%bind k' = from_libeval_literal k in
              let%bind v' = from_libeval_literal v in
              let () = Hashtbl.replace t' k' v' in
              pure ())
        in
        pure @@ SLiteral.Map (mt, t')
    | ADTValue (name, types, args) ->
        let%bind args' = mapM args ~f:from_libeval_literal in
        pure @@ SLiteral.ADTValue (name, types, args')
    | Clo _ ->
        let noexec _ =
          EvalMonad.fail0 ~kind:"Unexpected evaluation of closure" ?inst:None
        in
        pure @@ SLiteral.Clo noexec
    | TAbs _ ->
        let noexec _ =
          EvalMonad.fail0 ~kind:"Unexpected evaluation of type closure"
            ?inst:None
        in
        pure @@ SLiteral.TAbs noexec

  (* Translate environment literals to Scilla_base type. *)
  let translate_env env =
    mapM env ~f:(fun (name, lit) ->
        let%bind lit' = from_libeval_literal lit in
        pure (name, lit'))

  let rep_drop_type id =
    SIdentifier.mk_id (SIdentifier.get_id id)
      (ER.get_loc (SIdentifier.get_rep id))

  (* Same as the one in Syntax.ml, but updates rep too. *)
  let rec subst_type_in_expr tvar tp (e, rep') =
    (* Function to substitute in a rep. *)
    let subst_rep r =
      ER.mk_rep (ER.get_loc r)
        (TypeUtil.PlainTypes.mk_qualified_type
           (Type.subst_type_in_type' tvar tp (ER.get_type r).tp))
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

  let rec exp_eval (e, erep) env =
    let loc = ER.get_loc erep in
    match e with
    | Literal l ->
        let%bind l' = to_libeval_literal l in
        pure ((l', 0), env)
    | Var i ->
        let%bind v = Env.lookup env (rep_drop_type i) in
        pure @@ ((v, 0), env)
    | Let (i, _, lhs, rhs) ->
        let%bind (lval, g1), _ = exp_eval lhs env in
        let env' = Env.bind env (get_id i) lval in
        let%bind (rval, g2), env'' = exp_eval rhs env' in
        pure ((rval, g1 + g2), env'')
    | Message bs ->
        (* Resolve all message payload *)
        let resolve pld =
          match pld with
          | MLit l -> to_libeval_literal l
          | MVar i -> Env.lookup env (rep_drop_type i)
        in
        let%bind payload_resolved =
          (* Make sure we resolve all the payload *)
          mapM bs ~f:(fun (s, pld) ->
              let%bind lit = resolve pld in
              let%bind t = libeval_literal_type lit in
              pure (s, t, lit))
        in
        pure ((Msg payload_resolved, 0), env)
    | App (f, actuals) ->
        (* Resolve the actuals *)
        let%bind args =
          mapM actuals ~f:(fun arg -> Env.lookup env (rep_drop_type arg))
        in
        let%bind ff = Env.lookup env (rep_drop_type f) in
        (* Apply iteratively, also evaluating curried lambdas *)
        let%bind fully_applied, gas =
          List.fold_left args
            ~init:(pure (ff, 0))
            ~f:(fun res arg ->
              let%bind v, gacc = res in
              let%bind res', g = try_apply_as_closure v arg in
              pure (res', g + gacc))
        in
        pure ((fully_applied, gas), env)
    | Constr (cname, ts, actuals) ->
        let open Datatypes.DataTypeDictionary in
        let%bind _, constr =
          lookup_constructor ~sloc:(SR.get_loc (get_rep cname)) (get_id cname)
        in
        let alen = List.length actuals in
        if constr.arity <> alen then
          fail1 ~kind:"Incorrect number of arguments to constructor"
            ~inst:
              (sprintf "Constructor %s expects %d arguments, but got %d."
                 (as_error_string cname) constr.arity alen)
            (SR.get_loc (get_rep cname))
        else
          (* Resolve the actuals *)
          let%bind args =
            mapM actuals ~f:(fun arg -> Env.lookup env (rep_drop_type arg))
          in
          (* Make sure we only pass "pure" literals, not closures *)
          let lit = ADTValue (get_id cname, ts, args) in
          pure ((lit, 0), env)
    | MatchExpr (x, clauses) ->
        let%bind v = Env.lookup env (rep_drop_type x) in
        (* Get the branch and the bindings *)
        let%bind (_, e_branch), bnds =
          tryM clauses
            ~msg:(fun () ->
              mk_error1 ~kind:"Match expression failed. No clause matched."
                ?inst:None loc)
            ~f:(fun (p, _) -> match_with_pattern v p)
        in
        (* Update the environment for the branch *)
        let env' =
          List.fold_left bnds ~init:env ~f:(fun z (i, w) ->
              Env.bind z (get_id i) w)
        in
        exp_eval e_branch env'
    | Builtin ((b, bi), targs, actuals) ->
        let%bind env' = translate_env env in
        let actuals' = List.map actuals ~f:rep_drop_type in
        let%bind res, cost =
          Eval.builtin_executor env' (b, ER.get_loc bi) targs actuals'
        in
        let%bind res' = res () in
        let%bind res'' = to_libeval_literal res' in
        pure ((res'', Stdint.Uint64.to_int cost), env)
    | TApp (tf, arg_types) ->
        let%bind ff = Env.lookup env (rep_drop_type tf) in
        let%bind fully_applied, g =
          List.fold_left arg_types
            ~init:(pure (ff, 0))
            ~f:(fun res arg_type ->
              let%bind v, gacc = res in
              let%bind res, g = try_apply_as_type_closure v arg_type in
              pure (res, gacc + g))
        in
        pure ((fully_applied, g), env)
    | GasExpr (g, e') ->
        let rec translate_gascharge = function
          | SGasCharge.StaticCost i -> EvalSyntax.SGasCharge.StaticCost i
          | SizeOf v -> SizeOf v
          | ValueOf v -> ValueOf v
          | LengthOf v -> LengthOf v
          | MapSortCost m -> MapSortCost m
          | SumOf (g1, g2) ->
              SumOf (translate_gascharge g1, translate_gascharge g2)
          | ProdOf (g1, g2) ->
              ProdOf (translate_gascharge g1, translate_gascharge g2)
          | MinOf (g1, g2) ->
              MinOf (translate_gascharge g1, translate_gascharge g2)
          | DivCeil (g1, g2) -> DivCeil (translate_gascharge g1, g2)
          | LogOf g -> LogOf (translate_gascharge g)
        in
        let%bind env' = translate_env env in
        let%bind cost = Eval.eval_gas_charge env' (translate_gascharge g) in
        let%bind (res, g), _ = exp_eval e' env in
        pure ((res, cost + g), env)
    | Fun _ | Fixpoint _ -> pure ((Clo ((e, erep), env), 0), env)
    | TFun _ -> pure ((TAbs ((e, erep), env), 0), env)

  (* Applying a function *)
  and try_apply_as_closure v arg =
    match v with
    | Clo ((Fun (formal, _, body), _), env) ->
        let env1 = Env.bind env (get_id formal) arg in
        fstM @@ exp_eval body env1
    | Clo ((Fixpoint (g, _, body), _), env) -> (
        let env1 = Env.bind env (get_id g) v in
        match%bind exp_eval body env1 with
        | (Clo ((Fun (formal, _, body), _), env1'), gasf), _ ->
            let env2 = Env.bind env1' (get_id formal) arg in
            let%bind (res, gasf'), _ = exp_eval body env2 in
            pure (res, gasf + gasf')
        | _ -> fail0 ~kind:"Body of fixpoint must be a function." ?inst:None)
    | _ -> fail0 ~kind:"Not a functional value." ?inst:None

  and try_apply_as_type_closure v arg_type =
    match v with
    | TAbs ((TFun (tv, body), _), env) ->
        let body_subst = subst_type_in_expr tv arg_type body in
        fstM @@ exp_eval body_subst env
    | _ -> fail0 ~kind:"Not a type closure." ?inst:None

  let rec rewrite_runtime_literals genv llit :
      (expr_annot, scilla_error list) result =
    let build_type_rep ty =
      ER.mk_rep dummy_loc (TypeUtil.PlainTypes.mk_qualified_type ty)
    in
    match llit with
    | StringLit _ | IntLit _ | UintLit _ | BNum _ | ByStrX _ | ByStr _ ->
        let%bind llit' = from_libeval_literal llit in
        let%bind lty = libeval_literal_type llit in
        pure (Literal llit', build_type_rep lty)
    | ADTValue (cname, tl, args) ->
        let open Datatypes.DataTypeDictionary in
        let%bind adt, _ = lookup_constructor cname in
        let%bind argtys = mapM args ~f:libeval_literal_type in
        (* A new variable for each expression to be bound to. *)
        let%bind argvars =
          mapM argtys ~f:(fun argty ->
              pure
              @@ TUIdentifier.mk_id
                   (Name.parse_simple_name (LoweringUtils.tempname "regen"))
                   (build_type_rep argty))
        in
        (* Generate expressions for each literal that's an argument. *)
        let%bind argexps = mapM args ~f:(rewrite_runtime_literals genv) in
        let res : expr_annot =
          ( Constr (Identifier.mk_id cname SR.dummy_rep, tl, argvars),
            build_type_rep
              (TULiteral.LType.ADT (TUIdentifier.mk_loc_id adt.tname, tl)) )
        in
        (* Generate let bindings for all the variables+expressions we created. *)
        pure
        @@ List.fold ~init:res
             ~f:(fun acc (var, exp) -> (Let (var, None, exp, acc), get_rep var))
             (List.zip_exn argvars argexps)
    | Map ((kt, vt), m) ->
        let mapt_rep = build_type_rep (MapType (kt, vt)) in
        let emp = Caml.Hashtbl.create (Caml.Hashtbl.length m) in
        let init = (Literal (Map ((kt, vt), emp)), mapt_rep) in
        let m' = Caml.List.of_seq (Caml.Hashtbl.to_seq m) in
        foldM
          ~f:(fun eacc (k, v) ->
            let%bind kexp = rewrite_runtime_literals genv k in
            let%bind vexp = rewrite_runtime_literals genv v in
            (* Adding both expressions to variables. *)
            let kvar =
              TUIdentifier.mk_id
                (Name.parse_simple_name (LoweringUtils.tempname "regen"))
                (build_type_rep kt)
            in
            let vvar =
              TUIdentifier.mk_id
                (Name.parse_simple_name (LoweringUtils.tempname "regen"))
                (build_type_rep vt)
            in
            let mvar =
              TUIdentifier.mk_id
                (Name.parse_simple_name (LoweringUtils.tempname "regen"))
                mapt_rep
            in
            let putop =
              ( Builtin ((Builtin_put, mapt_rep), [], [ mvar; kvar; vvar ]),
                mapt_rep )
            in
            let massign = (Let (mvar, None, eacc, putop), mapt_rep) in
            let vassign =
              (Let (vvar, None, vexp, massign), build_type_rep vt)
            in
            let kassign =
              (Let (kvar, None, kexp, vassign), build_type_rep kt)
            in
            pure kassign)
          m' ~init
    | Clo (((Fun (arg, _, body), rep) as ea), env)
    | Clo (((Fixpoint (arg, _, body), rep) as ea), env)
    | TAbs (((TFun (arg, body), rep) as ea), env) ->
        let freevars =
          List.filter (free_vars_in_expr body)
            ~f:(Fn.non (Identifier.equal arg))
        in
        (* For each free variable, we need to generate a let-in binding
         * based on the variable's value in env. However, if the value
         * happens to be the same as in genv, then we need not. *)
        foldM freevars ~init:ea ~f:(fun accexpr v ->
            let v' = rep_drop_type v in
            let%bind localenv_val = Env.lookup env v' in
            match Env.lookup genv v' with
            | Ok globalenv_val
              when libeval_literal_eq localenv_val globalenv_val ->
                pure accexpr
            | _ ->
                let%bind localenv_val' =
                  rewrite_runtime_literals genv localenv_val
                in
                (* Not in the global environment or present with a differnt value.
                   Need to generate let binding. *)
                pure (Let (v, None, localenv_val', accexpr), rep))
    | Msg fields ->
        let%bind msg_exprs =
          mapM fields ~f:(fun (s, _, l) ->
              match%bind rewrite_runtime_literals genv l with
              | Literal l', _ -> pure ((s, MLit l'), None)
              | (_, erep) as e ->
                  let mvar =
                    TUIdentifier.mk_id
                      (Name.parse_simple_name (LoweringUtils.tempname "regen"))
                      erep
                  in
                  pure ((s, MVar mvar), Some (mvar, e)))
        in
        let msg', exprs = List.unzip msg_exprs in
        let message_expr =
          (Message msg', build_type_rep (SType.PrimType Msg_typ))
        in
        pure
        @@ List.fold exprs ~init:message_expr
             ~f:(fun ((_, accrep) as accexpr) eopt ->
               match eopt with
               | Some (mvar, e) -> (Let (mvar, None, e, accexpr), accrep)
               | None -> accexpr)
    | _ -> fail0 ~kind:"Cannot rewrite literal to expression" ?inst:None

  let eval_lib_entry env id e =
    let%bind (res, gas_consumed), _ = exp_eval e env in
    pure (res, Env.bind env (get_id id) res, gas_consumed)

  let eval_lib_entries env libentries remaining_gas =
    let%bind (env', remaining_gas'), lentries' =
      fold_mapM
        ~f:(fun (accenv, acc_remaining_gas) lentry ->
          match lentry with
          | LibTyp _ -> pure ((accenv, acc_remaining_gas), lentry)
          | LibVar (lname, ltopt, ((_, lrep) as lexp)) ->
              let%bind llit, env', consumed_gas =
                eval_lib_entry accenv lname lexp
              in
              let%bind lexp', _ = rewrite_runtime_literals accenv llit in
              let remaining_gas' = remaining_gas - consumed_gas in
              if remaining_gas <= 0 then
                fail0 ~kind:"Ran out of gas during partial evaluation"
                  ?inst:None
              else
                pure
                  ( (env', remaining_gas'),
                    LibVar
                      ( lname,
                        ltopt,
                        (GasExpr (StaticCost consumed_gas, (lexp', lrep)), lrep)
                      ) ))
        ~init:(env, remaining_gas) libentries
    in
    pure (env', lentries', remaining_gas')

  let eval_library env library remaining_gas =
    let%bind env', lentries', remaining_gas' =
      eval_lib_entries env library.lentries remaining_gas
    in
    pure (env', { library with lentries = lentries' }, remaining_gas')

  let rec eval_libtree_list env lts remaining_gas =
    foldrM lts ~init:(env, [], remaining_gas)
      ~f:(fun (accenv, acclst, accremgas) lt ->
        let%bind accenv', deps', accremgas' =
          eval_libtree_list accenv lt.deps accremgas
        in
        let%bind accenv'', libn', accremgas'' =
          eval_library accenv' lt.libn accremgas'
        in
        pure (accenv'', { libn = libn'; deps = deps' } :: acclst, accremgas''))

  let eval_mod_libs rlibs elibs (cmod : cmodule) remaining_gas =
    let%bind env_rlibs, rlibs', remaining_gas_rlibs =
      eval_lib_entries Env.empty rlibs (Stdint.Uint64.to_int remaining_gas)
    in
    let%bind env_elibs, elibs', remaining_gas_elibs =
      eval_libtree_list env_rlibs elibs remaining_gas_rlibs
    in
    let%bind _env_clibs, cmod', remaining_gas_clibs =
      match cmod.libs with
      | Some libs ->
          let%bind env_clibs, clibs', remaining_gas_clibs =
            eval_library env_elibs libs remaining_gas_elibs
          in
          pure (env_clibs, { cmod with libs = Some clibs' }, remaining_gas_clibs)
      | None -> pure (env_elibs, cmod, remaining_gas_elibs)
    in
    pure ((rlibs', elibs', cmod'), Stdint.Uint64.of_int remaining_gas_clibs)

  let eval_libs_wrapper rlibs elibs remaining_gas =
    let%bind env_rlibs, rlibs', remaining_gas_rlibs =
      eval_lib_entries Env.empty rlibs.lentries
        (Stdint.Uint64.to_int remaining_gas)
    in
    let%bind _env_elibs, elibs', remaining_gas_elibs =
      eval_libtree_list env_rlibs elibs remaining_gas_rlibs
    in
    pure
      ( ({ rlibs with lentries = rlibs' }, elibs'),
        Stdint.Uint64.of_int remaining_gas_elibs )
end
