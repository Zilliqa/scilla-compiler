
open TypeUtil
open Syntax
open Core
open MonomorphicSyntax
open ClosuredSyntax
open ParserUtil

(* Translate MmphSyntax to ClrCnvSyntax. *)
module ScillaCG_ClrCnv
    (ER : sig
       include Rep
       val get_type : rep -> PlainTypes.t inferred_type
     end) = struct

  (* How to not hardcode this? `erep_to_srep` is the issue. *)
  module SR = ParserRep

  module TU = TypeUtilities (SR) (ER)
  module MonomorphizedSyntax = MmphSyntax (SR) (ER)
  module CS = ClrCnvSyntax (SR) (ER)

  open MonomorphizedSyntax

  let erep_to_srep (erep : ER.rep) : SR.rep =
    ER.get_loc erep

  (* Convert e to a list of statements with
   * the final value `Bind`ed to dstvar. *)
  let rec expr_to_stmts (e, erep) dstvar =
    match e with
    | Literal l ->
      let s = (CS.Bind(dstvar, (CS.Literal l, erep)), erep_to_srep erep) in
      [ s ]
    | Var v ->
      let s = (CS.Bind(dstvar, (CS.Var v, erep)), erep_to_srep erep) in
      [s]
    | Message m ->
      let s = (CS.Bind(dstvar, (CS.Message m, erep)), erep_to_srep erep) in
      [s]
    | Constr (s, tl, il) ->
      let s = (CS.Bind(dstvar, (CS.Constr (s, tl, il), erep)), erep_to_srep erep) in
      [s]
    | Builtin (i, il)  ->
      let s = (CS.Bind(dstvar, (CS.Builtin (i, il), erep)), erep_to_srep erep) in
      [s]
    | App (a, al) ->
      let s = (CS.Bind(dstvar, (CS.App (a, al), erep)), erep_to_srep erep) in
      [s]
    | TFunSel (i, tl) ->
      let s = (CS.Bind(dstvar, (CS.TFunSel (i, tl), erep)), erep_to_srep erep) in
      [s]
    | Let (i, _topt, lhs, rhs) ->
      let s_lhs = expr_to_stmts lhs i in
      let s_rhs = expr_to_stmts rhs dstvar in
      (* TODO: This is potentially quadratic. The way to fix it is to have
         an accumulator. But that will require accummulating in the reverse
         order and calling List.rev at at end (and that'll be quadratic too?). *)
      s_lhs @ s_rhs
    | MatchExpr (i, clauses) ->
      let clauses' = List.map clauses ~f:(fun (pat, e') ->
        let sl = expr_to_stmts e' dstvar in
        (pat, sl)
      ) in
      let s = (CS.MatchStmt (i, clauses'), erep_to_srep erep) in
      [s]
    | Fun (i, t, body)
    | Fixpoint (i, t, body) ->
      (* closure conversion and isolation of function body. *)
      (* 1. Simply convert the expression to statements. *)
      let retvar = (asIdL "ret_val" erep) in
      let body' = expr_to_stmts body retvar in
      (* 2. Append a return statement at the end of the function definition. *)
      let body'' = body' @ [ (CS.Ret(retvar), erep_to_srep erep) ] in
      (* 3. Find the free variables in the expression. *)
      let freevars = free_vars_in_expr body in
      let fvenv : CS.cloenv = List.map freevars ~f:(fun i -> i, (ER.get_type (get_rep i)).tp) in
      (* 4. Add LoadEnv statements for each free variable at the beginning of the function. *)
      let loadenvs = List.map fvenv ~f:(fun (v, _t) ->
        (* We write to a variable with the same name
           (no point in using a different name and rewriting the uses). *)
        CS.LoadEnv(v, v, fvenv), erep_to_srep erep
      ) in
      let body_stmts = loadenvs @ body'' in
      let rec fbody = ((i, t), { CS.thisfun = ref fbody; envvars = fvenv }, body_stmts) in
      let (_, fclo, _) = fbody in
      (* We now have an environment and the function's body. Form a closure. *)
      let s = (CS.Bind(dstvar, (CS.FunClo fclo, erep)), erep_to_srep erep) in
      [s]
    | TFunMap (_, tbodies) ->
      let common_dstvar = Ident ("tfunmap_dstvar", erep) in
      let tbodies' = List.map tbodies ~f:(fun (t, body) ->
        let body' = expr_to_stmts body common_dstvar in
        (t, body')
      ) in
      let tfm = (CS.TFunMap (common_dstvar, tbodies'), erep) in
      let s = (CS.Bind(dstvar, tfm), erep_to_srep erep) in
      [s]

end