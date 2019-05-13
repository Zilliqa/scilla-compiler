
open TypeUtil
open Syntax
open Core
open MonomorphicSyntax
open ClosuredSyntax
open ParserUtil

(* Perform closure conversion of Scilla programs.
 * Addtionally, flatten out the AST into statements
 * (which is mostly flattening out let-in expressions).
 *)
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

  (* Create a closure for creating new variable names.
   * The closure maintains a state for incremental numbering.
   * This seems much simpler than carrying around an integer
   * everywhere in functional style. Since this isn't critical,
   * I choose readability over immutability.
   *)
  let newname_creator () =
    let name_counter = ref 0 in
    (fun base rep ->
      (* system generated names will begin with "_" for uniqueness. *)
      let n = "_" ^ base ^ (Int.to_string !name_counter) in
      name_counter := (!name_counter+1);
      asIdL n rep)

  (* Convert e to a list of statements with the final value `Bind`ed to dstvar. 
   * `newname` is an instance of `newname_creator` defined above. *)
  let expr_to_stmts newname (e, erep) dstvar =
    let rec recurser (e, erep) dstvar = match e with
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
      let s_lhs = recurser lhs i in
      (* Since "i" is bound only in RHS and not beyond, let's create a
         new name for it, to prevent potential shadowing of an outer
         "i" in statements that come after RHS is expanded. *)
      let rhs' = rename_free_var rhs i (newname (get_id i) (ER.get_loc (get_rep i))) in
      let s_rhs = recurser rhs' dstvar in
      (* TODO: This is potentially quadratic. The way to fix it is to have
         an accumulator. But that will require accummulating in the reverse
         order and calling List.rev at at end (and that'll be quadratic too?). *)
      s_lhs @ s_rhs
    | MatchExpr (i, clauses) ->
      let clauses' = List.map clauses ~f:(fun (pat, e') ->
        let sl = recurser e' dstvar in
        (pat, sl)
      ) in
      let s = (CS.MatchStmt (i, clauses'), erep_to_srep erep) in
      [s]
    | Fun (i, t, body)
    | Fixpoint (i, t, body) ->
      let fname = newname "fundef_" (ER.get_loc erep) in
      let retvar = newname "retval_" (ER.get_loc erep) in
      (* closure conversion and isolation of function body. *)
      (* 1. Simply convert the expression to statements. *)
      let body' = recurser body retvar in
      (* 2. Append a return statement at the end of the function definition. *)
      let body'' = body' @ [ (CS.Ret(retvar), erep_to_srep erep) ] in
      (* 3. Find the free variables in the original expression. *)
      let freevars = free_vars_in_expr body in
      let fvenv : CS.cloenv = List.map freevars ~f:(fun i -> i, (ER.get_type (get_rep i)).tp) in
      (* 4. Add LoadEnv statements for each free variable at the beginning of the function. *)
      let loadenvs = List.map fvenv ~f:(fun (v, _t) ->
        (* We write to a variable with the same name
           (no point in using a different name and rewriting the uses). *)
        CS.LoadEnv(v, v, fvenv), erep_to_srep erep
      ) in
      let body_stmts = loadenvs @ body'' in
      let rec fbody = (fname, (i, t), { CS.thisfun = ref fbody; envvars = fvenv }, body_stmts) in
      (* 5. Store variables into the closure environment. *)
      let envstores = List.map fvenv ~f:(fun (v, _t) ->
        CS.StoreEnv(v, v, fvenv), erep_to_srep erep
      ) in
      (* 6. We now have an environment and the function's body. Form a closure. *)
      let (_, _, fclo, _) = fbody in
      let s = (CS.Bind(dstvar, (CS.FunClo fclo, erep)), erep_to_srep erep) in
      envstores @ [s]
    | TFunMap (_, tbodies) ->
      let common_dstvar = newname "tfmval_" (ER.get_loc erep) in
      let tbodies' = List.map tbodies ~f:(fun (t, body) ->
        let body' = recurser body common_dstvar in
        (t, body')
      ) in
      let tfm = (CS.TFunMap (common_dstvar, tbodies'), erep) in
      let s = (CS.Bind(dstvar, tfm), erep_to_srep erep) in
      [s]
    in
    recurser (e, erep) dstvar

(*   let clocnv_module (cmod : cmodule) rlibs elibs =
 *)

end