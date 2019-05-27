
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
module ScillaCG_CloCnv
    (ER : sig
       include Rep
       val get_type : rep -> PlainTypes.t inferred_type
     end) = struct

  (* How to not hardcode this? `erep_to_srep` is the issue. *)
  module SR = ParserRep

  module TU = TypeUtilities (SR) (ER)
  module MonomorphizedSyntax = MmphSyntax (SR) (ER)
  module CS = CloCnvSyntax (SR) (ER)

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
      let rhs' = rename_free_var rhs i (newname (get_id i) (get_rep i)) in
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
      let (_, _, fclo, _) : CS.fundef = create_fundef body [(i, t)] in
      (* 5. Store variables into the closure environment. *)
      let envstores = List.map fclo.envvars ~f:(fun (v, _t) ->
        CS.StoreEnv(v, v, fclo.envvars), erep_to_srep erep
      ) in
      (* 6. We now have an environment and the function's body. Form a closure. *)
      let s = (CS.Bind(dstvar, (CS.FunClo fclo, erep)), erep_to_srep erep) in
      envstores @ [s]
    | TFunMap (_, tbodies) ->
      let tbodies' = List.map tbodies ~f:(fun (t, body) ->
        let (_, _, fclo, _) = create_fundef body [] in
        (t, fclo)
      ) in
      match tbodies' with
      | (_, fclo) :: _ ->
        (* The stores into env is common for all type instantiations (right?) *)
        let envstores = List.map fclo.envvars ~f:(fun (v, _t) ->
          CS.StoreEnv(v, v, fclo.envvars), erep_to_srep erep
        ) in
        let tfm = (CS.TFunMap (tbodies'), erep) in
        let s = (CS.Bind(dstvar, tfm), erep_to_srep erep) in
        envstores @ [s]
      | [] ->
        (* Is this possible? *)
        let s = (CS.Bind(dstvar, (CS.TFunMap([]), erep)), erep_to_srep erep) in
        [s]

    (* Create a function definition out of an expression. *)
    and create_fundef body args =
      let fname = newname "fundef_" erep in
      let retvar = newname "retval_" erep in
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
      let rec fbody = (fname, args, { CS.thisfun = ref fbody; envvars = fvenv }, body_stmts) in
      fbody
    in
    recurser (e, erep) dstvar

  let rec expand_stmts newname stmts =
    List.fold_right stmts ~init:[] ~f:(fun (stmt, srep) acc ->
      (match stmt with
      | Load (x, m) ->
        let s' = CS.Load(x, m) in
        (s', srep) :: acc
      | Store (m, i) ->
        let s' = CS.Store(m, i) in
        (s', srep) :: acc
      | MapUpdate (i, il, io) ->
        let s' = CS.MapUpdate (i, il, io) in
        (s', srep) :: acc
      | MapGet (i, i', il, b) ->
        let s' = CS.MapGet (i, i', il, b) in
        (s', srep) :: acc
      | ReadFromBC (i, s) ->
        let s' = CS.ReadFromBC (i, s) in
        (s', srep) :: acc
      | AcceptPayment ->
        let s' = CS.AcceptPayment in
        (s', srep) :: acc
      | SendMsgs m ->
        let s' = CS.SendMsgs(m) in
        (s', srep) :: acc
      | CreateEvnt e ->
        let s' = CS.CreateEvnt(e) in
        (s', srep) :: acc 
      | Throw t ->
        let s' = CS.Throw(t) in
        (s', srep) :: acc
      | CallProc (p, al) ->
        let s' = CS.CallProc(p, al) in
        (s', srep) :: acc
      | Bind (i , e) ->
        let stmts' = expr_to_stmts newname e i in
        stmts' @ acc
      | MatchStmt (i, pslist) ->
        let pslist' = List.map ~f:(fun (p, ss) ->
          let ss' = expand_stmts newname ss in
          (p, ss')
        ) pslist
        in
        let s' = CS.MatchStmt(i, pslist') in
        (s', srep) :: acc
      )
    )

  let clocnv_module (cmod : cmodule) rlibs elibs =
    let newname = newname_creator() in

    (* Go through each library entry and accummulate statements and type declarations. *)
    let clocnv_lib_entries lentries =
      List.fold_right ~init:([]) ~f:(fun lentry stmt_acc ->
        match lentry with
        | LibVar (i, lexp) ->
          let sts = expr_to_stmts newname lexp i in
          sts @ stmt_acc
        | LibTyp _ ->
          (* Having run `recursion_module` as a pre-pass to closure conversion,
             we can expect that all types are registered in Datatypes.ml already. *)
          stmt_acc
      ) lentries
    in
    let rlibs_stmts = clocnv_lib_entries rlibs in

    (* Translate external libraries (libtree). *)
    let rec clocnv_libtree libt =
      let deps_stmts_list = List.map ~f:(fun dep ->
        clocnv_libtree dep
      ) libt.deps in
      let deps_stmts = List.concat deps_stmts_list in
      let stmts = clocnv_lib_entries libt.libn.lentries in
      deps_stmts @ stmts
    in
    let elibs_stmts_list = List.map ~f:(fun elib ->
      clocnv_libtree elib
    ) elibs in
    let elibs_stmts = List.concat elibs_stmts_list in

    (* Translate contract library. *)
    let clib_stmts =
      match cmod.libs with
      | Some clib -> clocnv_lib_entries clib.lentries
      | None -> ([])
    in

    let lib_stmts' = 
      rlibs_stmts @ elibs_stmts @ clib_stmts in

    (* Translate field initialization expressions to statements. *)
    let cfields' =
      List.map cmod.contr.cfields ~f:(fun (i, t, e) ->
        (i, t, expr_to_stmts newname e i)
      )
    in

    (* Translate all transitions / procedures. *)
    let ccomps' =
      List.map cmod.contr.ccomps ~f:(fun comp ->
        let comp_body' = expand_stmts newname comp.comp_body in
        { CS.comp_type = comp.comp_type;
          CS.comp_name = comp.comp_name;
          CS.comp_params = comp.comp_params;
          CS.comp_body = comp_body' }
      )
    in

    let contr' =
      { CS.cname = cmod.contr.cname ;
        CS.cparams = cmod.contr.cparams;
        CS.cfields = cfields';
        CS.ccomps = ccomps' }
    in

    let cmod' =
      { CS.smver = cmod.smver;
        CS.cname = cmod.cname;
        CS.lib_stmts = lib_stmts';
        contr = contr' }
    in

    cmod'

  (* A wrapper to translate pure expressions. *)
  let clocnv_expr_wrapper ((e, erep) : expr_annot) =
    let newname = newname_creator() in
    expr_to_stmts newname (e, erep) (newname "expr_" erep)

  module OutputSyntax = CS
  module OutputSRep = SR
  module OutputERep = ER

end
