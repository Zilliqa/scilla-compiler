
open Syntax
open ExplicitAnnotationSyntax
open Core
open MonomorphicSyntax
open ClosuredSyntax
open MonadUtil
open Result.Let_syntax

(* Perform closure conversion of Scilla programs.
 * Addtionally, flatten out the AST into statements
 * (which is mostly flattening out let-in expressions).
 *)
module ScillaCG_CloCnv = struct

  module MS = MmphSyntax
  module CS = CloCnvSyntax

  open MS

  let erep_to_srep (erep : eannot) : eannot =
    { ea_tp = None; ea_loc = erep.ea_loc }

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

  let translate_payload = function
    | MLit l -> CS.MLit l
    | MVar v -> CS.MVar v

  let rec translate_pattern = function
    | Wildcard -> CS.Wildcard
    | Binder v -> CS.Binder v
    | Constructor (s, plist) ->
      CS.Constructor (s, List.map plist ~f:translate_pattern)

  (* Convert e to a list of statements with the final value `Bind`ed to dstvar. 
   * `newname` is an instance of `newname_creator` defined above. *)
  let expr_to_stmts newname (e, erep) dstvar =

    let rec recurser (e, erep) dstvar = match e with
    | Literal l ->
      let s = (CS.Bind(dstvar, (CS.Literal l, erep)), erep_to_srep erep) in
      pure [ s ]
    | Var v ->
      let s = (CS.Bind(dstvar, (CS.Var v, erep)), erep_to_srep erep) in
      pure  [s]
    | Message m ->
      let m' = List.map m ~f:(fun (s, p) -> (s, translate_payload p)) in
      let s = (CS.Bind(dstvar, (CS.Message m', erep)), erep_to_srep erep) in
      pure  [s]
    | Constr (s, tl, il) ->
      let s = (CS.Bind(dstvar, (CS.Constr (s, tl, il), erep)), erep_to_srep erep) in
      pure [s]
    | Builtin (i, il)  ->
      let s = (CS.Bind(dstvar, (CS.Builtin (i, il), erep)), erep_to_srep erep) in
      pure [s]
    | App (a, al) ->
      let s = (CS.Bind(dstvar, (CS.App (a, al), erep)), erep_to_srep erep) in
      pure [s]
    | TFunSel (i, tl) ->
      let s = (CS.Bind(dstvar, (CS.TFunSel (i, tl), erep)), erep_to_srep erep) in
      pure [s]
    | Let (i, _topt, lhs, rhs) ->
      let%bind s_lhs = recurser lhs i in
      (* Since "i" is bound only in RHS and not beyond, let's create a
         new name for it, to prevent potential shadowing of an outer
         "i" in statements that come after RHS is expanded. *)
      let rhs' = rename_free_var rhs i (newname (get_id i) (get_rep i)) in
      let%bind s_rhs = recurser rhs' dstvar in
      (* TODO: This is potentially quadratic. The way to fix it is to have
         an accumulator. But that will require accummulating in the reverse
         order and calling List.rev at at end. *)
      pure @@ s_lhs @ s_rhs
    | MatchExpr (i, clauses) ->
      let%bind clauses' = mapM clauses ~f:(fun (pat, e') ->
        let%bind sl = recurser e' dstvar in
        pure (translate_pattern pat, sl)
      ) in
      let s = (CS.MatchStmt (i, clauses'), erep_to_srep erep) in
      pure [s]
    | Fun (i, t, body)
    | Fixpoint (i, t, body) ->
      let%bind (f : CS.fundef) = create_fundef body [(i, t)] in
      (* 5. Store variables into the closure environment. *)
      let envstores = List.map (snd f.fclo.envvars) ~f:(fun (v, _t) ->
        CS.StoreEnv(v, v, f.fclo.envvars), erep_to_srep erep
      ) in
      (* 6. We now have an environment and the function's body. Form a closure. *)
      let s = (CS.Bind(dstvar, (CS.FunClo f.fclo, erep)), erep_to_srep erep) in
      pure @@ envstores @ [s]
    | TFunMap tbodies ->
      let%bind tbodies' = mapM tbodies ~f:(fun (t, body) ->
        let%bind (f : CS.fundef) = create_fundef body [] in
        pure (t, f.fclo)
      ) in
      match tbodies' with
      | (_, fclo) :: _ ->
        (* The stores into env is common for all type instantiations. *)
        let envstores = List.map (snd fclo.envvars) ~f:(fun (v, _t) ->
          CS.StoreEnv(v, v, fclo.envvars), erep_to_srep erep
        ) in
        let tfm = (CS.TFunMap (tbodies'), erep) in
        let s = (CS.Bind(dstvar, tfm), erep_to_srep erep) in
        pure @@ envstores @ [s]
      | [] ->
      (* I think this is only possible if there are no instantiations of the TFun,
       * which with the current strategy only happens if there are no types avaialble
       * to instantiate it with, and that shouldn't happen. Once we start optimising
       * the type instantiations we might end up in a situation where a user has written
       * a TFun which never gets used, in which case this branch could be executed.
       * So the branch cannot throw an error. *)
        let s = (CS.Bind(dstvar, (CS.TFunMap([]), erep)), erep_to_srep erep) in
        pure [s]

    (* Create a function definition out of an expression. *)
    and create_fundef body args =
      let fname = newname "fundef_" erep in
      let retvar = newname "retval_" erep in
      (* closure conversion and isolation of function body. *)
      (* 1. Simply convert the expression to statements. *)
      let%bind body' = recurser body retvar in
      (* 2. Append a return statement at the end of the function definition. *)
      let body'' = body' @ [ (CS.Ret(retvar), erep_to_srep erep) ] in
      (* 3(a). Find the free variables in the original expression. *)
      let freevars = free_vars_in_expr body in
      let%bind evars = mapM freevars ~f:(fun i ->
        match (get_rep i).ea_tp with
        | Some t -> pure (i, t)
        | None -> fail1 (sprintf "ClosureConversion: Type for free variable %s not available" (get_id i)) (get_rep i).ea_loc
      ) in
      (* 3(b). Form the environment by attaching a (statically) unique id. *)
      let fvenv = (get_id fname, evars) in
      (* 4. Add LoadEnv statements for each free variable at the beginning of the function. *)
      let loadenvs = List.map (snd fvenv) ~f:(fun (v, _t) ->
        (* We write to a variable with the same name
           (no point in using a different name and rewriting the uses). *)
        CS.LoadEnv(v, v, fvenv), erep_to_srep erep
      ) in
      let body_stmts = loadenvs @ body'' in
      let rec fbody : CS.fundef = {
        fname = fname; fargs = args;
        fclo = { CS.thisfun = ref fbody; envvars = fvenv };
        fbody = body_stmts
      } in
      pure fbody
    in
    recurser (e, erep) dstvar

  let rec expand_stmts newname stmts =
    foldrM stmts ~init:[] ~f:(fun acc (stmt, srep) ->
      (match stmt with
      | Load (x, m) ->
        let s' = CS.Load(x, m) in
        pure @@ (s', srep) :: acc
      | Store (m, i) ->
        let s' = CS.Store(m, i) in
        pure @@ (s', srep) :: acc
      | MapUpdate (i, il, io) ->
        let s' = CS.MapUpdate (i, il, io) in
        pure @@ (s', srep) :: acc
      | MapGet (i, i', il, b) ->
        let s' = CS.MapGet (i, i', il, b) in
        pure @@ (s', srep) :: acc
      | ReadFromBC (i, s) ->
        let s' = CS.ReadFromBC (i, s) in
        pure @@ (s', srep) :: acc
      | AcceptPayment ->
        let s' = CS.AcceptPayment in
        pure @@ (s', srep) :: acc
      | SendMsgs m ->
        let s' = CS.SendMsgs(m) in
        pure @@ (s', srep) :: acc
      | CreateEvnt e ->
        let s' = CS.CreateEvnt(e) in
        pure @@ (s', srep) :: acc 
      | Throw t ->
        let s' = CS.Throw(t) in
        pure @@ (s', srep) :: acc
      | CallProc (p, al) ->
        let s' = CS.CallProc(p, al) in
        pure @@ (s', srep) :: acc
      | Bind (i , e) ->
        let%bind stmts' = expr_to_stmts newname e i in
        pure @@ stmts' @ acc
      | MatchStmt (i, pslist) ->
        let%bind pslist' = mapM ~f:(fun (p, ss) ->
          let%bind ss' = expand_stmts newname ss in
          pure (translate_pattern p, ss')
        ) pslist
        in
        let s' = CS.MatchStmt(i, pslist') in
        pure @@ (s', srep) :: acc
      )
    )

  let clocnv_module (cmod : cmodule) rlibs elibs =
    let newname = newname_creator() in

    (* Go through each library entry and accummulate statements and type declarations. *)
    let clocnv_lib_entries lentries =
      foldrM ~init:([]) ~f:(fun stmt_acc lentry ->
        match lentry with
        | LibVar (i, lexp) ->
          let%bind sts = expr_to_stmts newname lexp i in
          pure (sts @ stmt_acc)
        | LibTyp _ ->
          (* Having run `recursion_module` as a pre-pass to closure conversion,
             we can expect that all types are registered in Datatypes.ml already. *)
          pure stmt_acc
      ) lentries
    in
    let%bind rlibs_stmts = clocnv_lib_entries rlibs in

    (* Translate external libraries (libtree). *)
    let rec clocnv_libtree libt =
      let%bind deps_stmts_list = mapM ~f:(fun dep ->
        clocnv_libtree dep
      ) libt.deps in
      let deps_stmts = List.concat deps_stmts_list in
      let%bind stmts = clocnv_lib_entries libt.libn.lentries in
      pure (deps_stmts @ stmts)
    in
    let%bind elibs_stmts_list = mapM ~f:(fun elib ->
      clocnv_libtree elib
    ) elibs in
    let elibs_stmts = List.concat elibs_stmts_list in

    (* Translate contract library. *)
    let%bind clib_stmts =
      match cmod.libs with
      | Some clib -> clocnv_lib_entries clib.lentries
      | None -> pure ([])
    in

    let lib_stmts' = 
      rlibs_stmts @ elibs_stmts @ clib_stmts in

    (* Translate field initialization expressions to statements. *)
    let%bind cfields' =
      mapM cmod.contr.cfields ~f:(fun (i, t, e) ->
        let%bind e' = expr_to_stmts newname e i in
        pure (i, t, e')
      )
    in

    (* Translate all transitions / procedures. *)
    let%bind ccomps' =
      mapM cmod.contr.ccomps ~f:(fun comp ->
        let%bind comp_body' = expand_stmts newname comp.comp_body in
        pure { CS.comp_type = comp.comp_type;
               CS.comp_name = comp.comp_name;
               CS.comp_params = comp.comp_params;
               CS.comp_body = comp_body' }
      )
    in

    let%bind contr' =
      pure { CS.cname = cmod.contr.cname ;
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

    pure cmod'

  (* A wrapper to translate pure expressions. *)
  let clocnv_expr_wrapper ((e, erep) : expr_annot) =
    let newname = newname_creator() in
    expr_to_stmts newname (e, erep) (newname "expr_" erep)

  module OutputSyntax = CS

end
