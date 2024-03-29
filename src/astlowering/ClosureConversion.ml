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
open Scilla_base
module Literal = Literal.GlobalLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open UncurriedSyntax
open MonomorphicSyntax
open ClosuredSyntax
open MonadUtil
open Result.Let_syntax
open GasCharge.ScillaGasCharge (Identifier.Name)

(* Perform closure conversion of Scilla programs.
 * Addtionally, flatten out the AST into statements
 * (which is mostly flattening out let-in and match expressions).
 *)
module ScillaCG_CloCnv = struct
  open Uncurried_Syntax
  open MmphSyntax
  module CS = CloCnvSyntax

  (* Convert e to a list of statements with the final value `Bind`ed to dstvar. 
   * `newname` is an instance of `newname_creator` defined in CodegenUtils. *)
  let expr_to_stmts newname (e, erep) dstvar =
    (* A small utility to generate env alloc and env store statements. *)
    let gen_env_stmts envvars rep =
      if List.is_empty (snd envvars) then []
      else
        let envcreate = (CS.AllocCloEnv envvars, rep) in
        let envstores =
          List.map (snd envvars) ~f:(fun (v, _t) ->
              (CS.StoreEnv (v, v, envvars), erep))
        in
        envcreate :: envstores
    in

    let rec recurser (e, erep) dstvar =
      match e with
      | Literal l ->
          let s = (CS.Bind (dstvar, (CS.Literal l, erep)), erep) in
          pure [ s ]
      | Var v ->
          let s = (CS.Bind (dstvar, (CS.Var v, erep)), erep) in
          pure [ s ]
      | Message m ->
          let m' = List.map m ~f:(fun (s, p) -> (s, p)) in
          let s = (CS.Bind (dstvar, (CS.Message m', erep)), erep) in
          pure [ s ]
      | Constr (s, tl, il) ->
          let s = (CS.Bind (dstvar, (CS.Constr (s, tl, il), erep)), erep) in
          pure [ s ]
      | Builtin (i, ts, il) ->
          let s = (CS.Bind (dstvar, (CS.Builtin (i, ts, il), erep)), erep) in
          pure [ s ]
      | App (a, al) ->
          let s = (CS.Bind (dstvar, (CS.App (a, al), erep)), erep) in
          pure [ s ]
      | TFunSel (i, tl) ->
          let s = (CS.Bind (dstvar, (CS.TFunSel (i, tl), erep)), erep) in
          pure [ s ]
      | Let (i, _topt, lhs, rhs) ->
          let%bind s_lhs = recurser lhs i in
          let%bind s_rhs = recurser rhs dstvar in
          (* TODO: This is potentially quadratic. The way to fix it is to have
             an accumulator. But that will require accummulating in the reverse
             order and calling List.rev at at end. *)
          pure @@ ((CS.LocalDecl i, erep) :: (s_lhs @ s_rhs))
      | GasExpr (g, e) ->
          let%bind s_e = recurser e dstvar in
          pure @@ ((CS.GasStmt g, erep) :: s_e)
      | MatchExpr (i, clauses, jopt) ->
          let%bind clauses' =
            mapM clauses ~f:(fun (pat, e') ->
                let%bind sl = recurser e' dstvar in
                pure (pat, sl))
          in
          let%bind jopt' =
            match jopt with
            | Some (lbl, e') ->
                let%bind sl = recurser e' dstvar in
                pure @@ Some (lbl, sl)
            | None -> pure None
          in
          let s = (CS.MatchStmt (i, clauses', jopt'), erep) in
          pure [ s ]
      | JumpExpr jlbl ->
          let s = (CS.JumpStmt jlbl, erep) in
          pure [ s ]
      | Fun (args, body) ->
          let%bind (f : CS.fundef) = create_fundef body args erep in
          (* 5. Store variables into the closure environment. *)
          let envstmts = gen_env_stmts f.fclo.envvars erep in
          (* 6. We now have an environment and the function's body. Form a closure. *)
          let s = (CS.Bind (dstvar, (CS.FunClo f.fclo, erep)), erep) in
          pure @@ envstmts @ [ s ]
      | Fixpoint (fi, _, (sube, subrep)) ->
          let%bind (f : CS.fundef) =
            match sube with
            | Fun (args, body) -> create_fundef body args subrep
            | GasExpr (g, (Fun (args, body), funrep)) ->
                (* Push the gas charge to inside the body of the function.
                 * An application of the fixpoint = application of inner fun
                 * and we can't do anything with fixpoints except apply. *)
                create_fundef (GasExpr (g, body), subrep) args funrep
            | _ ->
                fail1 ~kind:"ClosureConversion: Fixpoint must be a function."
                  ?inst:None erep.ea_loc
          in
          let env_alloc, env_stores =
            List.split_n (gen_env_stmts f.fclo.envvars erep) 1
          in
          (* The fixpoint itself becomes a closure that is passed through the
           * environment. Since we already have a store from fi to the environment
           * (inserted by gen_env_stmts, make sure the variable fi contains the
           * closure we just created *)
          let fi_decl = (CS.LocalDecl fi, erep) in
          let fi_bind = (CS.Bind (fi, (CS.FunClo f.fclo, erep)), erep) in
          (* The final result of this expression is also the same closure. *)
          let s = (CS.Bind (dstvar, (CS.Var fi, erep)), erep) in
          (* Having env_create first ensures that the LLVM code generation
           * first generates a function for the closure (which is triggered
           * by AllocCloEnv), and then works on generating the assignments
           * for CS.Bind here and the env stores. *)
          pure @@ env_alloc @ [ fi_decl; fi_bind ] @ env_stores @ [ s ]
      | TFunMap tbodies -> (
          let%bind tbodies' =
            mapM tbodies ~f:(fun (t, ((_, brep) as body)) ->
                (* We need to create a () -> brep.ea_tp type for the function. *)
                let erep' =
                  {
                    ea_loc = brep.ea_loc;
                    ea_tp = Option.map brep.ea_tp ~f:(fun t -> FunType ([], t));
                    ea_auxi = brep.ea_auxi;
                  }
                in
                let%bind (f : CS.fundef) = create_fundef body [] erep' in
                pure (t, f.fclo))
          in
          match tbodies' with
          | (_, fclo) :: _ ->
              (* The stores into env is common for all type instantiations. *)
              let envstmts = gen_env_stmts fclo.envvars erep in
              let tfm = (CS.TFunMap tbodies', erep) in
              let s = (CS.Bind (dstvar, tfm), erep) in
              pure @@ envstmts @ [ s ]
          | [] ->
              (* I think this is only possible if there are no instantiations of the TFun,
               * which with the current strategy only happens if there are no types avaialble
               * to instantiate it with, and that shouldn't happen. Once we start optimising
               * the type instantiations we might end up in a situation where a user has written
               * a TFun which never gets used, in which case this branch could be executed.
               * So the branch cannot throw an error. *)
              let s = (CS.Bind (dstvar, (CS.TFunMap [], erep)), erep) in
              pure [ s ])
    (* Create a function definition out of an expression. *)
    and create_fundef body args erep =
      let fname = newname "fundef" erep in
      let ea_loc = erep.ea_loc in
      let%bind retty =
        match erep.ea_tp with
        | Some (FunType (_, rtp)) -> pure rtp
        | _ ->
            fail1
              ~kind:
                "ClosureConversion: unable to determine return type of function"
              ?inst:None erep.ea_loc
      in
      let retrep = { ea_loc; ea_tp = Some retty; ea_auxi = erep.ea_auxi } in
      let retvar = newname "retval" retrep in
      (* closure conversion and isolation of function body. *)
      (* 1. Simply convert the expression to statements. *)
      let%bind body' = recurser body retvar in
      (* 2. Append a return statement at the end of the function definition. *)
      let body'' =
        ((CS.LocalDecl retvar, retrep) :: body') @ [ (CS.Ret retvar, retrep) ]
      in
      (* 3(a). Compute free variables in the body and remove bound args from it. *)
      let freevars' = free_vars_in_expr body in
      let freevars =
        List.filter freevars' ~f:(fun fv ->
            not (Identifier.is_mem_id fv (fst @@ List.unzip args)))
      in
      let%bind evars =
        mapM freevars ~f:(fun i ->
            match (Identifier.get_rep i).ea_tp with
            | Some t -> pure (i, t)
            | None ->
                fail1
                  ~kind:
                    "ClosureConversion: Type not available for free variable"
                  ~inst:(Identifier.as_string i) (Identifier.get_rep i).ea_loc)
      in
      (* 3(b). Form the environment by attaching a (statically) unique id. *)
      let fvenv = (fname, evars) in
      (* 4. Add LoadEnv statements for each free variable at the beginning of the function. *)
      let loadenvs =
        List.map (snd fvenv) ~f:(fun (v, _t) ->
            (* We write to a variable with the same name
               (no point in using a different name and rewriting the uses). *)
            (CS.LoadEnv (v, v, fvenv), erep))
      in
      let body_stmts = loadenvs @ body'' in
      let rec fbody : CS.fundef =
        {
          fname;
          fargs = args;
          fretty = retty;
          fclo = { CS.thisfun = ref fbody; envvars = fvenv };
          fbody = body_stmts;
        }
      in
      pure fbody
    in
    recurser (e, erep) dstvar

  (* Closure convert within a list of statements. Also flatten the AST. *)
  let rec expand_stmts newname stmts =
    foldrM stmts ~init:[] ~f:(fun acc (stmt, srep) ->
        match stmt with
        | Load (x, m) ->
            let s' = CS.Load (x, m) in
            pure @@ ((CS.LocalDecl x, Identifier.get_rep x) :: (s', srep) :: acc)
        | RemoteLoad (x, addr, m) ->
            let s' = CS.RemoteLoad (x, addr, m) in
            pure @@ ((CS.LocalDecl x, Identifier.get_rep x) :: (s', srep) :: acc)
        | TypeCast (x, a, t) ->
            let s' = CS.TypeCast (x, a, t) in
            pure @@ ((CS.LocalDecl x, Identifier.get_rep x) :: (s', srep) :: acc)
        | Store (m, i) ->
            let s' = CS.Store (m, i) in
            pure @@ ((s', srep) :: acc)
        | MapUpdate (i, il, io) ->
            let s' = CS.MapUpdate (i, il, io) in
            pure @@ ((s', srep) :: acc)
        | MapGet (i, i', il, b) ->
            let s' = CS.MapGet (i, i', il, b) in
            pure @@ ((CS.LocalDecl i, Identifier.get_rep i) :: (s', srep) :: acc)
        | RemoteMapGet (i, addr, i', il, b) ->
            let s' = CS.RemoteMapGet (i, addr, i', il, b) in
            pure @@ ((CS.LocalDecl i, Identifier.get_rep i) :: (s', srep) :: acc)
        | ReadFromBC (i, s) ->
            let s' =
              match s with
              | CurBlockNum -> [ (CS.ReadFromBC (i, CurBlockNum), srep) ]
              | ChainID -> [ (CS.ReadFromBC (i, ChainID), srep) ]
              | ReplicateContr (addr, iparams) ->
                  [ (CS.ReadFromBC (i, ReplicateContr (addr, iparams)), srep) ]
              | Timestamp v ->
                  (* _read_blockchain takes string arguments.
                   * So convert the BNum to a String. *)
                  let stringed_v_rep =
                    {
                      ea_tp =
                        Some
                          (Uncurried_Syntax.PrimType
                             Scilla_base.Type.PrimType.String_typ);
                      ea_loc = srep.ea_loc;
                      ea_auxi = None;
                    }
                  in
                  let stringed_builtin =
                    ( CS.Builtin
                        ((Syntax.Builtin_to_string, stringed_v_rep), [], [ v ]),
                      stringed_v_rep )
                  in
                  let stringed_v =
                    newname (Identifier.as_string v) stringed_v_rep
                  in
                  let stringd_bind =
                    (CS.Bind (stringed_v, stringed_builtin), srep)
                  in
                  [
                    (CS.LocalDecl stringed_v, stringed_v_rep);
                    stringd_bind;
                    (CS.ReadFromBC (i, Timestamp stringed_v), srep);
                  ]
            in
            pure @@ ((CS.LocalDecl i, Identifier.get_rep i) :: (s' @ acc))
        | AcceptPayment ->
            let s' = CS.AcceptPayment in
            pure @@ ((s', srep) :: acc)
        | SendMsgs m ->
            let s' = CS.SendMsgs m in
            pure @@ ((s', srep) :: acc)
        | CreateEvnt e ->
            let s' = CS.CreateEvnt e in
            pure @@ ((s', srep) :: acc)
        | Throw t ->
            let s' = CS.Throw t in
            pure @@ ((s', srep) :: acc)
        | CallProc (p, al) ->
            let s' = CS.CallProc (p, al) in
            pure @@ ((s', srep) :: acc)
        | Iterate (l, p) ->
            (* forall ls proc
             *  is translated to:
             * i = ls
             * loop IterateLoop:
             *   match i with
             *   | Cons cur next =>
             *     CallProc p [cur]
             *     i = next
             *     JumpStmt IterateLoop
             *   | Nil =>
             *   end
             *)
            let lrep = Identifier.get_rep l in
            let%bind l_typ = LoweringUtils.rep_typ lrep in
            let%bind lelm_typ =
              match l_typ with
              | ADT (tname, [ elty ])
                when String.(Identifier.as_string tname = "List") ->
                  pure elty
              | _ -> fail0 ~kind:"Argument to forall must be a list" ?inst:None
            in
            (* Declare a temporary to use as the loop iteration variable. *)
            let ivar = newname (Identifier.as_string l) lrep in
            let loop_preheader =
              [
                (CS.LocalDecl ivar, srep);
                (CS.Bind (ivar, (CS.Var l, lrep)), srep);
              ]
            in
            let loop_label = newname "IterateLoop" srep in
            (* Generate the loop body. *)
            let list_cur =
              newname "list_cur" { lrep with ea_tp = Some lelm_typ }
            in
            let list_next = newname "list_next" lrep in
            let cons_branch =
              Constructor
                (mk_annot_id "Cons" srep, [ Binder list_cur; Binder list_next ])
            in
            let nil_branch = Constructor (mk_annot_id "Nil" srep, []) in
            let cons_body =
              [
                (CS.CallProc (p, [ list_cur ]), srep);
                (CS.Bind (ivar, (CS.Var list_next, lrep)), srep);
                (CS.JumpStmt loop_label, srep);
              ]
            in
            let loop_body =
              [
                ( CS.MatchStmt
                    (ivar, [ (cons_branch, cons_body); (nil_branch, []) ], None),
                  srep );
              ]
            in
            let s' =
              loop_preheader @ [ (CS.Loop (loop_label, loop_body), srep) ]
            in
            pure @@ s' @ acc
        | Bind (i, e) ->
            let%bind stmts' = expr_to_stmts newname e i in
            pure @@ ((CS.LocalDecl i, Identifier.get_rep i) :: (stmts' @ acc))
        | MatchStmt (i, pslist, jopt) ->
            let%bind pslist' =
              mapM
                ~f:(fun (p, ss) ->
                  let%bind ss' = expand_stmts newname ss in
                  pure (p, ss'))
                pslist
            in
            let%bind jopt' =
              match jopt with
              | Some (lbl, ss) ->
                  let%bind ss' = expand_stmts newname ss in
                  pure @@ Some (lbl, ss')
              | None -> pure None
            in
            let s' = CS.MatchStmt (i, pslist', jopt') in
            pure @@ ((s', srep) :: acc)
        | GasStmt g -> pure @@ ((CS.GasStmt g, srep) :: acc)
        | JumpStmt jlbl ->
            let s' = CS.JumpStmt jlbl in
            pure @@ ((s', srep) :: acc))

  (* Go through each library entry and accummulate statements and type declarations. *)
  let clocnv_lib_entries newname lentries =
    foldrM ~init:[]
      ~f:(fun stmt_acc lentry ->
        match lentry with
        | LibVar (i, _, ((_, lrep) as lexp)) ->
            let%bind sts = expr_to_stmts newname lexp i in
            pure (((CS.LibVarDecl i, lrep) :: sts) @ stmt_acc)
        | LibTyp _ ->
            (* Having run `recursion_module` as a pre-pass to closure conversion,
                we can expect that all types are registered in Datatypes.ml already. *)
            pure stmt_acc)
      lentries

  (* Translate external libraries (libtree). *)
  let rec clocnv_libtree newname libt =
    let%bind deps_stmts_list =
      mapM ~f:(fun dep -> clocnv_libtree newname dep) libt.deps
    in
    let deps_stmts = List.concat deps_stmts_list in
    let%bind stmts = clocnv_lib_entries newname libt.libn.lentries in
    pure (deps_stmts @ stmts)

  (* Translate contract constraint.
   * Introduce throw if constraint evaluates to false. *)
  let clocnv_cconstraint newname ((cce, ccrep) as cc) =
    let srep = { ccrep with ea_tp = None } in
    match cce with
    | GasExpr (gc, (Literal (ADTValue (name, _, _)), _))
      when String.equal (Name.as_string name) "True" ->
        pure [ (CS.GasStmt gc, srep) ]
    | _ ->
        let ccres = newname "cconstraint_result" ccrep in
        let resdecl = (CS.LocalDecl ccres, ccrep) in
        let%bind cc' = expr_to_stmts newname cc ccres in

        let false_branch = Constructor (mk_annot_id "False" srep, []) in
        let true_branch = Constructor (mk_annot_id "True" srep, []) in
        let errrep = { srep with ea_tp = Some (PrimType Exception_typ) } in
        let errvar = newname "cconstraint_fail" errrep in
        let errmsg =
          ( CS.Message
              [
                ( "_exception",
                  MLit (StringLit "Contract constraint evaluated to False") );
              ],
            errrep )
        in
        let false_body =
          [
            (CS.LocalDecl errvar, errrep);
            (CS.Bind (errvar, errmsg), srep);
            (CS.Throw (Some errvar), srep);
          ]
        in
        let throw_if_false =
          [
            ( CS.MatchStmt
                (ccres, [ (false_branch, false_body); (true_branch, []) ], None),
              srep );
          ]
        in
        pure ((resdecl :: cc') @ throw_if_false)

  let clocnv_module (cmod : cmodule) rlibs elibs =
    let newname = LoweringUtils.global_newnamer in

    let%bind rlibs_stmts = clocnv_lib_entries newname rlibs in
    let%bind elibs_stmts_list =
      mapM ~f:(fun elib -> clocnv_libtree newname elib) elibs
    in
    let elibs_stmts = List.concat elibs_stmts_list in

    (* Translate contract library. *)
    let%bind clib_stmts =
      match cmod.libs with
      | Some clib -> clocnv_lib_entries newname clib.lentries
      | None -> pure []
    in

    let%bind cconstaint_stmts =
      clocnv_cconstraint newname cmod.contr.cconstraint
    in

    let lib_stmts' = rlibs_stmts @ elibs_stmts @ clib_stmts in

    (* Translate field initialization expressions to statements. *)
    let%bind cfields' =
      mapM cmod.contr.cfields ~f:(fun (i, t, (e, erep)) ->
          let tempname =
            newname (Identifier.as_string i) (Identifier.get_rep i)
          in
          let tempdecl = (CS.LocalDecl tempname, Identifier.get_rep tempname) in
          let%bind e' = expr_to_stmts newname (e, erep) tempname in
          let e'' = (tempdecl :: e') @ [ (CS.Store (i, tempname), erep) ] in
          pure (i, t, e''))
    in

    (* Translate all transitions / procedures. *)
    let%bind ccomps' =
      mapM cmod.contr.ccomps ~f:(fun comp ->
          let%bind comp_body' = expand_stmts newname comp.comp_body in
          pure
            {
              CS.comp_type = comp.comp_type;
              CS.comp_name = comp.comp_name;
              CS.comp_params = comp.comp_params;
              CS.comp_body = comp_body';
            })
    in

    let%bind contr' =
      pure
        {
          CS.cname = cmod.contr.cname;
          CS.cparams = cmod.contr.cparams;
          CS.cconstraint = cconstaint_stmts;
          CS.cfields = cfields';
          CS.ccomps = ccomps';
        }
    in

    let cmod' =
      { CS.smver = cmod.smver; CS.lib_stmts = lib_stmts'; contr = contr' }
    in

    pure cmod'

  (* A wrapper to translate pure expressions. *)
  let clocnv_expr_wrapper rlibs elibs (e, erep) =
    let newname = LoweringUtils.global_newnamer in
    let%bind rlibs_stmts = clocnv_lib_entries newname rlibs.lentries in
    let%bind elibs_stmts_list =
      mapM ~f:(fun elib -> clocnv_libtree newname elib) elibs
    in
    let elibs_stmts = List.concat elibs_stmts_list in
    let retname = newname "expr" erep in
    let%bind stmts = expr_to_stmts newname (e, erep) retname in
    let e_stmts =
      (CS.LocalDecl retname, erep) :: (stmts @ [ (CS.Ret retname, erep) ])
    in
    pure (rlibs_stmts @ elibs_stmts, e_stmts)

  module OutputSyntax = CS
end
