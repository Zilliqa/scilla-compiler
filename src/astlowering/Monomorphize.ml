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

(* 
 * This file contains code to instantiate all type polymorphic functions
 * in a Scilla program. The new AST is a variation of ScillaSyntax which
 * replace TApp and TFun expressions with TFunSel and TFunMap expressions.
 * The AST definition can be found in MonomorphicSyntax.ml.
 *)

open Core_kernel
open! Int.Replace_polymorphic_compare
module Array = BatDynArray
open Scilla_base
module Literal = Literal.FlattenedLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open MonadUtil
open UncurriedSyntax
open Core.Result.Let_syntax
open MonomorphicSyntax

(* Monadic version of List.fold_map *)
let fold_mapM ~f ~init l =
  let%bind acc, l'_rev =
    foldM ~init:(init, [])
      ~f:(fun (accacc, lrevacc) lel ->
        let%bind accacc', lel' = f accacc lel in
        pure (accacc', lel' :: lrevacc))
      l
  in
  pure (acc, List.rev l'_rev)

(* Monadic wrapper around any container's fold (Set, Map etc). *)
(* folder : 'a t -> init:'accum -> f:('accum -> 'a -> 'accum) -> 'accum *)
let wrapM_folder ~folder ~f ~init l =
  let f' acc e = match acc with Error _ -> acc | Ok acc' -> f acc' e in
  folder l ~init:(Ok init) ~f:f'

(* Monad version of fold2 *)
let rec fold2M ~f ~init ls ms ~msg =
  match (ls, ms) with
  | x :: ls', y :: ms' ->
      let%bind res = f init x y in
      fold2M ~f ~init:res ls' ms' ~msg
  | [], [] -> pure init
  | _ -> fail @@ msg ()

(* Translate ScillaSyntax to MonomorphicSyntax. *)
module ScillaCG_Mmph = struct
  module MS = MmphSyntax
  module TU = Uncurried_Syntax.TypeUtilities
  open UncurriedSyntax.Uncurried_Syntax

  (* ******************************************************** *)
  (*  Types used for the type- and control-flow analysis      *)
  (* ******************************************************** *)

  module TypElm = struct
    type t = typ

    let compare = TU.compare

    let equal = TU.equal_typ

    let sexp_of_t = sexp_of_typ

    let t_of_sexp = typ_of_sexp

    let make x = x
  end

  (* Calling context, with the caller's tfa_data index representing context. *)
  module Context = struct
    module T = struct
      type t = int list [@@deriving compare, hash, sexp, equal]
    end

    include T
    include Comparable.Make (T)

    let k = 2

    (* Attach a new context c to ctx.
     * c is added to ctx and the result is cropped for a max of k contexts. *)
    let attach_caller ctx c = fst @@ List.split_n (c :: ctx) k
  end

  (* The context of free variables in a (type) closure. *)
  type context_env = (int * Context.t) list [@@deriving sexp, compare, equal]

  (* We track the flow of TFuns as a pair of tfa_data index (of the TFun)
   * and the context environment of its free type variables. *)
  type tfun_clo_env = int * context_env [@@deriving sexp, compare, equal]

  module TFunCloElm = struct
    type t = tfun_clo_env

    let compare = compare_tfun_clo_env

    let equal = equal_tfun_clo_env

    let sexp_of_t = sexp_of_tfun_clo_env

    let t_of_sexp = tfun_clo_env_of_sexp

    let make x = x
  end

  module TypSet = Set.Make (TypElm)
  module IntSet = Int.Set
  module TFunCloSet = Set.Make (TFunCloElm)

  type rev_ref = ExprRef of expr_annot ref | VarRef of eannot Identifier.t

  let elof_exprref = function
    | ExprRef eref -> pure eref
    | _ -> fail0 "Monomorphize: elof_exprref: Incorrect value"

  let elof_varref = function
    | VarRef v -> pure v
    | _ -> fail0 " Monomorphize: elof_varref: Incorrect value"

  (* Data element propagated in the type-flow analysis. *)
  type tfa_el = {
    (* The TFun expressions that reach a program point or variable. *)
    reaching_tfuns : TFunCloSet.t;
    (* The Fun expressions that reach a program point or variable. *)
    reaching_funs : IntSet.t;
    (* The closed types that reach a type variable, in a given context. *)
    reaching_ctyps : TypSet.t Context.Map.t;
    (* A back reference to who this information belongs to. *)
    elof : rev_ref;
    (* The free type variables at a TFun.
     * Useful in building the context_env for reaching_tfuns. *)
    free_tvars : int list;
  }

  let empty_tfa_el elof =
    {
      reaching_tfuns = TFunCloSet.empty;
      reaching_funs = IntSet.empty;
      reaching_ctyps = Context.Map.empty;
      elof;
      free_tvars = [];
    }

  (* Store for the analysis data. *)
  let tfa_data = Array.create ()

  (* ******************************************************** *)
  (* Add auxiliary annotation to perform type-flow analysis   *)
  (* ******************************************************** *)

  (* Add a new entry to tfa_data and return its index. *)
  let add_tfa_el el =
    let idx = Array.length tfa_data in
    let () = Array.add tfa_data el in
    idx

  (* Get the index of the next element to be inserted. *)
  let next_index () = Array.length tfa_data

  let get_tfa_el idx = tfa_data.(idx)

  let set_tfa_el idx el = tfa_data.(idx) <- el

  (* The initialization environment tracks the following: *)
  (* 1. The variable indices list is used to attach a tfa_el entry
   *   to a (type) variable at its binding point and use that to
   *   attach the same tfa_el entry at the uses. This way, we 
   *   don't have to rewrite the AST with unique names for variables
   *   and type variables.
   * 2. Free type variables. These are attached to TFun expressions
   *   to easily compute context_env for them.
   *)
  type init_env = { var_indices : (string * int) list; free_tvars : int list }

  let empty_init_env = { var_indices = []; free_tvars = [] }

  let resolv_var ienv v =
    match List.Assoc.find ~equal:String.equal ienv.var_indices v with
    | Some i -> pure i
    | None ->
        fail0 ("Monomorphize: initialize_tfa: Unable to resolve variable " ^ v)

  (* Attach tfa_data index to a variable @v already bound in @ienv *)
  let initialize_tfa_var ienv v =
    let vrep = Identifier.get_rep v in
    let%bind i = resolv_var ienv (Identifier.get_id v) in
    pure
    @@ Identifier.mk_id (Identifier.get_id v) { vrep with ea_auxi = Some i }

  (* Attach a new tfa_data index to variable @v and append it to @env *)
  let initialize_tfa_bind ienv v =
    let idx = add_tfa_el (empty_tfa_el (VarRef v)) in
    let ienv' =
      { ienv with var_indices = (Identifier.get_id v, idx) :: ienv.var_indices }
    in
    let%bind v' = initialize_tfa_var ienv' v in
    (* For consistency, let's update v with v' tfa_data. *)
    let () = set_tfa_el idx { (get_tfa_el idx) with elof = VarRef v' } in
    pure (ienv', v')

  (* Attach tfa_data index to tvars in @t bound in @ienv *)
  let initialize_tfa_tvar ienv t =
    let rec go local_bounds t =
      match t with
      | TypeVar v ->
          if Identifier.is_mem_id v local_bounds then pure t
          else
            let%bind v' = initialize_tfa_var ienv v in
            pure (TypeVar v')
      | PolyFun (tv, t') -> go (tv :: local_bounds) t'
      | MapType (kt, vt) ->
          let%bind kt' = go local_bounds kt in
          let%bind vt' = go local_bounds vt in
          pure @@ MapType (kt', vt')
      | FunType (arg_typs, ret_typ) ->
          let%bind arg_typs' = mapM ~f:(go local_bounds) arg_typs in
          let%bind ret_typ' = go local_bounds ret_typ in
          pure @@ FunType (arg_typs', ret_typ')
      | ADT (tname, arg_typs) ->
          let%bind arg_typs' = mapM ~f:(go local_bounds) arg_typs in
          pure @@ ADT (tname, arg_typs')
      | PrimType _ | Unit -> pure t
    in
    go [] t

  (* Sets up a tfa_index for each bound variable and returns new env. *)
  let initialize_tfa_match_bind sp =
    let initialize_tfa_match_bind_base ienv = function
      | Wildcard -> pure (ienv, Wildcard)
      | Binder b ->
          let%bind ienv', b' = initialize_tfa_bind ienv b in
          pure (ienv', Binder b')
    in
    match sp with
    | Any base ->
        let%bind new_binds, base' =
          initialize_tfa_match_bind_base empty_init_env base
        in
        pure (new_binds, Any base')
    | Constructor (cname, basel) ->
        let%bind new_binds, basel'_rev =
          fold_mapM ~init:empty_init_env
            ~f:(fun accenv base -> initialize_tfa_match_bind_base accenv base)
            basel
        in
        pure (new_binds, Constructor (cname, List.rev basel'_rev))

  (* Attach an auxiliary annotation for expr, its constituent exprs and vars. *)
  let rec initialize_tfa_expr (ienv : init_env) (e, annot) =
    let%bind e' =
      match e with
      | Literal _ | JumpExpr _ -> pure e
      | Var v ->
          let%bind v' = initialize_tfa_var ienv v in
          pure (Var v')
      | Message comps ->
          let%bind pl' =
            mapM
              ~f:(function
                | s, MLit l -> pure (s, MLit l)
                | s, MVar v ->
                    let%bind v' = initialize_tfa_var ienv v in
                    pure (s, MVar v'))
              comps
          in
          pure (Message pl')
      | App (f, alist) ->
          let%bind f' = initialize_tfa_var ienv f in
          let%bind alist' = mapM ~f:(initialize_tfa_var ienv) alist in
          pure (App (f', alist'))
      | Constr (cname, tlist, vlist) ->
          let%bind tlist' = mapM ~f:(initialize_tfa_tvar ienv) tlist in
          let%bind vlist' = mapM ~f:(initialize_tfa_var ienv) vlist in
          pure @@ Constr (cname, tlist', vlist')
      | Builtin (b, vlist) ->
          let%bind vlist' = mapM ~f:(initialize_tfa_var ienv) vlist in
          pure @@ Builtin (b, vlist')
      | MatchExpr (p, blist, jopt) ->
          let%bind p' = initialize_tfa_var ienv p in
          let%bind blist' =
            mapM
              ~f:(fun (sp, e) ->
                let%bind new_binds, sp' = initialize_tfa_match_bind sp in
                let ienv' =
                  {
                    ienv with
                    var_indices = new_binds.var_indices @ ienv.var_indices;
                  }
                in
                let%bind e' = initialize_tfa_expr ienv' e in
                pure (sp', e'))
              blist
          in
          let%bind jopt' =
            match jopt with
            | None -> pure None
            | Some (l, je) ->
                let%bind e' = initialize_tfa_expr ienv je in
                pure (Some (l, e'))
          in
          pure @@ MatchExpr (p', blist', jopt')
      | Fun (atl, sube) ->
          let%bind ienv', atl'_rev =
            fold_mapM ~init:ienv
              ~f:(fun accenv (v, t) ->
                let%bind t' = initialize_tfa_tvar accenv t in
                let%bind accenv', v' = initialize_tfa_bind accenv v in
                pure (accenv', (v', t')))
              atl
          in
          let%bind sube' = initialize_tfa_expr ienv' sube in
          pure @@ Fun (List.rev atl'_rev, sube')
      | Fixpoint (v, t, sube) ->
          let%bind t' = initialize_tfa_tvar ienv t in
          let%bind ienv', v' = initialize_tfa_bind ienv v in
          let%bind sube' = initialize_tfa_expr ienv' sube in
          pure (Fixpoint (v', t', sube'))
      | Let (x, xtopt, lhs, rhs) ->
          let%bind lhs' = initialize_tfa_expr ienv lhs in
          let%bind xopt' =
            match xtopt with
            | Some xt ->
                let%bind xt' = initialize_tfa_tvar ienv xt in
                pure (Some xt')
            | None -> pure None
          in
          let%bind ienv', x' = initialize_tfa_bind ienv x in
          let%bind rhs' = initialize_tfa_expr ienv' rhs in
          pure (Let (x', xopt', lhs', rhs'))
      | TFun (tv, sube) ->
          let%bind ienv', tv' = initialize_tfa_bind ienv tv in
          let%bind tv_index = resolv_var ienv' (Identifier.get_id tv') in
          (* For everything inside this TFun, tv is a free variable. *)
          let ienv'' =
            { ienv' with free_tvars = tv_index :: ienv'.free_tvars }
          in
          let%bind sube' = initialize_tfa_expr ienv'' sube in
          pure (TFun (tv', sube'))
      | TApp (tf, targs) ->
          let%bind tf' = initialize_tfa_var ienv tf in
          let%bind targs' = mapM ~f:(initialize_tfa_tvar ienv) targs in
          pure (TApp (tf', targs'))
    in
    (* Add auxiliary annotation for the new expression. *)
    let idx = next_index () in
    let annot' = { annot with ea_auxi = Some idx } in
    let ea = (e', annot') in
    let _ = add_tfa_el (empty_tfa_el (ExprRef (ref ea))) in
    pure ea

  (* Walk through statement list and add all TApps. *)
  let rec initialize_tfa_stmts (ienv : init_env) stmts =
    match stmts with
    | [] -> pure []
    (* We leave statement annotations as-is, but annotate variables. *)
    | (s, annot) :: sts ->
        let%bind s', ienv' =
          match s with
          | AcceptPayment | JumpStmt _ -> pure (s, ienv)
          | Bind (x, e) ->
              let%bind e' = initialize_tfa_expr ienv e in
              let%bind ienv', x' = initialize_tfa_bind ienv x in
              pure (Bind (x', e'), ienv')
          | Load (x, f) ->
              let%bind ienv', x' = initialize_tfa_bind ienv x in
              pure (Load (x', f), ienv')
          | Store (f, x) ->
              let%bind x' = initialize_tfa_var ienv x in
              pure @@ (Store (f, x'), ienv)
          | MapGet (x, m, indices, exists) ->
              let%bind ienv', x' = initialize_tfa_bind ienv x in
              let%bind indices' = mapM ~f:(initialize_tfa_var ienv) indices in
              pure (MapGet (x', m, indices', exists), ienv')
          | MapUpdate (m, indices, vopt) ->
              let%bind indices' = mapM ~f:(initialize_tfa_var ienv) indices in
              let%bind vopt' =
                match vopt with
                | None -> pure None
                | Some v ->
                    let%bind v' = initialize_tfa_var ienv v in
                    pure (Some v')
              in
              pure (MapUpdate (m, indices', vopt'), ienv)
          | ReadFromBC (x, bs) ->
              let%bind x' = initialize_tfa_var ienv x in
              pure (ReadFromBC (x', bs), ienv)
          | Iterate (l, p) ->
              let%bind l' = initialize_tfa_var ienv l in
              pure (Iterate (l', p), ienv)
          | CallProc (p, args) ->
              let%bind args' = mapM ~f:(initialize_tfa_var ienv) args in
              pure (CallProc (p, args'), ienv)
          | SendMsgs m ->
              let%bind m' = initialize_tfa_var ienv m in
              pure (SendMsgs m', ienv)
          | CreateEvnt m ->
              let%bind m' = initialize_tfa_var ienv m in
              pure (CreateEvnt m', ienv)
          | Throw mopt ->
              let%bind mopt' =
                match mopt with
                | None -> pure None
                | Some m ->
                    let%bind m' = initialize_tfa_var ienv m in
                    pure (Some m')
              in
              pure (Throw mopt', ienv)
          | MatchStmt (p, blist, jopt) ->
              let%bind p' = initialize_tfa_var ienv p in
              let%bind blist' =
                mapM
                  ~f:(fun (sp, e) ->
                    let%bind new_binds, sp' = initialize_tfa_match_bind sp in
                    let ienv' =
                      {
                        ienv with
                        var_indices = new_binds.var_indices @ ienv.var_indices;
                      }
                    in
                    let%bind e' = initialize_tfa_stmts ienv' e in
                    pure (sp', e'))
                  blist
              in
              let%bind jopt' =
                match jopt with
                | None -> pure None
                | Some (l, je) ->
                    let%bind e' = initialize_tfa_stmts ienv je in
                    pure (Some (l, e'))
              in
              pure (MatchStmt (p', blist', jopt'), ienv)
        in
        let%bind sts' = initialize_tfa_stmts ienv' sts in
        pure @@ ((s', annot) :: sts')

  (* Walk through entire module, initializing AST nodes to a TFA element. *)
  let initialize_tfa_module (cmod : cmodule) rlibs elibs =
    (* Function to anaylze library entries. *)
    let initialize_tfa_lib_entries env lentries =
      fold_mapM
        ~f:(fun accenv lentry ->
          match lentry with
          | LibVar (x, topt, lexp) ->
              let%bind lexp' = initialize_tfa_expr accenv lexp in
              let%bind accenv', x' = initialize_tfa_bind accenv x in
              let%bind topt' =
                match topt with
                | Some t ->
                    let%bind t' = initialize_tfa_tvar accenv t in
                    pure (Some t')
                | None -> pure None
              in
              pure (accenv', LibVar (x', topt', lexp'))
          | LibTyp _ -> pure (accenv, lentry))
        ~init:env lentries
    in

    (* Intialize in recursion library entries. *)
    let%bind rlib_env, rlibs' =
      initialize_tfa_lib_entries empty_init_env rlibs
    in

    (* Function to initialize in external and contract libraries. *)
    let initialize_tfa_library env lib =
      initialize_tfa_lib_entries env lib.lentries
    in

    (* Initialize in full library tree. *)
    let rec initialize_tfa_libtree env lib =
      (* first analyze all the dependent libraries. *)
      let%bind env', deps' =
        fold_mapM
          ~f:(fun accenv lib -> initialize_tfa_libtree accenv lib)
          ~init:env lib.deps
      in
      (* intialize in this library. *)
      let%bind env'', lentris' = initialize_tfa_library env' lib.libn in
      pure
        (env'', { libn = { lib.libn with lentries = lentris' }; deps = deps' })
    in
    let%bind elibs_env, elibs' =
      fold_mapM
        ~f:(fun accenv libt -> initialize_tfa_libtree accenv libt)
        ~init:rlib_env elibs
    in
    let%bind libs_env, cmod_libs =
      match cmod.libs with
      | Some lib ->
          let%bind libs_env, lentries' = initialize_tfa_library elibs_env lib in
          pure
            ( libs_env,
              { cmod with libs = Some { lib with lentries = lentries' } } )
      | None -> pure (elibs_env, cmod)
    in

    (* Initialize in fields. *)
    let%bind cmod_cfields =
      let%bind cfields' =
        mapM
          ~f:(fun (f, t, fexp) ->
            let%bind t' = initialize_tfa_tvar libs_env t in
            let%bind fexp' = initialize_tfa_expr libs_env fexp in
            pure (f, t', fexp'))
          cmod_libs.contr.cfields
      in
      pure
        { cmod_libs with contr = { cmod_libs.contr with cfields = cfields' } }
    in

    (* Initialize in contract parameters. Note: These are of no interest
     * to us. But since they are accessed the same way as any other bound
     * variables in transitions / procedures, we must have a tfa_el annotated
     * for them, for simpler uniform access. *)
    let%bind cparams_env, cmod_cparams =
      let%bind cparams_env, cparams' =
        fold_mapM ~init:libs_env
          ~f:(fun accenv (v, t) ->
            let%bind accenv', v' = initialize_tfa_bind accenv v in
            let%bind t' = initialize_tfa_tvar accenv t in
            pure (accenv', (v', t')))
          cmod_cfields.contr.cparams
      in
      pure
        ( cparams_env,
          {
            cmod_cfields with
            contr = { cmod_cfields.contr with cparams = cparams' };
          } )
    in

    (* Initialize in components. *)
    let%bind cmod_comps =
      let%bind ccomps' =
        mapM
          ~f:(fun comp ->
            let%bind env', comp_params' =
              fold_mapM ~init:cparams_env
                ~f:(fun accenv (v, t) ->
                  let%bind accenv', v' = initialize_tfa_bind accenv v in
                  let%bind t' = initialize_tfa_tvar accenv t in
                  pure (accenv', (v', t')))
                comp.comp_params
            in
            let%bind stmts' = initialize_tfa_stmts env' comp.comp_body in
            pure { comp with comp_body = stmts'; comp_params = comp_params' })
          cmod_cparams.contr.ccomps
      in
      pure
        {
          cmod_cparams with
          contr = { cmod_cparams.contr with ccomps = ccomps' };
        }
    in
    pure (cmod_comps, rlibs', elibs')

  (* ******************************************************** *)
  (* ******* Type-flow + control-flow analysis ************** *)
  (* ******************************************************** *)

  (* The analysis is a context-sensitive control-flow analysis over TFuns,
   * which is a control-flow-analysis, but over type abstractions
   * instead of value abstractions. The analysis also does the usual
   * control-flow analysis, but without context-sensitivity.
   * References:
      1. Principles of Program Analysis by Flemming Nielson, Hanne R. Nielson, Chris Hankin.
      2. An Efficient Type- and Control-Flow Analysis for System F - Adsit and Fluet.
   *)

  let get_tfa_idx_annot annot =
    match annot.ea_auxi with
    | Some i -> pure i
    | None ->
        fail1 "Monomorphize: annot_idx: internal error: No tfa_data index"
          annot.ea_loc

  (* Fetch the tfa_data element corresponding to an annotation. *)
  let get_tfa_el_annot annot =
    let%bind idx = get_tfa_idx_annot annot in
    pure @@ get_tfa_el idx

  (* Set the tfa_data element corresponding to an annotation. *)
  let set_tfa_el_annot annot el =
    let%bind idx = get_tfa_idx_annot annot in
    pure @@ set_tfa_el idx el

  (* Implements the inclusion constraint. i.e., 
   * all flow information in src is included in dest,
   * and the result, along with indication of a change is returned. *)
  let include_in dest src =
    let include_contexted_typs dest src =
      Context.Map.merge dest src ~f:(fun ~key ->
          let _ = key in
          function
          | `Left v | `Right v -> Some v
          | `Both (v1, v2) -> Some (TypSet.union v1 v2))
    in
    let dest' =
      {
        reaching_tfuns = TFunCloSet.union dest.reaching_tfuns src.reaching_tfuns;
        reaching_funs = IntSet.union dest.reaching_funs src.reaching_funs;
        reaching_ctyps =
          include_contexted_typs dest.reaching_ctyps src.reaching_ctyps;
        elof = dest.elof;
        free_tvars = dest.free_tvars;
      }
    in
    (* TODO: Make this faster. *)
    ( dest',
      (not @@ TFunCloSet.equal dest'.reaching_tfuns dest.reaching_tfuns)
      || (not @@ IntSet.equal dest'.reaching_funs dest.reaching_funs)
      || not
         @@ Context.Map.equal TypSet.equal dest'.reaching_ctyps
              dest.reaching_ctyps )

  (* A wrapper around include_in to directly update tfa_data. *)
  let include_in_annot dest_annot src_annot =
    let%bind src_el = get_tfa_el_annot src_annot in
    let%bind dest_el = get_tfa_el_annot dest_annot in
    let new_dest_el, changed = include_in dest_el src_el in
    let%bind () = set_tfa_el_annot dest_annot new_dest_el in
    pure changed

  (* Input: A list "l" of sets "s1" ... "sn" of types.
   * Output: The n-ary cartesian product of these sets.
   * http://gallium.inria.fr/blog/on-the-nary-cartesian-product/ *)
  let rec n_cartesian_product = function
    | [] -> []
    | h :: t ->
        let rest = n_cartesian_product t in
        List.concat
          (List.map ~f:(fun i -> List.map ~f:(fun r -> i :: r) rest) h)

  type tfa_env = {
    (* The contexts of currently free type variables. *)
    ctx_env : context_env;
    (* The current calling context. *)
    cctx : Context.t;
  }

  let empty_tfa_env = { ctx_env = []; cctx = [] }

  (* Analyze expr and return if any data-flow information was updated. *)
  let rec analyze_tfa_expr (env : tfa_env) (e, e_annot) =
    match e with
    | Literal _ | JumpExpr _ | Message _ | Builtin _ -> pure false
    | Var v ->
        (* Copy over what reaches v to e *)
        include_in_annot e_annot (Identifier.get_rep v)
    | App (f, plist) ->
        (* For every function that reaches f, apply alist and analyze. *)
        let%bind f_el = get_tfa_el_annot (Identifier.get_rep f) in
        wrapM_folder ~folder:IntSet.fold ~init:false f_el.reaching_funs
          ~f:(fun changed f_idx ->
            (* For each argument a, include a's tfa data in 
             * that of f's corresponding formal parameter. *)
            let%bind eref = elof_exprref (get_tfa_el f_idx).elof in
            match !eref with
            | Fun (atlist, ((_, sub_annot) as sube)), _ ->
                let%bind changed' =
                  fold2M ~init:changed atlist plist
                    ~f:(fun changed (a, _) p ->
                      let%bind changed' =
                        include_in_annot (Identifier.get_rep a)
                          (Identifier.get_rep p)
                      in
                      pure (changed || changed'))
                    ~msg:(fun () ->
                      (* TODO: Do not process when lengths differ.
                       * Because of flow through ADTs and pattern matches,
                       * we can have functions with different types reaching. *)
                      ErrorUtils.mk_error1
                        "Monomorphize: analyze_tfa_expr: internal error: \
                         Parameter length mistmatch"
                        (Identifier.get_rep f).ea_loc)
                in
                (* Analyze the subexpression and note any changes. *)
                let%bind changed'' = analyze_tfa_expr env sube in
                (* Include sub-expressions data-flow info in this one. *)
                let%bind changed''' = include_in_annot e_annot sub_annot in
                pure (changed' || changed'' || changed''')
            | _ ->
                fail1
                  "Monomorphize: analyze_tfa_expr: internal error: Expected \
                   Fun expr"
                  (Identifier.get_rep f).ea_loc)
    | Constr (_, _, vlist) ->
        (* Copy over every argument's reachables to e. *)
        let%bind changed =
          foldM vlist ~init:false ~f:(fun changed v ->
              let%bind changed' =
                include_in_annot e_annot (Identifier.get_rep v)
              in
              pure (changed || changed'))
        in
        pure changed
    | MatchExpr (p, blist, jopt) ->
        let%bind changed =
          foldM blist ~init:false
            ~f:(fun changed (pat, ((_, subannot) as sube)) ->
              let patbounds = get_spattern_bounds pat in
              (* Include reachables in p in each pattern bound identifier. *)
              let%bind changed' =
                foldM patbounds ~init:changed ~f:(fun changed b ->
                    let%bind changed' =
                      include_in_annot (Identifier.get_rep b)
                        (Identifier.get_rep p)
                    in
                    pure (changed || changed'))
              in
              (* Analyze sub. *)
              let%bind changed'' = analyze_tfa_expr env sube in
              (* Include sub expressions reachables in e. *)
              let%bind changed''' = include_in_annot e_annot subannot in
              pure (changed' || changed'' || changed'''))
        in
        (* Analyze jopt and include its reachables in e. *)
        let%bind changed' =
          match jopt with
          | Some (_, ((_, jannot) as jexpr)) ->
              let%bind changed = analyze_tfa_expr env jexpr in
              let%bind changed' = include_in_annot e_annot jannot in
              pure (changed || changed')
          | None -> pure false
        in
        pure (changed || changed')
    | Fun _ ->
        (* Include e in itself and that's it.
         * The sub expression is analyzed during application. *)
        let%bind e_idx = get_tfa_idx_annot e_annot in
        let e_el = get_tfa_el e_idx in
        let changed = not @@ IntSet.mem e_el.reaching_funs e_idx in
        let e_el' =
          { e_el with reaching_funs = IntSet.add e_el.reaching_funs e_idx }
        in
        let () = set_tfa_el e_idx e_el' in
        pure changed
    | Fixpoint (v, _, ((_, subannot) as sube)) ->
        let%bind changed = analyze_tfa_expr env sube in
        (* Include sube's reachables in v and analyze sube. *)
        let%bind changed' = include_in_annot (Identifier.get_rep v) subannot in
        (* Include sube's reachables in e as well. *)
        let%bind changed'' = include_in_annot e_annot subannot in
        pure (changed || changed' || changed'')
    | Let (x, _, ((_, lannot) as lhs), ((_, rannot) as rhs)) ->
        let%bind changed = analyze_tfa_expr env lhs in
        (* Copy over reaches of lhs to x. *)
        let%bind changed' = include_in_annot (Identifier.get_rep x) lannot in
        let%bind changed'' = analyze_tfa_expr env rhs in
        (* Copy over rhs's reachables to e. *)
        let%bind changed''' = include_in_annot e_annot rannot in
        pure (changed || changed' || changed'' || changed''')
    | TFun _ ->
        (* Include e in itself, but with the right
         * context_env for its free type variables. *)
        let%bind e_idx = get_tfa_idx_annot e_annot in
        let e_el = get_tfa_el e_idx in
        let%bind ce =
          mapM e_el.free_tvars ~f:(fun fv_idx ->
              match List.Assoc.find env.ctx_env ~equal:( = ) fv_idx with
              | Some ctx -> pure (fv_idx, ctx)
              | None ->
                  let%bind i = elof_varref (get_tfa_el fv_idx).elof in
                  fail1
                    (sprintf
                       "Monomorphize: internal error: Couldn't find %s in \
                        current context environment"
                       (Identifier.get_id i))
                    e_annot.ea_loc)
        in
        let e_ce = (e_idx, ce) in
        let changed = not @@ TFunCloSet.mem e_el.reaching_tfuns e_ce in
        let e_el' =
          { e_el with reaching_tfuns = TFunCloSet.add e_el.reaching_tfuns e_ce }
        in
        let () = set_tfa_el e_idx e_el' in
        pure changed
    | TApp (tf, targs) ->
        (* For each free type variable in the current context,
         * gather the types that may flow into it. *)
        let%bind ftv_specls =
          mapM env.ctx_env ~f:(fun (tvi, ctx) ->
              let el = get_tfa_el tvi in
              let%bind tv = elof_varref el.elof in
              match Context.Map.find el.reaching_ctyps ctx with
              | Some tys -> pure (tv, tys)
              | None -> pure (tv, TypSet.empty))
        in
        (* Substitute the free type variables in each targ
         * with all combinations possible, for each to yeild a set. *)
        let%bind targs_specls =
          mapM targs ~f:(fun targ ->
              (* If targ is already a closed type, no substitutions required. *)
              if TU.is_closed_type targ then pure (TypSet.add TypSet.empty targ)
              else
                let ftv_targ = TU.free_tvars targ in
                let ftv_specls' =
                  List.filter ftv_specls ~f:(fun (ftv, _) ->
                      (* We want only those ftv_specls that are free in targ. *)
                      List.mem ftv_targ ftv ~equal:Identifier.equal)
                in
                (* Set -> List *)
                let ftv_specls'' =
                  List.map ftv_specls' ~f:(fun (tv, ts) ->
                      List.map (TypSet.to_list ts) ~f:(fun ts' -> (tv, ts')))
                in
                (* Compute all possible specializations. *)
                let specls = n_cartesian_product ftv_specls'' in
                (* Substitute each specialization in targ to obtain
                 * the specialized arg. *)
                let specls' =
                  List.filter_map specls ~f:(fun specl ->
                      let specl' = TU.subst_types_in_type specl targ in
                      (* We don't want to propagate open types. *)
                      if TU.is_closed_type specl' then Some specl' else None)
                in
                pure @@ TypSet.of_list specls')
        in
        let%bind e_idx = get_tfa_idx_annot e_annot in
        let env' = { env with cctx = Context.attach_caller env.cctx e_idx } in
        (* We now have all specializations (yet) of targ.
         * Propagate them to each possible callee in the right ctx. *)
        let%bind tf_el = get_tfa_el_annot (Identifier.get_rep tf) in
        wrapM_folder ~folder:TFunCloSet.fold ~init:false tf_el.reaching_tfuns
          ~f:(fun changed (tf_idx, ce) ->
            let%bind tf_expr_ref = elof_exprref (get_tfa_el tf_idx).elof in
            let%bind changed', _, _, sub_annot =
              foldM
                ~init:(changed, ce, tf_expr_ref, Identifier.get_rep tf)
                targs_specls
                ~f:(fun (changed, ce, tf_expr_ref, _) targ ->
                  match !tf_expr_ref with
                  | TFun (ta, ((_, sub_annot) as sube)), _ ->
                      (* Include targ into ta, in the context env'.cctx.  *)
                      let%bind ta_idx =
                        get_tfa_idx_annot (Identifier.get_rep ta)
                      in
                      let ta_el = get_tfa_el ta_idx in
                      let reaching_ctyps', changed' =
                        match
                          Context.Map.find ta_el.reaching_ctyps env'.cctx
                        with
                        | Some ctyps ->
                            let ctyps' = TypSet.union ctyps targ in
                            ( Context.Map.set ta_el.reaching_ctyps
                                ~key:env'.cctx ~data:ctyps',
                              not @@ TypSet.equal ctyps' ctyps )
                        | None ->
                            ( Context.Map.set ta_el.reaching_ctyps
                                ~key:env'.cctx ~data:targ,
                              true )
                      in
                      let ta_el' =
                        { ta_el with reaching_ctyps = reaching_ctyps' }
                      in
                      let%bind () =
                        set_tfa_el_annot (Identifier.get_rep ta) ta_el'
                      in
                      (* Append ta, in the current context, to the context environment. *)
                      let env'' =
                        { env' with ctx_env = (ta_idx, env'.cctx) :: ce }
                      in
                      (* Analyze the subexpression and note any changes. *)
                      let%bind changed'' = analyze_tfa_expr env'' sube in
                      pure
                        ( changed || changed' || changed'',
                          env''.ctx_env,
                          ref sube,
                          sub_annot )
                  | _ ->
                      (* TODO: Like in App, we can have a mismatch in length of arguments
                       * when there's a flow through ADTs. So check this at the start and ignore. *)
                      fail1
                        "Monomorphize: analyze_tfa_expr: internal error: \
                         Expected TFun expr"
                        (Identifier.get_rep tf).ea_loc)
            in
            (* Include the last sub-expressions (application) data-flow info in this one. *)
            let%bind changed'' = include_in_annot e_annot sub_annot in
            pure (changed' || changed''))

  (* ******************************************************** *)
  (* ************** Pretty print analysis ******************* *)
  (* ******************************************************** *)

  (* Print given context elements (TApps) along with its tfa_data index and location.
   * This will serve as a reference table for all tfa_data indices printed. *)
  let pp_ctx_elms ctx_elm_list =
    let pp_ctx_elm ctx_elm =
      let%bind eref = elof_exprref (get_tfa_el ctx_elm).elof in
      match !eref with
      | TApp (tv, tys), ea ->
          let tyss = String.concat ~sep:" " (List.map tys ~f:pp_typ) in
          pure @@ Int.to_string ctx_elm ^ ": ["
          ^ ErrorUtils.get_loc_str ea.ea_loc
          ^ "] @" ^ Identifier.get_id tv ^ " " ^ tyss
      | _, ea ->
          fail1 "Monomorphize: pp_tapp: internal error: Expected TApp" ea.ea_loc
    in
    let%bind ctx_elm_s = mapM ctx_elm_list ~f:pp_ctx_elm in
    pure @@ String.concat ~sep:"\n" ctx_elm_s

  (* Gather the indices of all TApp expressions. *)
  let rec gather_ctx_elms_expr (e, e_annot) =
    match e with
    | Literal _ | JumpExpr _ | Message _ | Builtin _ | Var _ | App _ | Constr _
      ->
        pure []
    | MatchExpr (_, blist, jopt) -> (
        let%bind subs' =
          foldrM blist ~init:[] ~f:(fun acc (_, sube) ->
              let%bind subs = gather_ctx_elms_expr sube in
              pure (List.rev subs @ acc))
        in
        let subs = List.rev subs' in
        match jopt with
        | Some (_, je) ->
            let%bind js = gather_ctx_elms_expr je in
            pure (subs @ js)
        | None -> pure subs )
    | Fun (_, sube) | Fixpoint (_, _, sube) | TFun (_, sube) ->
        gather_ctx_elms_expr sube
    | Let (_, _, lhs, rhs) ->
        let%bind lhss = gather_ctx_elms_expr lhs in
        let%bind rhss = gather_ctx_elms_expr rhs in
        pure (lhss @ rhss)
    | TApp _ ->
        let%bind i = get_tfa_idx_annot e_annot in
        pure [ i ]

  let rec pp_tfa_expr (e, _) =
    match e with
    | Literal _ | JumpExpr _ | Message _ | Builtin _ | Var _ | App _ | Constr _
    | TApp _ ->
        pure ""
    | MatchExpr (_, blist, jopt) -> (
        let%bind subs =
          foldM blist ~init:"" ~f:(fun acc (_, sube) ->
              let%bind subs = pp_tfa_expr sube in
              pure (acc ^ subs))
        in
        match jopt with
        | Some (_, je) ->
            let%bind js = pp_tfa_expr je in
            pure (subs ^ js)
        | None -> pure subs )
    | Fun (_, sube) | Fixpoint (_, _, sube) -> pp_tfa_expr sube
    | Let (_, _, lhs, rhs) ->
        let%bind lhss = pp_tfa_expr lhs in
        let%bind rhss = pp_tfa_expr rhs in
        pure (lhss ^ rhss)
    | TFun (tv, sube) ->
        let%bind tv_el = get_tfa_el_annot (Identifier.get_rep tv) in
        let ctx_ctyps = Context.Map.to_alist tv_el.reaching_ctyps in
        let ctx_ctyps' =
          String.concat ~sep:"\n"
            (List.map ctx_ctyps ~f:(fun (ctx, tys) ->
                 let tys' = TypSet.to_list tys in
                 "Context: ["
                 ^ String.concat ~sep:";" (List.map ctx ~f:Int.to_string)
                 ^ "]: Types: ["
                 ^ String.concat ~sep:";" (List.map tys' ~f:pp_typ)
                 ^ "]"))
        in
        let%bind subes = pp_tfa_expr sube in
        pure
        @@ sprintf "[%s] %s: %s\n"
             (ErrorUtils.get_loc_str (Identifier.get_rep tv).ea_loc)
             (Identifier.get_id tv) ctx_ctyps'
        ^ subes

  let pp_tfa_expr_wrapper e =
    let%bind ctx_elms = gather_ctx_elms_expr e in
    let%bind ctx_elms' = pp_ctx_elms ctx_elms in
    let%bind e' = pp_tfa_expr e in
    pure @@ "Monomorphize TFA: Calling context table:\n" ^ ctx_elms'
    ^ "\nAnalysis results:\n" ^ e' ^ "\n"

  (* ******************************************************** *)
  (* ************** Monomorphization  *********************** *)
  (* ******************************************************** *)

  (* Walk through "e" and replace TFun and TApp with TFunMap and TFunSel respectively. *)
  let rec monomorphize_expr (e, rep) =
    match e with
    | Literal l -> pure (MS.Literal l, rep)
    | Var v -> pure (MS.Var v, rep)
    | Message m ->
        let m' = List.map ~f:(fun (s, p) -> (s, p)) m in
        pure (MS.Message m', rep)
    | App (a, l) -> pure (MS.App (a, l), rep)
    | Constr (s, tl, il) -> pure (MS.Constr (s, tl, il), rep)
    | Builtin (i, il) -> pure (MS.Builtin (i, il), rep)
    | Fixpoint (i, t, body) ->
        let%bind body' = monomorphize_expr body in
        pure (MS.Fixpoint (i, t, body'), rep)
    | Fun (args, body) ->
        let%bind body' = monomorphize_expr body in
        pure (MS.Fun (args, body'), rep)
    | Let (i, topt, lhs, rhs) ->
        let%bind lhs' = monomorphize_expr lhs in
        let%bind rhs' = monomorphize_expr rhs in
        pure (MS.Let (i, topt, lhs', rhs'), rep)
    | JumpExpr l -> pure (MS.JumpExpr l, rep)
    | MatchExpr (i, clauses, join_clause_opt) ->
        let%bind clauses' =
          mapM
            ~f:(fun (p, cexp) ->
              let%bind cexp' = monomorphize_expr cexp in
              pure (p, cexp'))
            clauses
        in
        let%bind join_clause_opt' =
          match join_clause_opt with
          | Some (l, join_clause) ->
              let%bind join_clause' = monomorphize_expr join_clause in
              pure (Some (l, join_clause'))
          | None -> pure None
        in
        pure (MS.MatchExpr (i, clauses', join_clause_opt'), rep)
    | TFun _ ->
        (* TODO *)
        pure (MS.TFunMap [], rep)
    | TApp (i, tl) -> pure (MS.TFunSel (i, tl), rep)

  (* Walk through statement list and replace TFun and TApp with TFunMap and TFunSel respectively. *)
  let rec monomorphize_stmts stmts : (MS.stmt_annot list, 'a) result =
    match stmts with
    | [] -> pure []
    | (s, srep) :: sts -> (
        let%bind sts' = monomorphize_stmts sts in
        match s with
        | Load (x, m) ->
            let s' = MS.Load (x, m) in
            pure ((s', srep) :: sts')
        | Store (m, i) ->
            let s' = MS.Store (m, i) in
            pure ((s', srep) :: sts')
        | MapUpdate (i, il, io) ->
            let s' = MS.MapUpdate (i, il, io) in
            pure ((s', srep) :: sts')
        | MapGet (i, i', il, b) ->
            let s' = MS.MapGet (i, i', il, b) in
            pure ((s', srep) :: sts')
        | ReadFromBC (i, s) ->
            let s' = MS.ReadFromBC (i, s) in
            pure ((s', srep) :: sts')
        | AcceptPayment ->
            let s' = MS.AcceptPayment in
            pure ((s', srep) :: sts')
        | SendMsgs m ->
            let s' = MS.SendMsgs m in
            pure ((s', srep) :: sts')
        | CreateEvnt e ->
            let s' = MS.CreateEvnt e in
            pure ((s', srep) :: sts')
        | Throw t ->
            let s' = MS.Throw t in
            pure ((s', srep) :: sts')
        | CallProc (p, al) ->
            let s' = MS.CallProc (p, al) in
            pure ((s', srep) :: sts')
        | Iterate (l, p) ->
            let s' = MS.Iterate (l, p) in
            pure ((s', srep) :: sts')
        | Bind (i, e) ->
            let%bind e' = monomorphize_expr e in
            let s' = MS.Bind (i, e') in
            pure ((s', srep) :: sts')
        | JumpStmt l ->
            let s' = MS.JumpStmt l in
            pure ((s', srep) :: sts')
        | MatchStmt (i, pslist, join_clause_opt) ->
            let%bind pslist' =
              mapM
                ~f:(fun (p, ss) ->
                  let%bind ss' = monomorphize_stmts ss in
                  pure (p, ss'))
                pslist
            in
            let%bind join_clause_opt' =
              match join_clause_opt with
              | Some (l, join_clause) ->
                  let%bind join_clause' = monomorphize_stmts join_clause in
                  pure (Some (l, join_clause'))
              | None -> pure None
            in
            let s' = MS.MatchStmt (i, pslist', join_clause_opt') in
            pure ((s', srep) :: sts') )

  (* Walk through entire module and replace TFun and TApp with TFunMap and TFunSel respectively. *)
  let monomorphize_module (cmod : cmodule) rlibs elibs =
    (* Analyze and find all possible instantiations. *)
    let%bind _cmod', _rlibs', _elibs' =
      initialize_tfa_module cmod rlibs elibs
    in

    (* Function to monomorphize library entries. *)
    let monomorphize_lib_entries lentries =
      mapM
        ~f:(fun lentry ->
          match lentry with
          | LibVar (i, topt, lexp) ->
              let%bind lexp' = monomorphize_expr lexp in
              pure (MS.LibVar (i, topt, lexp'))
          | LibTyp (i, tdefs) ->
              let tdefs' =
                List.map
                  ~f:(fun (t : ctr_def) ->
                    { MS.cname = t.cname; MS.c_arg_types = t.c_arg_types })
                  tdefs
              in
              pure (MS.LibTyp (i, tdefs')))
        lentries
    in

    (* Translate recursion libs. *)
    let%bind rlibs' = monomorphize_lib_entries rlibs in

    (* Function to monomorphize a library. *)
    let monomorphize_lib lib =
      let%bind lentries' = monomorphize_lib_entries lib.lentries in
      let lib' = { MS.lname = lib.lname; lentries = lentries' } in
      pure lib'
    in

    (* Monomorphize the library tree. *)
    let rec monomorphize_libtree libt =
      let%bind deps' =
        mapM ~f:(fun dep -> monomorphize_libtree dep) libt.deps
      in
      let%bind libn' = monomorphize_lib libt.libn in
      let libt' = { MS.libn = libn'; MS.deps = deps' } in
      pure libt'
    in
    let%bind elibs' = mapM ~f:(fun elib -> monomorphize_libtree elib) elibs in

    (* Translate contract library. *)
    let%bind clibs' =
      match cmod.libs with
      | Some clib ->
          let%bind clib' = monomorphize_lib clib in
          pure @@ Some clib'
      | None -> pure None
    in

    (* Translate fields and their initializations. *)
    let%bind fields' =
      mapM
        ~f:(fun (i, t, fexp) ->
          let%bind fexp' = monomorphize_expr fexp in
          pure (i, t, fexp'))
        cmod.contr.cfields
    in

    (* Translate all contract components. *)
    let%bind comps' =
      mapM
        ~f:(fun comp ->
          let%bind body' = monomorphize_stmts comp.comp_body in
          pure
            {
              MS.comp_type = comp.comp_type;
              MS.comp_name = comp.comp_name;
              MS.comp_params = comp.comp_params;
              MS.comp_body = body';
            })
        cmod.contr.ccomps
    in

    let contr' =
      {
        MS.cname = cmod.contr.cname;
        MS.cparams = cmod.contr.cparams;
        MS.cfields = fields';
        ccomps = comps';
      }
    in
    let cmod' =
      {
        MS.smver = cmod.smver;
        MS.elibs = cmod.elibs;
        MS.libs = clibs';
        MS.contr = contr';
      }
    in

    (* Return back the whole program, transformed. *)
    pure (cmod', rlibs', elibs')

  (* For monomorphizing standalone expressions. *)
  let monomorphize_expr_wrapper expr =
    let%bind expr' = initialize_tfa_expr empty_init_env expr in
    let%bind () =
      let rec iterate_till_fixpoint () =
        let%bind changed = analyze_tfa_expr empty_tfa_env expr' in
        if changed then iterate_till_fixpoint () else pure ()
      in
      iterate_till_fixpoint ()
    in
    let%bind analysis_res = pp_tfa_expr_wrapper expr' in
    let () = DebugMessage.plog analysis_res in
    let%bind expr'' = monomorphize_expr expr' in
    pure expr''

  module OutputSyntax = MS
end

(* References:
  Motivation for a monomorphizing compiler:
  - Levity Polymorphism - Richard A. Eisenberg and Simon Peyton Jones
  - http://web.cecs.pdx.edu/~apt/jfp98.ps
  - http://mlton.org/References.attachments/060916-mlton.pdf
  - https://twitter.com/pcwalton/status/1192970706482388992?s=20 
*)
