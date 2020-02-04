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

(* This file translates the closure converted AST into LLVM-IR. 
 *
 * Memory representation of Scilla values:
 *
 * References:
 *  https://mapping-high-level-constructs-to-llvm-ir.readthedocs.io/en/latest/basic-constructs/unions.html#tagged-unions
 *  https://v1.realworldocaml.org/v1/en/html/memory-representation-of-values.html
 * 
 * -StringLit : %String = type { i8*, i32 }
 * -IntLit(32/64/128/256) : %Int(32/64/128/256) = type { i(32/64/128/256) }
 * -UintLit(32/64/128/256) : %Uint(32/64/128/256) = type { i(32/64/128/256) }
 *    Integers are wrapped with a struct to distinguish b/w signed and unsigned
 *    types. LLVM does not distinguish b/w them and only has i(32/64/128/256).
 * -ByStrX : [ X x i8 ] Array, where X is statically known.
 * -ByStr : %Bystr = type { i8*, i32 }
 * -ADTValue (cnameI, ts, ls) :
 *    Suppose the type of this literal (output of literal_type) is
 *    ADT (tname, ts), and tname has constructors cname1, ... cnameN,
 *    associated with it, then the translation happens as described below:
 *
 *    All ADTs are boxed, i.e., represented by a pointer to a
 *    packed struct containing the actual ADTValue. Record description:
 *
 *      %cnameI_ts1_..._tsn = type { i8, [type of each element of ls] }
 *      %tname_ts1_..._tsn = type { i8, cname1_ts1_..._tsn*, ..., cnameN_ts1_..._tsn* }.
 *      %p = %tname_ts1_...tsn* <bitcast> pointer_type (%cnameI_ts1_..._tsn)
 *
 *    where %p is the final pointer that represents the ADTValue in concern.
 *    The naming convention "_ts1_..._tsn" represents the specific polymorphic
 *    instantiation of the ADT. Also, the struct type "tname_ts1_...tsn" only
 *    requires the first i* value (the tag) for deconstructing the ADTValue.
 *    The remaining fields containing the struct types for each constructor in
 *    this type, is only to aid in type checking over the LLVM-IR. They must
 *    never be dereferenced (accessed).
 *
 *    The structs are packed so that it's straightforward to unpack / build them
 *    from handwritten C++ code in the SRTL without worrying about padding.
 *    We can't have handwritten C++ struct definitions of these structs (in SRTL)
 *    for the C++ compiler to take care of padding etc, because these structs
 *    are contract specific. The Scilla type will be passed to the C++ SRTL
 *    at runtime (as a TypeDescr), so that SRTL can parse the type, and based on that,
 *    the struct itself.
 *    Without this arrangement, we will have to generate code for complex operations
 *    such as JSON (de)serialization of Scilla values. Instead, we can now have SRTL
 *    do it, and aid it by passing the Scilla type along.
 *
 *  Closure representation:
 *    All Scilla functions are represented as closures, irrespective of whether they
 *    have free variables or not.
 *    An LLVM closure is represented by an unnamed struct type "{ fundef_sig*, void* }",
 *    where "fundef_sig" is the type signature of the `fundef` AST node corresponding
 *    to the closure and the "void*" is a pointer to the environment. A strong type
 *    cannot be used for the environment because two Scilla functions with the same
 *    types may have different environment types.
 *
 *    `fundef_sig` of a closure is built as follows:
 *     - All functions will take a (possibly null) pointer to their (possibly empty)
 *       environment as the first argument.
 *     - If the return value of the function needs to be passed on the stack
 *       (see can_pass_by_val), then a pointer to a caller allocated space for the
 *       return value will be the second argument.
 *     - The formal parameters follow in their original order.
 *)

open Core
open Result.Let_syntax
open MonadUtil
open Syntax
open UncurriedSyntax.Uncurried_Syntax
open ClosuredSyntax
open CodegenUtils
open Printf
open TypeLLConv

let array_get arr idx =
  try pure @@ arr.(idx)
  with Invalid_argument _ -> fail0 "GenLlvm: array_get: Invalid array index"

(* Convert a Scilla literal (compile time constant value) into LLVM-IR. *)
let rec genllvm_literal llmod l =
  let ctx = Llvm.module_context llmod in
  let i8_type = Llvm.i8_type ctx in
  let%bind sty = TypeUtilities.literal_type l in
  let%bind llty, llctys = genllvm_typ llmod sty in

  match l with
  | StringLit s ->
      (* Represented by scilla_string_ty. *)
      (* Build an array of characters. *)
      let chars =
        define_unnamed_const_global (tempname "stringlit")
          (Llvm.const_string ctx s) llmod
      in
      build_scilla_bytes ctx llty chars
  | ByStr bs ->
      let i8s =
        Array.map
          (String.to_array @@ Bystr.to_raw_bytes bs)
          ~f:(fun c -> Llvm.const_int i8_type (Char.to_int c))
      in
      let i8_array = Llvm.const_array i8_type i8s in
      let chars =
        define_unnamed_const_global (tempname "bystrlit") i8_array llmod
      in
      build_scilla_bytes ctx llty chars
  | IntLit il ->
      (* No better way to convert to LLVM integer than via strings :-(.
       * LLVM provides APIs that use APInt, but they aren't exposed via the OCaml API. *)
      pure
      @@ Llvm.const_named_struct llty
           ( match il with
           | Int32L i ->
               [|
                 Llvm.const_int_of_string (Llvm.i32_type ctx)
                   (Int32.to_string i) 10;
               |]
           | Int64L i ->
               [|
                 Llvm.const_int_of_string (Llvm.i64_type ctx)
                   (Int64.to_string i) 10;
               |]
           | Int128L i ->
               [|
                 Llvm.const_int_of_string
                   (Llvm.integer_type ctx 128)
                   (Stdint.Int128.to_string i)
                   10;
               |]
           | Int256L i ->
               [|
                 Llvm.const_int_of_string
                   (Llvm.integer_type ctx 256)
                   (Integer256.Int256.to_string i)
                   10;
               |] )
  | UintLit uil ->
      pure
      @@ Llvm.const_named_struct llty
           ( match uil with
           | Uint32L ui ->
               [|
                 Llvm.const_int_of_string (Llvm.i32_type ctx)
                   (Stdint.Uint32.to_string ui)
                   10;
               |]
           | Uint64L ui ->
               [|
                 Llvm.const_int_of_string (Llvm.i64_type ctx)
                   (Stdint.Uint64.to_string ui)
                   10;
               |]
           | Uint128L ui ->
               [|
                 Llvm.const_int_of_string
                   (Llvm.integer_type ctx 128)
                   (Stdint.Uint128.to_string ui)
                   10;
               |]
           | Uint256L ui ->
               [|
                 Llvm.const_int_of_string
                   (Llvm.integer_type ctx 256)
                   (Integer256.Uint256.to_string ui)
                   10;
               |] )
  | ByStrX bs ->
      let i8s =
        Array.map
          (String.to_array @@ Bystrx.to_raw_bytes bs)
          ~f:(fun c -> Llvm.const_int i8_type (Char.to_int c))
      in
      pure @@ Llvm.const_array i8_type i8s
  | ADTValue (cname, _, lits) ->
      (* LLVM struct that'll hold this ADTValue. *)
      let%bind llcty, tag = get_ctr_struct llctys cname in
      let%bind lits_ll = mapM lits ~f:(genllvm_literal llmod) in
      (* Prepend the tag to the constructor object we're building. *)
      let lits' = Llvm.const_int i8_type tag :: lits_ll in
      let ctrval = Llvm.const_named_struct llcty (Array.of_list lits') in
      (* Since ADTValues are boxed, i.e., represented by a pointer to the struct,
       * we are forced to create an unnamed global constant to get an address. *)
      let p_ctrval =
        define_unnamed_const_global (tempname "adtlit") ctrval llmod
      in
      (* The pointer to the constructor type should be cast to the adt type. *)
      let p_adtval = Llvm.const_bitcast p_ctrval llty in
      pure p_adtval
  | BNum _ | Msg _ | Map _ -> fail0 "GenLlvm: Unimplemented"

open CloCnvSyntax

type value_scope =
  (* Llvm.ValueKind.GlobalVariable *)
  | Global of Llvm.llvalue
  (* Llvm.ValueKind.Argument *)
  | FunArg of Llvm.llvalue
  (* Llvm.ValueKind.Instruction.Alloca *)
  | Local of Llvm.llvalue
  (* Pointer to a closure record and the struct type of the environment. *)
  | CloP of (Llvm.llvalue * Llvm.lltype)

type gen_env = {
  (* Resolve input AST name to a processed LLVM value *)
  llvals : (string * value_scope) list;
  (* Join points in scope. *)
  joins : (string * Llvm.llbasicblock) list;
  (* For currently being generated function, return via memory? *)
  retp : Llvm.llvalue option;
  (* Env pointer for the currently compiled function *)
  envparg : Llvm.llvalue option;
  (* A successor block to jump to. *)
  succblock : Llvm.llbasicblock option;
}

let try_resolve_id genv id =
  List.Assoc.find genv.llvals ~equal:( = ) (get_id id)

(* Resolve a name from the identifier. *)
let resolve_id genv id =
  match try_resolve_id genv id with
  | Some scope -> pure scope
  | None ->
      fail1
        (sprintf "GenLlvm: internal error: cannot resolve id %s." (get_id id))
        (get_rep id).ea_loc

(* Resolve id, and if it's alloca, load the alloca. *)
let resolve_id_value env builder_opt id =
  let%bind resolved = resolve_id env id in
  match resolved with
  | Global llval | FunArg llval | CloP (llval, _) -> pure llval
  | Local llval -> (
      match builder_opt with
      | Some builder ->
          pure @@ Llvm.build_load llval (tempname (get_id id)) builder
      | None ->
          fail1
            (sprintf
               "GenLlvm: resolve_id: internal error: llbuilder not provided to \
                load alloca for %s."
               (get_id id))
            (get_rep id).ea_loc )

(* Resolve id to an alloca or fail. *)
let resolve_id_local genv id =
  let%bind xresolv = resolve_id genv id in
  match xresolv with
  | Local a -> pure a
  | _ ->
      fail1
        (sprintf "GenLlvm: resolve_id_local: %s did not resolve to a Local"
           (get_id id))
        (get_rep id).ea_loc

let resolve_jblock genv b =
  match List.Assoc.find genv.joins ~equal:( = ) (get_id b) with
  | Some joinp -> pure joinp
  | None ->
      fail1
        (sprintf "GenLlvm: internal error: cannot resolve join point %s."
           (get_id b))
        (get_rep b).ea_loc

(* Build a struct val of that type using the function declaration and env pointer.
 * The type of fundecl itself isn't used because it can have strong type for the
 * closure environment argument (the first argument of the function), but we want
 * to use a void* for the first argument when building a closure for compatibility
 * with other Scilla functions of the same type but different environment type.
 *)
let build_closure builder cloty_ll fundecl fname envp =
  if Llvm.classify_value fundecl <> Llvm.ValueKind.Function then
    fail1
      (sprintf
         "GenLlvm: build_closure: internal error: Expected LLVM function \
          declaration for %s."
         (get_id fname))
      (get_rep fname).ea_loc
  else
    let ctx = Llvm.type_context cloty_ll in
    (* The fundef type is the first component of the closure type. *)
    let%bind clotys = struct_element_types cloty_ll in
    let%bind fundef_ty = array_get clotys 0 in
    (* Build a struct value for the closure. *)
    let fundecl' = Llvm.const_pointercast fundecl fundef_ty in
    let tmp =
      Llvm.build_insertvalue (Llvm.undef cloty_ll) fundecl' 0
        (tempname (get_id fname))
        builder
    in
    let envp_void =
      Llvm.build_pointercast envp (void_ptr_type ctx)
        (tempname (get_id fname ^ "_env_voidp"))
        builder
    in
    let cloval =
      Llvm.build_insertvalue tmp envp_void 1
        (tempname (get_id fname ^ "_cloval"))
        builder
    in
    pure cloval

(* Create a new block before pos_block. *)
let new_block_before llctx name pos_block =
  Llvm.insert_block llctx name pos_block

(* Create a new block after pos_block. *)
let new_block_after llctx name pos_block =
  let n = Llvm.insert_block llctx name pos_block in
  let _ = Llvm.move_block_after pos_block n in
  n

let genllvm_expr genv builder (e, erep) =
  let llmod =
    Llvm.insertion_block builder |> Llvm.block_parent |> Llvm.global_parent
  in
  let llctx = Llvm.module_context llmod in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in

  match e with
  | Literal l -> genllvm_literal llmod l
  | Var v -> resolve_id_value genv (Some builder) v
  | Constr (cname, _, cargs) ->
      let%bind sty = rep_typ erep in
      let%bind llty, llctys = genllvm_typ llmod sty in
      let%bind llcty, tag = get_ctr_struct llctys cname in
      let%bind cargs_ll =
        mapM cargs ~f:(resolve_id_value genv (Some builder))
      in
      (* Append the tag to the struct elements. *)
      let cargs_ll' = Llvm.const_int (Llvm.i8_type llctx) tag :: cargs_ll in
      let cmem = Llvm.build_malloc llcty (tempname "adtval") builder in
      (* Store each element of the struct into the malloc'd memory. *)
      List.iteri cargs_ll' ~f:(fun i el ->
          let gep = Llvm.build_struct_gep cmem i (tempname "adtgep") builder in
          let _ = Llvm.build_store el gep builder in
          ());
      let adtp = Llvm.build_bitcast cmem llty (tempname "adtptr") builder in
      pure adtp
  | FunClo fc -> (
      let fname = fst fc.envvars in
      let%bind resolved = resolve_id genv fname in
      match resolved with
      | CloP (cp, _) ->
          (* TODO: Ensure initialized. Requires stronger type for cloenv. *)
          pure cp
      | Global gv ->
          (* If the function resolves to a declaration, it means we haven't allocated
           * a closure for it (i.e., no AllocCloEnv statement). Ensure empty environment. *)
          if not (List.is_empty (snd fc.envvars)) then
            fail1
              (sprintf
                 "GenLlvm: genllvm_expr: Expected closure for %s with empty \
                  environment."
                 (get_id fname))
              erep.ea_loc
          else
            (* Build a closure object with empty environment. *)
            let envp = void_ptr_nullptr llctx in
            let%bind fundef_ty_ll = id_typ_ll llmod fname in
            let%bind cloval =
              build_closure builder fundef_ty_ll gv fname envp
            in
            pure cloval
      | _ ->
          fail1
            (sprintf "GenLlvm: genllvm:expr: Incorrect resolution of %s."
               (get_id fname))
            erep.ea_loc )
  | App (f, args) ->
      (* Resolve f (to a closure value) *)
      let%bind fclo_ll = resolve_id_value genv (Some builder) f in
      (* and extract the fundef and environment pointers. *)
      let fptr =
        Llvm.build_extractvalue fclo_ll 0
          (tempname (get_id f ^ "_fptr"))
          builder
      in
      let%bind fty = ptr_element_type (Llvm.type_of fptr) in
      let envptr =
        Llvm.build_extractvalue fclo_ll 1
          (tempname (get_id f ^ "_envptr"))
          builder
      in
      (* Resolve all arguments. *)
      let%bind args_ll =
        mapM args ~f:(fun arg ->
            let%bind arg_ty = id_typ_ll llmod arg in
            if can_pass_by_val dl arg_ty then
              resolve_id_value genv (Some builder) arg
            else
              (* Create an alloca, write the value to it, and pass the address. *)
              let argmem =
                Llvm.build_alloca arg_ty
                  (tempname (get_id f ^ "_" ^ get_id arg))
                  builder
              in
              let%bind arg' = resolve_id_value genv (Some builder) arg in
              let _ = Llvm.build_store arg' argmem builder in
              pure argmem)
      in
      let param_tys = Llvm.param_types fty in
      if Array.length param_tys = List.length args + 1 then
        (* Return by value. *)
        pure
        @@ Llvm.build_call fptr
             (Array.of_list (envptr :: args_ll))
             (tempname (get_id f ^ "_call"))
             builder
      else if Array.length param_tys = List.length args + 2 then
        (* Allocate a temporary stack variable for the return value. *)
        let%bind pretty_ty = array_get param_tys 1 in
        let%bind retty = ptr_element_type pretty_ty in
        let ret_alloca =
          Llvm.build_alloca retty (tempname (get_id f ^ "_retalloca")) builder
        in
        let _ =
          Llvm.build_call fptr
            (Array.of_list (envptr :: ret_alloca :: args_ll))
            "" builder
        in
        (* Load from ret_alloca. *)
        pure
        @@ Llvm.build_load ret_alloca (tempname (get_id f ^ "_ret")) builder
      else
        fail1
          (sprintf "%s %s."
             ( "GenLlvm: genllvm_expr: internal error: Incorrect number of \
                arguments" ^ " when compiling function application" )
             (get_id f))
          erep.ea_loc
  | _ -> fail1 "GenLlvm: genllvm_expr: unimplimented" erep.ea_loc

(* Translate stmts into LLVM-IR by inserting instructions through irbuilder.
 * Local variables are held in function-wide allocas since we don't know their scope.
 * Name clashes aren't a problem as it was taken care of in the ScopingRename pass.
 * The mem2reg pass will promote these allocas to virtual registers, no worries. *)
let rec genllvm_stmts genv builder stmts =
  let func = Llvm.insertion_block builder |> Llvm.block_parent in
  let llmod = Llvm.global_parent func in
  let llctx = Llvm.module_context llmod in

  let errm0 msg = fail0 ("GenLlvm: genllvm_stmts: internal error: " ^ msg) in
  let errm1 msg loc =
    fail1 ("GenLlvm: genllvm_stmts: internal error: " ^ msg) loc
  in

  (* Check that the LLVM struct type for an env matches the list of env vars we know. *)
  let validate_envvars_type env_ty evars =
    let%bind struct_types = struct_element_types env_ty in
    if Array.length struct_types <> List.length evars then
      errm0 "closure environment lengths mismatch."
    else
      let%bind evars_typs_ll =
        mapM evars ~f:(fun (_, t) -> genllvm_typ_fst llmod t)
      in
      if List.equal ( = ) (Array.to_list struct_types) evars_typs_ll then
        pure ()
      else errm0 "closure environment types mismatch."
  in

  let%bind _ =
    foldM stmts ~init:genv ~f:(fun accenv (stmt, _) ->
        match stmt with
        | LocalDecl x ->
            let%bind xty_ll = id_typ_ll llmod x in
            let xll = Llvm.build_alloca xty_ll (get_id x) builder in
            pure
            @@ { accenv with llvals = (get_id x, Local xll) :: accenv.llvals }
        | Bind (x, e) ->
            (* Find the allocation for x and store to it. *)
            let%bind xll = resolve_id_local accenv x in
            let%bind e_val = genllvm_expr accenv builder e in
            let _ = Llvm.build_store e_val xll builder in
            pure accenv
        | Ret v ->
            let%bind vll = resolve_id_value accenv (Some builder) v in
            let _ =
              match accenv.retp with
              | None -> Llvm.build_ret vll builder
              | Some p ->
                  let _ = Llvm.build_store vll p builder in
                  Llvm.build_ret_void builder
            in
            pure accenv
        | AllocCloEnv (fname, evars) -> (
            (* Allocate memory for the environment and build a closure object. *)
            (* We don't pass the builder because we expect fname to resolve to a global function. *)
            let%bind fdecl = resolve_id_value accenv None fname in
            let%bind fun_ty = ptr_element_type (Llvm.type_of fdecl) in
            if Llvm.classify_type fun_ty <> Llvm.TypeKind.Function then
              errm0 "Expected function type."
            else
              (* The first argument of fdecl is to the environment *)
              let%bind env_ty_p = array_get (Llvm.param_types fun_ty) 0 in
              let%bind env_ty = ptr_element_type env_ty_p in
              let%bind _ = validate_envvars_type env_ty evars in
              (* Allocate the environment. *)
              let envp =
                Llvm.build_malloc env_ty
                  (tempname (get_id fname ^ "_envp"))
                  builder
              in
              let%bind clo_ty_ll = id_typ_ll llmod fname in
              let%bind resolved_fname = resolve_id accenv fname in
              match resolved_fname with
              | Global fd ->
                  let%bind cloval =
                    build_closure builder clo_ty_ll fd fname envp
                  in
                  (* Now we bind fname to cloval instead of the function declaration it originally was bound to. *)
                  pure
                    {
                      accenv with
                      llvals =
                        (get_id fname, CloP (cloval, env_ty)) :: accenv.llvals;
                    }
              | _ ->
                  fail1
                    (sprintf
                       "GenLlvm: genllvm_stmts: %s did not resolve to global \
                        declaration."
                       (get_id fname))
                    (get_rep fname).ea_loc )
        | StoreEnv (envvar, v, (fname, envvars)) -> (
            let%bind resolved_fname = resolve_id accenv fname in
            match resolved_fname with
            | CloP (cloval, envty) ->
                let%bind _ = validate_envvars_type envty envvars in
                (* Get the second component of cloval (the envptr) and cast it to right type. *)
                let envvoidp =
                  Llvm.build_extractvalue cloval 1
                    (tempname (get_id fname ^ "_envp"))
                    builder
                in
                let envp =
                  Llvm.build_bitcast envvoidp (Llvm.pointer_type envty)
                    (tempname (get_id fname ^ "_envp"))
                    builder
                in
                (* Search for envvar in envvars and get its index. *)
                let%bind i =
                  match
                    List.findi envvars ~f:(fun _ (envvar', _) ->
                        equal_id envvar envvar')
                  with
                  | Some (i, _) -> pure i
                  | None ->
                      errm1
                        (sprintf "%s not found in env of %s." (get_id envvar)
                           (get_id fname))
                        (get_rep fname).ea_loc
                in
                (* Store v into envp[i] *)
                let envp_i =
                  Llvm.build_struct_gep envp i
                    (tempname (get_id fname ^ "_env_" ^ get_id envvar))
                    builder
                in
                let%bind vresolved = resolve_id_value accenv (Some builder) v in
                let _ = Llvm.build_store vresolved envp_i builder in
                (* This operation doesn't affect our codegen environment. *)
                pure accenv
            | _ ->
                errm1
                  (sprintf "expected %s to resolve to closure." (get_id fname))
                  (get_rep fname).ea_loc )
        | LoadEnv (v, envvar, (fname, envvars)) -> (
            match accenv.envparg with
            | Some envp ->
                let%bind envty = ptr_element_type (Llvm.type_of envp) in
                let%bind _ = validate_envvars_type envty envvars in
                (* Search for envvar in envvars and get its index. *)
                let%bind i =
                  match
                    List.findi envvars ~f:(fun _ (envvar', _) ->
                        equal_id envvar envvar')
                  with
                  | Some (i, _) -> pure i
                  | None ->
                      errm1
                        (sprintf "%s not found in env of %s." (get_id envvar)
                           (get_id fname))
                        (get_rep fname).ea_loc
                in
                (* Load from envp[i] into v *)
                let envp_i =
                  Llvm.build_struct_gep envp i
                    (tempname (get_id fname ^ "_env_" ^ get_id envvar))
                    builder
                in
                let loadi =
                  Llvm.build_load envp_i
                    (tempname (get_id v ^ "_envload"))
                    builder
                in
                (* Put the loaded value into a local variable, so that we can bind it as a Local. *)
                let loadi_alloca =
                  Llvm.build_alloca (Llvm.type_of loadi) (get_id v) builder
                in
                let _ = Llvm.build_store loadi loadi_alloca builder in
                pure
                  {
                    accenv with
                    llvals = (get_id v, Local loadi_alloca) :: accenv.llvals;
                  }
            | None ->
                errm1
                  (sprintf "expected envparg when compiling fundef %s."
                     (get_id fname))
                  (get_rep fname).ea_loc )
        | MatchStmt (o, clauses, jopt) ->
            let match_block = Llvm.insertion_block builder in
            (* Let's first generate the successor block for this entire match block. *)
            let succblock =
              new_block_after llctx (tempname "matchsucc") match_block
            in
            let genv_succblock = { accenv with succblock = Some succblock } in
            (* Let's next generate jopt as there may be jumps to it from clauses. *)
            let%bind genv_joinblock, insert_before_block =
              match jopt with
              | Some (jname, jsts) ->
                  let jblock =
                    new_block_after llctx (get_id jname) match_block
                  in
                  let builder' = Llvm.builder_at_end llctx jblock in
                  let%bind _ = genllvm_block genv_succblock builder' jsts in
                  (* Bind this block. *)
                  pure
                    ( {
                        genv_succblock with
                        joins = (get_id jname, jblock) :: genv_succblock.joins;
                      },
                      jblock )
              | None -> pure (genv_succblock, succblock)
            in
            let%bind ollval = resolve_id_value accenv (Some builder) o in
            (* Load the tag from ollval. *)
            let tagval_gep =
              Llvm.build_struct_gep ollval 0
                (tempname (get_id o ^ "_tag"))
                builder
            in
            let tagval =
              Llvm.build_load tagval_gep (tempname (get_id o ^ "_tag")) builder
            in
            let%bind sty = id_typ o in
            let%bind _, llctys = genllvm_typ llmod sty in
            (* Separate into constructor clauses and Any clause,
             * validating that an Any clause, if it exists, is the last one. *)
            let%bind cons_clauses, default_clause_opt =
              let rec go clauses (cons_clauses, default_clause_opt) =
                match clauses with
                | ((spat, _) as clause) :: rest_clauses -> (
                    match spat with
                    | Any _ ->
                        if
                          List.is_empty rest_clauses
                          (* This is the last one, we're good. *)
                        then pure (cons_clauses, Some clause)
                        else
                          errm1
                            (sprintf
                               "matching %s: Any clause not at the end of \
                                clauses."
                               (get_id o))
                            (get_rep o).ea_loc
                    | Constructor _ ->
                        (* Accummulate this and process further. *)
                        go rest_clauses
                          (clause :: cons_clauses, default_clause_opt) )
                (* We're done processing all clauses, reverse the list since we accummulated it in reverse. *)
                | [] -> pure (List.rev cons_clauses, default_clause_opt)
              in
              go clauses ([], None)
            in
            (* Check that there are right number of clauses. *)
            let%bind _ =
              match default_clause_opt with
              | None ->
                  if List.length cons_clauses <> List.length llctys then
                    errm1
                      (sprintf "match %s: all constructors not matched."
                         (get_id o))
                      (get_rep o).ea_loc
                  else pure ()
              | Some _ -> pure ()
            in
            let%bind default_block =
              match default_clause_opt with
              | Some (Any c, clause_stmts) ->
                  let default_block =
                    new_block_before llctx (tempname "default")
                      insert_before_block
                  in
                  let builder' = Llvm.builder_at_end llctx default_block in
                  (* Bind if c is a Binder. *)
                  let genv' =
                    match c with
                    | Wildcard -> genv_joinblock
                    | Binder v ->
                        (* Bind v as a local variable. *)
                        let valloca =
                          Llvm.build_alloca (Llvm.type_of ollval) (get_id v)
                            builder'
                        in
                        let _ = Llvm.build_store ollval valloca builder' in
                        {
                          genv_joinblock with
                          llvals =
                            (get_id v, Local valloca) :: genv_joinblock.llvals;
                        }
                  in
                  let _ = genllvm_block genv' builder' clause_stmts in
                  pure default_block
              | _ ->
                  (* This can only be if all clauses are constructors.
                   * Generate an empty default block. This will never execute. *)
                  let emptydefault =
                    new_block_before llctx (tempname "empty_default")
                      insert_before_block
                  in
                  let builder' = Llvm.builder_at_end llctx emptydefault in
                  let _ = Llvm.build_br succblock builder' in
                  pure emptydefault
            in
            (* Translate each clause. *)
            let%bind tag_block_list =
              mapM cons_clauses ~f:(fun (spat, body) ->
                  match spat with
                  | Constructor (cname, cargs) ->
                      let%bind llcty, tag = get_ctr_struct llctys cname in
                      let clause_block =
                        new_block_before llctx (tempname cname) default_block
                      in
                      let builder' = Llvm.builder_at_end llctx clause_block in
                      let cobjp =
                        Llvm.build_bitcast ollval (Llvm.pointer_type llcty)
                          (tempname (get_id o))
                          builder'
                      in
                      let celm_tys = Llvm.struct_element_types llcty in
                      (* The LLVM struct type will have one additional field for the tag. *)
                      if Array.length celm_tys <> List.length cargs + 1 then
                        errm1
                          (sprintf
                             "matching %s: Constructor %s argument mismatch."
                             (get_id o) cname)
                          (get_rep o).ea_loc
                      else
                        (* Generate binding for each binder in cargs. We count from 1 to ignore the tag. *)
                        let _, binds_rev =
                          List.fold cargs ~init:(1, []) ~f:(fun (i, acc) c ->
                              match c with
                              | Wildcard -> (i + 1, acc)
                              | Binder v ->
                                  (* Bind v as a local variable. *)
                                  let vgep =
                                    Llvm.build_struct_gep cobjp i
                                      (tempname (get_id v ^ "_gep"))
                                      builder'
                                  in
                                  let vloaded =
                                    Llvm.build_load vgep
                                      (tempname (get_id v ^ "_load"))
                                      builder'
                                  in
                                  let valloca =
                                    Llvm.build_alloca (Llvm.type_of vloaded)
                                      (get_id v) builder'
                                  in
                                  let _ =
                                    Llvm.build_store vloaded valloca builder'
                                  in
                                  (i + 1, (get_id v, Local valloca) :: acc))
                        in
                        let genv' =
                          {
                            genv_joinblock with
                            llvals = List.rev binds_rev @ genv_joinblock.llvals;
                          }
                        in
                        let%bind _ = genllvm_block genv' builder' body in
                        pure
                          (Llvm.const_int (Llvm.i8_type llctx) tag, clause_block)
                  | _ ->
                      errm1
                        (sprintf "matching %s: expected Constructor pattern."
                           (get_id o))
                        (get_rep o).ea_loc)
            in
            (* Create the switch statement and add all clauses to it. *)
            let sw =
              Llvm.build_switch tagval default_block
                (List.length tag_block_list)
                builder
            in
            let _ =
              List.iter tag_block_list ~f:(fun (tag, block) ->
                  Llvm.add_case sw tag block)
            in
            (* Reposition the builder back to where we can continue further. *)
            let _ = Llvm.position_at_end succblock builder in
            pure accenv
        | JumpStmt dest ->
            let%bind jblock = resolve_jblock accenv dest in
            let _ = Llvm.build_br jblock builder in
            pure accenv
        | _ -> pure accenv)
  in
  pure ()

(* Generate LLVM-IR for a block of statements.
 * Inserts a terminator instruction when needed. *)
and genllvm_block genv builder stmts =
  let%bind _ = genllvm_stmts genv builder stmts in
  let b = Llvm.insertion_block builder in
  let fname = Llvm.value_name (Llvm.block_parent b) in
  match Llvm.block_terminator b with
  | Some _ -> pure ()
  | None -> (
      match genv.succblock with
      | Some sb ->
          let _ = Llvm.build_br sb builder in
          pure ()
      | None ->
          fail0
            (sprintf
               "GenLlvm: genllvm_block: internal error: Unable to determine \
                successor block in %s."
               fname) )

let genllvm_closures llmod topfuns =
  let ctx = Llvm.module_context llmod in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  (* We translate closures in two passes, the first pass declares them
   * all and the second one does the actual translation of the bodies. *)
  let%bind fdecls =
    foldrM topfuns ~init:[] ~f:(fun accenv cr ->
        let%bind ret_ty_ll = genllvm_typ_fst llmod !(cr.thisfun).fretty in
        let%bind envars_ty_ll =
          mapM (snd cr.envvars) ~f:(Fn.compose (genllvm_typ_fst llmod) snd)
        in
        let envty_name = tempname (get_id !(cr.thisfun).fname ^ "_env") in
        let%bind env_ty_ll =
          named_struct_type llmod envty_name (Array.of_list envars_ty_ll)
        in
        let penv_ty_ll = Llvm.pointer_type env_ty_ll in
        let%bind args_ty_ll =
          mapM !(cr.thisfun).fargs ~f:(Fn.compose (genllvm_typ_fst llmod) snd)
        in
        (* Check if an argument needs to be passed through a pointer. *)
        let args_ty_ll' =
          List.map args_ty_ll ~f:(fun llt ->
              if can_pass_by_val dl llt then llt else Llvm.pointer_type llt)
        in
        let%bind decl =
          (* We can't use "genllvm_typ" because it doesn't know the type of the environment. *)
          if
            can_pass_by_val dl ret_ty_ll
            (* return type, env pointer type, argument types *)
          then
            scilla_function_decl ~is_internal:true llmod
              (get_id !(cr.thisfun).fname)
              ret_ty_ll
              (penv_ty_ll :: args_ty_ll')
          else
            (* returns void (return value is via the stack),
             * env pointer type, type of pointer to return type, argument types *)
            let fargs_ty =
              penv_ty_ll :: Llvm.pointer_type ret_ty_ll :: args_ty_ll'
            in
            scilla_function_decl ~is_internal:true llmod
              (get_id !(cr.thisfun).fname)
              (Llvm.void_type ctx) fargs_ty
        in
        pure @@ ((get_id !(cr.thisfun).fname, decl) :: accenv))
  in

  let genv_fdecls =
    {
      llvals = List.map fdecls ~f:(fun (fname, decl) -> (fname, Global decl));
      joins = [];
      retp = None;
      envparg = None;
      succblock =
        None (* No successor blocks when we begin to compile a function *);
    }
  in

  (* Let us now define each of these functions. *)
  let fdecl_cr_l = List.zip_exn fdecls topfuns in
  let%bind _ =
    iterM fdecl_cr_l ~f:(fun ((fname, f), cr) ->
        let fid = !(cr.thisfun).fname in
        (* The function f doesn't have a body yet, so insert a basic block. *)
        let _ = Llvm.append_block ctx "entry" f in
        let builder = Llvm.builder_at_end ctx (Llvm.entry_block f) in
        let sfdef_args = !(cr.thisfun).fargs in
        let f_params = Llvm.params f in
        let%bind envparg = array_get f_params 0 in
        (* Bind the envptr arg for codegen inside the function. *)
        let genv_envparg = { genv_fdecls with envparg = Some envparg } in
        (* Bind the return value argument if via a pointer. *)
        let%bind args_begin, genv_retp =
          if List.length sfdef_args + 1 = Array.length f_params then
            (* Return value is not through a pointer. *)
            pure (1, genv_envparg)
          else if List.length sfdef_args + 2 = Array.length f_params then
            (* Return value is through the second argument, a pointer. *)
            let%bind retp = array_get f_params 1 in
            pure (2, { genv_envparg with retp = Some retp })
          else
            fail1
              (sprintf
                 "GenLlvm: genllvm_closures: internal error compiling fundef \
                  %s. Incorrect number of arguments."
                 fname)
              (get_rep fid).ea_loc
        in
        (* Now bind each function argument. *)
        let%bind genv_args, _ =
          foldrM sfdef_args
            ~init:(genv_retp, List.length sfdef_args - 1)
            ~f:(fun (accum_genv, idx) (varg, sty) ->
              let%bind arg_llval = array_get f_params (args_begin + idx) in
              let%bind sty_llty = genllvm_typ_fst llmod sty in
              let arg_mismatch_err =
                fail1
                  (sprintf
                     "GenLlvm: genllvm_closures: type mismatch in argument %s \
                      compiling function %s."
                     (get_id varg) (get_id fid))
                  (get_rep fid).ea_loc
              in
              let%bind arg_llval' =
                if can_pass_by_val dl sty_llty then
                  if sty_llty = Llvm.type_of arg_llval then pure arg_llval
                  else arg_mismatch_err
                else if Llvm.pointer_type sty_llty = Llvm.type_of arg_llval then
                  pure (Llvm.build_load arg_llval (get_id varg) builder)
                else arg_mismatch_err
              in
              pure
                ( {
                    accum_genv with
                    llvals =
                      (get_id varg, FunArg arg_llval') :: accum_genv.llvals;
                  },
                  idx - 1 ))
        in
        (* We now have the environment to generate the function body. *)
        genllvm_block genv_args builder !(cr.thisfun).fbody)
  in

  pure genv_fdecls

let prepare_target llmod =
  (* We only support generating code for x86_64. *)
  Llvm_X86.initialize ();
  let triple = Llvm_target.Target.default_triple () in
  let lltarget = Llvm_target.Target.by_triple triple in
  let llmachine = Llvm_target.TargetMachine.create ~triple lltarget in
  let lldly =
    Llvm_target.DataLayout.as_string
      (Llvm_target.TargetMachine.data_layout llmachine)
  in
  let _ = Llvm.set_target_triple triple llmod in
  let _ = Llvm.set_data_layout lldly llmod in
  ()

let optimize_module llmod =
  let mpm = Llvm.PassManager.create () in
  let () = Llvm_scalar_opts.add_memory_to_register_promotion mpm in
  let () = Llvm_scalar_opts.add_aggressive_dce mpm in
  let () = Llvm_scalar_opts.add_early_cse mpm in
  let () = Llvm_ipo.add_function_inlining mpm in
  let () = Llvm_scalar_opts.add_aggressive_dce mpm in
  let () = Llvm_scalar_opts.add_cfg_simplification mpm in
  let () = Llvm_scalar_opts.add_gvn mpm in
  let () = Llvm_scalar_opts.add_dead_store_elimination mpm in
  let () = Llvm_scalar_opts.add_aggressive_dce mpm in
  let _ = Llvm.PassManager.run_module llmod mpm in
  ()

(* Generate an LLVM module for a Scilla module. *)
let genllvm_module (cmod : cmodule) =
  let llcontext = Llvm.create_context () in
  let llmod = Llvm.create_module llcontext (get_id cmod.contr.cname) in
  let _ = prepare_target llmod in

  (* printf "\n%s\n" (Llvm.string_of_llmodule llmod); *)
  match Llvm_analysis.verify_module llmod with
  | None -> pure (Llvm.string_of_llmodule llmod)
  | Some err -> fail0 ("GenLlvm: genllvm_module: internal error: " ^ err)

(* Generate an LLVM module for a statement sequence. *)
let genllvm_stmt_list_wrapper stmts =
  let llcontext = Llvm.create_context () in
  let llmod = Llvm.create_module llcontext "scilla_expr" in
  let _ = prepare_target llmod in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in

  (* Gather all the top level functions. *)
  let topclos = gather_closures stmts in
  let%bind tydescr_map =
    TypeDescr.generate_type_descr_stmts_wrapper llmod topclos stmts
  in
  let%bind genv_fdecls = genllvm_closures llmod topclos in

  (* Create a function to house the instructions. *)
  let%bind fty, retty =
    (* Let's look at the last statement and try to infer a return type. *)
    match List.last stmts with
    | Some (Ret v, _) ->
        let%bind retty = rep_typ (get_rep v) in
        let%bind retty_ll = id_typ_ll llmod v in
        if
          can_pass_by_val dl retty_ll
          (* First argument, as per convention, is an (empty) envptr. *)
        then
          pure (Llvm.function_type retty_ll [| void_ptr_type llcontext |], retty)
          (* First argument is an (empty) envptr and second is the pointer to return value. *)
        else
          pure
            ( Llvm.function_type (Llvm.void_type llcontext)
                [| void_ptr_type llcontext; Llvm.pointer_type retty_ll |],
              retty )
    | _ ->
        fail0
          "GenLlvm: genllvm_stmt_list_wrapper: expected last statment to be Ret"
  in
  let f = Llvm.define_function (tempname "scilla_expr") fty llmod in
  (* Let's mark f as an internal function for aggressive optimizations. *)
  Llvm.set_linkage Llvm.Linkage.Internal f;
  let%bind init_env =
    if Llvm.void_type llcontext = Llvm.return_type fty then
      (* If return type is void, then second parameter is the pointer to return value. *)
      let%bind retp = array_get (Llvm.params f) 1 in
      pure { genv_fdecls with retp = Some retp }
    else pure { genv_fdecls with retp = None }
  in
  let irbuilder = Llvm.builder_at_end llcontext (Llvm.entry_block f) in
  let%bind _ = genllvm_block init_env irbuilder stmts in

  (* Generate a wrapper function scilla_main that'll call print on the result value. *)
  let%bind printer = GenSrtlDecls.decl_print_scilla_val llmod in
  let mainty = Llvm.function_type (Llvm.void_type llcontext) [||] in
  let mainb =
    Llvm.entry_block (Llvm.define_function "scilla_main" mainty llmod)
  in
  let builder_mainb = Llvm.builder_at_end llcontext mainb in
  let%bind _ =
    if TypeUtilities.is_storable_type retty then
      let%bind tydescr_ll = TypeDescr.resolve_typdescr tydescr_map retty in
      match init_env.retp with
      | Some retp ->
          (* Returns value on the stack through a pointer. *)
          let%bind __ =
            match retty with
            | PrimType _ -> pure ()
            | _ ->
                fail0 "GenLlvm: Stack (indirect) return of non PrimType value"
          in
          (* Allocate memory for return value. *)
          let%bind retty = ptr_element_type (Llvm.type_of retp) in
          let memv =
            Llvm.build_alloca retty (tempname "mainval") builder_mainb
          in
          let memv_voidp =
            Llvm.build_pointercast memv (void_ptr_type llcontext)
              (tempname "memvoidcast") builder_mainb
          in
          let _ =
            Llvm.build_call f
              [| void_ptr_nullptr llcontext; memv |]
              "" builder_mainb
          in
          let _ =
            Llvm.build_call printer
              [| tydescr_ll; memv_voidp |]
              "" builder_mainb
          in
          pure ()
      | None ->
          (* Direct return *)
          let retty_ll = Llvm.return_type fty in
          let calli =
            Llvm.build_call f
              [| void_ptr_nullptr llcontext |]
              (tempname "exprval") builder_mainb
          in
          (* ADTs and Maps are always boxed, so we pass the pointer anyway.
        * PrimTypes need to be boxed now. *)
          if Llvm.classify_type retty_ll <> Llvm.TypeKind.Pointer then
            let%bind _ =
              match retty with
              | PrimType _ -> pure ()
              | _ -> fail0 "GenLlvm: Direct return of PrimType value by value"
            in
            let memv =
              Llvm.build_alloca retty_ll (tempname "pval") builder_mainb
            in
            let memv_voidp =
              Llvm.build_pointercast memv (void_ptr_type llcontext)
                (tempname "memvoidcast") builder_mainb
            in
            let _ = Llvm.build_store calli memv builder_mainb in
            let _ =
              Llvm.build_call printer
                [| tydescr_ll; memv_voidp |]
                "" builder_mainb
            in
            pure ()
          else
            let%bind _ =
              match retty with
              | ADT _ | MapType _ -> pure ()
              | _ ->
                  fail0
                    "GenLlvm: Direct return of non ADT / non MapType value by \
                     pointer"
            in
            let memv_voidp =
              Llvm.build_pointercast calli (void_ptr_type llcontext)
                (tempname "memvoidcast") builder_mainb
            in
            let _ =
              Llvm.build_call printer
                [| tydescr_ll; memv_voidp |]
                "" builder_mainb
            in
            pure ()
    else
      (* For non storable types, we print "<closure>" *)
      let _ =
        Llvm.build_call f
          [| void_ptr_nullptr llcontext |]
          (tempname "cloval") builder_mainb
      in
      (* TODO *)
      pure ()
  in
  let _ = Llvm.build_ret_void builder_mainb in

  DebugMessage.plog
    (sprintf "Before verify module: \n%s\n" (Llvm.string_of_llmodule llmod));

  match Llvm_analysis.verify_module llmod with
  | None ->
      DebugMessage.plog
        (sprintf "Before optimizations: \n%s\n" (Llvm.string_of_llmodule llmod));
      (* optimize_module llmod; *)
      pure (Llvm.string_of_llmodule llmod)
  | Some err ->
      fail0 ("GenLlvm: genllvm_stmt_list_wrapper: internal error: " ^ err)
