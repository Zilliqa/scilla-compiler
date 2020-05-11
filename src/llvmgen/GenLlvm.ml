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
 *
 *  Interaction with SRTL / JITD
 *  A.
 *    When a builtin / function in SRTL must take / return values of different types
 *    For example, _print_scilla_val, _fetch_field, or when JITD has to invoke a
 *    transition wrapper, then the arguments / return values are passed in memory
 *    (accompanied by type descriptor(s) when necessary).
 *    If there's only one value  being passed / returned:
 *      1. If the value's type is boxed, then the pointer is the boxing pointer.
 *         (this avoids an extra indirection).
 *      2. For unboxed types, the value must be loaded in the callee / caller.
 *    When multiple values are passed, all the values are put in a memory buffer
 *    and the offsets of each individual value can only be computed in-order,
 *    by knowing their types. A load is now always needed in the callee / caller.
 *  B.
 *    Builtins / functions in SRTL whose types are fixed (for example _add_int32)
 *    don't need a type descriptor and actual values are passed / returned
 *    (instead of through memory). Of course if the value is too big for
 *    `can_pass_by_val`, then it's passed via the stack. This is same as the
 *    convention used for function calls within a Scilla execution.
 *)

open Core_kernel
open! Int.Replace_polymorphic_compare
open Result.Let_syntax
open Scilla_base
module Literal = Literal.FlattenedLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
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
        define_global ~const:true ~unnamed:true (tempname "stringlit")
          (Llvm.const_string ctx s) llmod
      in
      build_scilla_bytes ctx llty chars
  | ByStr bs ->
      let i8s =
        Array.map
          (String.to_array @@ Literal.Bystr.to_raw_bytes bs)
          ~f:(fun c -> Llvm.const_int i8_type (Char.to_int c))
      in
      let i8_array = Llvm.const_array i8_type i8s in
      let chars =
        define_global ~const:true ~unnamed:true (tempname "bystrlit") i8_array
          llmod
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
          (String.to_array @@ Literal.Bystrx.to_raw_bytes bs)
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
        define_global ~const:true ~unnamed:true (tempname "adtlit") ctrval llmod
      in
      (* The pointer to the constructor type should be cast to the adt type. *)
      let p_adtval = Llvm.const_bitcast p_ctrval llty in
      pure p_adtval
  | BNum _ | Msg _ | Map _ -> fail0 "GenLlvm: Unimplemented"

open CloCnvSyntax

type value_scope =
  (* Llvm.ValueKind.GlobalVariable *)
  | Global of Llvm.llvalue
  (* Global function declaration. *)
  | FunDecl of Llvm.llvalue
  (* Llvm.ValueKind.Argument *)
  | FunArg of Llvm.llvalue
  (* Llvm.ValueKind.Instruction.Alloca *)
  | Local of Llvm.llvalue
  (* Pair of closure record and the struct type of the environment. *)
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
  (* type descriptor map. *)
  tdmap : TypeDescr.typ_descr;
}

let try_resolve_id genv id =
  List.Assoc.find genv.llvals ~equal:String.( = ) (Identifier.get_id id)

(* Resolve a name from the identifier. *)
let resolve_id genv id =
  match try_resolve_id genv id with
  | Some scope -> pure scope
  | None ->
      fail1
        (sprintf "GenLlvm: internal error: cannot resolve id %s."
           (Identifier.get_id id))
        (Identifier.get_rep id).ea_loc

(* Resolve id, and if it's alloca, load the alloca. *)
let resolve_id_value env builder_opt id =
  let%bind resolved = resolve_id env id in
  match resolved with
  | FunDecl llval | FunArg llval | CloP (llval, _) -> pure llval
  | Local llval | Global llval -> (
      match builder_opt with
      | Some builder ->
          pure
          @@ Llvm.build_load llval (tempname (Identifier.get_id id)) builder
      | None ->
          fail1
            (sprintf
               "GenLlvm: resolve_id: internal error: llbuilder not provided to \
                load alloca for %s."
               (Identifier.get_id id))
            (Identifier.get_rep id).ea_loc )

(* Resolve id to an alloca / global memory location or fail. *)
let resolve_id_memloc genv id =
  let%bind xresolv = resolve_id genv id in
  match xresolv with
  | Local a | Global a -> pure a
  | _ ->
      fail1
        (sprintf "GenLlvm: resolve_id_local: %s did not resolve to a Local"
           (Identifier.get_id id))
        (Identifier.get_rep id).ea_loc

let resolve_jblock genv b =
  match
    List.Assoc.find genv.joins ~equal:String.( = ) (Identifier.get_id b)
  with
  | Some joinp -> pure joinp
  | None ->
      fail1
        (sprintf "GenLlvm: internal error: cannot resolve join point %s."
           (Identifier.get_id b))
        (Identifier.get_rep b).ea_loc

(* Build a struct val of that type using the function declaration and env pointer.
 * The type of fundecl itself isn't used because it can have strong type for the
 * closure environment argument (the first argument of the function), but we want
 * to use a void* for the first argument when building a closure for compatibility
 * with other Scilla functions of the same type but different environment type.
 *)
let build_closure builder cloty_ll fundecl fname envp =
  if Base.Poly.(Llvm.classify_value fundecl <> Llvm.ValueKind.Function) then
    fail1
      (sprintf
         "GenLlvm: build_closure: internal error: Expected LLVM function \
          declaration for %s."
         (Identifier.get_id fname))
      (Identifier.get_rep fname).ea_loc
  else
    let ctx = Llvm.type_context cloty_ll in
    (* The fundef type is the first component of the closure type. *)
    let%bind clotys = struct_element_types cloty_ll in
    let%bind fundef_ty = array_get clotys 0 in
    (* Build a struct value for the closure. *)
    let fundecl' = Llvm.const_pointercast fundecl fundef_ty in
    let%bind tmp =
      build_insertvalue (Llvm.undef cloty_ll) fundecl' 0
        (tempname (Identifier.get_id fname))
        builder
    in
    let envp_void =
      Llvm.build_pointercast envp (void_ptr_type ctx)
        (tempname (Identifier.get_id fname ^ "_env_voidp"))
        builder
    in
    let%bind cloval =
      build_insertvalue tmp envp_void 1
        (tempname (Identifier.get_id fname ^ "_cloval"))
        builder
    in
    pure cloval

(* Built call instructions for Apps and Builtins. *)
let build_call_helper llmod genv builder callee_id callee args envptr_opt =
  let llctx = Llvm.module_context llmod in
  let envptr = match envptr_opt with Some envptr -> [ envptr ] | None -> [] in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  let fname, sloc =
    (Identifier.get_id callee_id, (Identifier.get_rep callee_id).ea_loc)
  in
  let%bind fty = ptr_element_type (Llvm.type_of callee) in
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
              (tempname (fname ^ "_" ^ Identifier.get_id arg))
              builder
          in
          let%bind arg' = resolve_id_value genv (Some builder) arg in
          let _ = Llvm.build_store arg' argmem builder in
          pure argmem)
  in
  let param_tys = Llvm.param_types fty in
  (* Scilla function application (App) calls have an envptr argument. *)
  let num_call_args = List.length args + List.length envptr in
  (* If the callee signature has exactly num_call_args parameters, 
   * it's direct return (i.e., no additional parameter for return). *)
  if Array.length param_tys = num_call_args then
    (* Return by value. *)
    let callname =
      (* Calls to function returning void must not have a name. *)
      if Base.Poly.(Llvm.return_type fty <> Llvm.void_type llctx) then
        tempname (fname ^ "_call")
      else ""
    in
    pure
    @@ Llvm.build_call callee
         (Array.of_list (envptr @ args_ll))
         callname builder
  else if Array.length param_tys = num_call_args + 1 then
    (* Allocate a temporary stack variable for the return value. *)
    let%bind pretty_ty = array_get param_tys 1 in
    let%bind retty = ptr_element_type pretty_ty in
    let ret_alloca =
      Llvm.build_alloca retty (tempname (fname ^ "_retalloca")) builder
    in
    let _ =
      Llvm.build_call callee
        (Array.of_list (envptr @ (ret_alloca :: args_ll)))
        "" builder
    in
    (* Load from ret_alloca. *)
    pure @@ Llvm.build_load ret_alloca (tempname (fname ^ "_ret")) builder
  else
    fail1
      (sprintf "%s %s."
         ( "GenLlvm: genllvm_expr: internal error: Incorrect number of arguments"
         ^ " when compiling function application" )
         fname)
      sloc

let genllvm_expr genv builder (e, erep) =
  let llmod =
    Llvm.insertion_block builder |> Llvm.block_parent |> Llvm.global_parent
  in
  let llctx = Llvm.module_context llmod in

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
      let%bind cmem =
        GenSrtlDecls.build_salloc llcty (tempname "adtval") builder
      in
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
      | FunDecl gv ->
          (* If the function resolves to a declaration, it means we haven't allocated
           * a closure for it (i.e., no AllocCloEnv statement). Ensure empty environment. *)
          if not (List.is_empty (snd fc.envvars)) then
            fail1
              (sprintf
                 "GenLlvm: genllvm_expr: Expected closure for %s with empty \
                  environment."
                 (Identifier.get_id fname))
              erep.ea_loc
          else
            (* Build a closure object with empty environment. *)
            let envp = void_ptr_nullptr llctx in
            let%bind clo_ty_ll = id_typ_ll llmod fname in
            let%bind cloval = build_closure builder clo_ty_ll gv fname envp in
            pure cloval
      | _ ->
          fail1
            (sprintf "GenLlvm: genllvm:expr: Incorrect resolution of %s."
               (Identifier.get_id fname))
            erep.ea_loc )
  | App (f, args) ->
      (* Resolve f (to a closure value) *)
      let%bind fclo_ll = resolve_id_value genv (Some builder) f in
      (* and extract the fundef and environment pointers. *)
      let%bind fptr =
        build_extractvalue fclo_ll 0
          (tempname (Identifier.get_id f ^ "_fptr"))
          builder
      in
      let%bind envptr =
        build_extractvalue fclo_ll 1
          (tempname (Identifier.get_id f ^ "_envptr"))
          builder
      in
      build_call_helper llmod genv builder f fptr args (Some envptr)
  | Builtin ((b, brep), args) ->
      let bname = Identifier.mk_id (pp_builtin b) brep in
      let%bind bdecl = GenSrtlDecls.decl_builtins llmod b args in
      build_call_helper llmod genv builder bname bdecl args None
  | _ -> fail1 "GenLlvm: genllvm_expr: unimplimented" erep.ea_loc

(* Allocates memory for indices, puts them in there and returns a pointer. *)
let prepare_state_access_indices llmod genv builder indices =
  let llctx = Llvm.module_context llmod in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  if List.is_empty indices then
    pure @@ Llvm.const_pointer_null (Llvm.i8_type llctx)
  else
    let%bind indices_types = mapM indices ~f:(id_typ_ll llmod) in
    let membuf_size =
      List.fold indices_types ~init:0 ~f:(fun s t -> s + llsizeof dl t)
    in
    let%bind membuf =
      GenSrtlDecls.build_array_salloc (Llvm.i8_type llctx) membuf_size
        (tempname "indices_buf") builder
    in
    let%bind _ =
      foldM (List.zip_exn indices indices_types) ~init:0
        ~f:(fun offset (idx, t) ->
          let%bind idx_ll = resolve_id_value genv (Some builder) idx in
          let idx_size = llsizeof dl t in
          if offset + idx_size > membuf_size then
            fail0
              "GenLlvm: genllvm_stmts: internal error: incorrect offset \
               computation for MapGet"
          else
            let gep =
              Llvm.build_gep membuf
                [| Llvm.const_int (Llvm.i32_type llctx) offset |]
                (tempname "indices_gep") builder
            in
            let gepcasted =
              Llvm.build_pointercast gep (Llvm.pointer_type t) "indices_cast"
                builder
            in
            let _ = Llvm.build_store idx_ll gepcasted builder in
            pure (offset + idx_size))
    in
    pure membuf

(* Translate state fetches. *)
let genllvm_fetch_state llmod genv builder dest fname indices fetch_val =
  let llctx = Llvm.module_context llmod in
  let%bind indices_buf =
    prepare_state_access_indices llmod genv builder indices
  in
  let%bind f = GenSrtlDecls.decl_fetch_field llmod in
  let%bind mty = id_typ fname in
  let%bind tyd = TypeDescr.resolve_typdescr genv.tdmap mty in
  let%bind execptr =
    match Llvm.lookup_global "_execptr" llmod with
    | Some v ->
        let v' = Llvm.build_load v (tempname "execptr") builder in
        pure v'
    | None ->
        fail0
          "GenLlvm: genllvm_update_state: internal error. Couldn't find execptr"
  in
  let fieldname =
    Llvm.const_pointercast
      (define_global
         (tempname (Identifier.get_id fname))
         (Llvm.const_stringz llctx (Identifier.get_id fname))
         llmod ~const:true ~unnamed:true)
      (Llvm.pointer_type (Llvm.i8_type llctx))
  in
  let num_indices =
    Llvm.const_int (Llvm.i32_type llctx) (List.length indices)
  in
  let fetchval_ll =
    Llvm.const_int (Llvm.i32_type llctx) (Bool.to_int fetch_val)
  in
  (* We have all the arguments built, build the call. *)
  let retval =
    Llvm.build_call f
      [| execptr; fieldname; tyd; num_indices; indices_buf; fetchval_ll |]
      (tempname (Identifier.get_id dest))
      builder
  in
  let%bind retty = id_typ dest in
  let%bind retty_ll = genllvm_typ_fst llmod retty in
  let%bind retloc = resolve_id_memloc genv dest in
  let%bind () =
    if is_boxed_typ retty then
      (* An assertion that boxed types are pointers. *)
      let%bind () =
        if Base.Poly.(Llvm.classify_type retty_ll <> Llvm.TypeKind.Pointer) then
          fail0
            "GenLlvm: genllvm_stmts: internal error: Boxed type doesn't \
             translate to pointer type"
        else pure ()
      in
      (* Write to the local alloca for this value. *)
      let castedret =
        Llvm.build_pointercast retval retty_ll
          (tempname (Identifier.get_id dest))
          builder
      in
      let _ = Llvm.build_store castedret retloc builder in
      pure ()
    else
      (* Not a boxed type. Load the value and then write to local mem. *)
      let pcast =
        Llvm.build_pointercast retval
          (Llvm.pointer_type retty_ll)
          (tempname (Identifier.get_id dest))
          builder
      in
      let retload =
        Llvm.build_load pcast (tempname (Identifier.get_id dest)) builder
      in
      let _ = Llvm.build_store retload retloc builder in
      pure ()
  in
  pure genv

(* Translate state updates. *)
let genllvm_update_state llmod genv builder fname indices valopt =
  let llctx = Llvm.module_context llmod in
  let%bind indices_buf =
    prepare_state_access_indices llmod genv builder indices
  in
  let%bind f = GenSrtlDecls.decl_update_field llmod in
  let%bind mty = id_typ fname in
  let%bind tyd = TypeDescr.resolve_typdescr genv.tdmap mty in
  let%bind execptr =
    match Llvm.lookup_global "_execptr" llmod with
    | Some v ->
        let v' = Llvm.build_load v (tempname "execptr") builder in
        pure v'
    | None ->
        fail0
          "GenLlvm: genllvm_update_state: internal error. Couldn't find execptr"
  in
  let fieldname =
    Llvm.const_pointercast
      (define_global
         (tempname (Identifier.get_id fname))
         (Llvm.const_stringz llctx (Identifier.get_id fname))
         llmod ~const:true ~unnamed:true)
      (Llvm.pointer_type (Llvm.i8_type llctx))
  in
  let num_indices =
    Llvm.const_int (Llvm.i32_type llctx) (List.length indices)
  in
  let%bind value_ll =
    match valopt with
    | Some v ->
        let%bind vty = id_typ v in
        let%bind vty_ll = genllvm_typ_fst llmod vty in
        let%bind value_ll = resolve_id_value genv (Some builder) v in
        if is_boxed_typ vty then
          let%bind () =
            (* This is a pointer already, just pass that directly. *)
            if Base.Poly.(Llvm.classify_type vty_ll <> Llvm.TypeKind.Pointer)
            then
              fail0
                "GenLlvm: genllvm_update_state: internal error. Expected \
                 pointer value"
            else pure ()
          in
          let castedvalue =
            Llvm.build_pointercast value_ll (void_ptr_type llctx)
              (tempname "update_value") builder
          in
          pure castedvalue
        else
          (* Build alloca for the value and pass the alloca. *)
          let alloca =
            Llvm.build_alloca vty_ll (tempname "update_value") builder
          in
          let _ = Llvm.build_store value_ll alloca builder in
          let castedalloca =
            Llvm.build_pointercast alloca (void_ptr_type llctx)
              (tempname "update_value") builder
          in
          pure castedalloca
    | None ->
        (* No value to pass, just pass a null pointer. *)
        pure (void_ptr_nullptr llctx)
  in
  (* Insert a call to update the value. *)
  let _ =
    Llvm.build_call f
      [| execptr; fieldname; tyd; num_indices; indices_buf; value_ll |]
      "" builder
  in
  pure genv

(* Translate stmts into LLVM-IR by inserting instructions through irbuilder, *)
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
      if List.equal Base.Poly.( = ) (Array.to_list struct_types) evars_typs_ll
      then pure ()
      else errm0 "closure environment types mismatch."
  in

  let%bind _ =
    foldM stmts ~init:genv ~f:(fun accenv (stmt, _) ->
        match stmt with
        | LocalDecl x ->
            (* Local variables are stored to and loaded from allocas.
             * Running the mem2reg pass will take care of this. *)
            let%bind xty_ll = id_typ_ll llmod x in
            let xll = Llvm.build_alloca xty_ll (Identifier.get_id x) builder in
            pure
            @@ {
                 accenv with
                 llvals = (Identifier.get_id x, Local xll) :: accenv.llvals;
               }
        | LibVarDecl v ->
            let%bind vty_ll = id_typ_ll llmod v in
            let vll =
              (* Global variables need to be zero initialized.
               * Only declaring would lead to an `extern` linkage. *)
              let init = Llvm.const_null vty_ll in
              define_global (Identifier.get_id v) init llmod ~const:false
                ~unnamed:false
            in
            pure
              {
                accenv with
                llvals = (Identifier.get_id v, Global vll) :: accenv.llvals;
              }
        | Bind (x, e) ->
            (* Find the allocation for x and store to it. *)
            let%bind xll = resolve_id_memloc accenv x in
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
            if Base.Poly.(Llvm.classify_type fun_ty <> Llvm.TypeKind.Function)
            then errm0 "Expected function type."
            else
              (* The first argument of fdecl is to the environment *)
              let%bind env_ty_p = array_get (Llvm.param_types fun_ty) 0 in
              let%bind env_ty = ptr_element_type env_ty_p in
              let%bind _ = validate_envvars_type env_ty evars in
              (* Allocate the environment. *)
              let%bind envp =
                GenSrtlDecls.build_salloc env_ty
                  (tempname (Identifier.get_id fname ^ "_envp"))
                  builder
              in
              let%bind clo_ty_ll = id_typ_ll llmod fname in
              let%bind resolved_fname = resolve_id accenv fname in
              match resolved_fname with
              | FunDecl fd ->
                  let%bind cloval =
                    build_closure builder clo_ty_ll fd fname envp
                  in
                  (* Now we bind fname to cloval instead of the function declaration it originally was bound to. *)
                  pure
                    {
                      accenv with
                      llvals =
                        (Identifier.get_id fname, CloP (cloval, env_ty))
                        :: accenv.llvals;
                    }
              | _ ->
                  errm1
                    (sprintf "%s did not resolve to global declaration."
                       (Identifier.get_id fname))
                    (Identifier.get_rep fname).ea_loc )
        | StoreEnv (envvar, v, (fname, envvars)) -> (
            let%bind resolved_fname = resolve_id accenv fname in
            match resolved_fname with
            | CloP (cloval, envty) ->
                let%bind _ = validate_envvars_type envty envvars in
                (* Get the second component of cloval (the envptr) and cast it to right type. *)
                let%bind envvoidp =
                  build_extractvalue cloval 1
                    (tempname (Identifier.get_id fname ^ "_envp"))
                    builder
                in
                let envp =
                  Llvm.build_bitcast envvoidp (Llvm.pointer_type envty)
                    (tempname (Identifier.get_id fname ^ "_envp"))
                    builder
                in
                (* Search for envvar in envvars and get its index. *)
                let%bind i =
                  match
                    List.findi envvars ~f:(fun _ (envvar', _) ->
                        Identifier.equal envvar envvar')
                  with
                  | Some (i, _) -> pure i
                  | None ->
                      errm1
                        (sprintf "%s not found in env of %s."
                           (Identifier.get_id envvar) (Identifier.get_id fname))
                        (Identifier.get_rep fname).ea_loc
                in
                (* Store v into envp[i] *)
                let envp_i =
                  Llvm.build_struct_gep envp i
                    (tempname
                       ( Identifier.get_id fname ^ "_env_"
                       ^ Identifier.get_id envvar ))
                    builder
                in
                let%bind vresolved = resolve_id_value accenv (Some builder) v in
                let _ = Llvm.build_store vresolved envp_i builder in
                (* This operation doesn't affect our codegen environment. *)
                pure accenv
            | _ ->
                errm1
                  (sprintf "expected %s to resolve to closure."
                     (Identifier.get_id fname))
                  (Identifier.get_rep fname).ea_loc )
        | LoadEnv (v, envvar, (fname, envvars)) -> (
            match accenv.envparg with
            | Some envp ->
                let%bind envty = ptr_element_type (Llvm.type_of envp) in
                let%bind _ = validate_envvars_type envty envvars in
                (* Search for envvar in envvars and get its index. *)
                let%bind i =
                  match
                    List.findi envvars ~f:(fun _ (envvar', _) ->
                        Identifier.equal envvar envvar')
                  with
                  | Some (i, _) -> pure i
                  | None ->
                      errm1
                        (sprintf "%s not found in env of %s."
                           (Identifier.get_id envvar) (Identifier.get_id fname))
                        (Identifier.get_rep fname).ea_loc
                in
                (* Load from envp[i] into v *)
                let envp_i =
                  Llvm.build_struct_gep envp i
                    (tempname
                       ( Identifier.get_id fname ^ "_env_"
                       ^ Identifier.get_id envvar ))
                    builder
                in
                let loadi =
                  Llvm.build_load envp_i
                    (tempname (Identifier.get_id v ^ "_envload"))
                    builder
                in
                (* Put the loaded value into a local variable, so that we can bind it as a Local. *)
                let loadi_alloca =
                  Llvm.build_alloca (Llvm.type_of loadi) (Identifier.get_id v)
                    builder
                in
                let _ = Llvm.build_store loadi loadi_alloca builder in
                pure
                  {
                    accenv with
                    llvals =
                      (Identifier.get_id v, Local loadi_alloca) :: accenv.llvals;
                  }
            | None ->
                errm1
                  (sprintf "expected envparg when compiling fundef %s."
                     (Identifier.get_id fname))
                  (Identifier.get_rep fname).ea_loc )
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
                    new_block_after llctx (Identifier.get_id jname) match_block
                  in
                  let builder' = Llvm.builder_at_end llctx jblock in
                  let%bind () = genllvm_block genv_succblock builder' jsts in
                  (* Bind this block. *)
                  pure
                    ( {
                        genv_succblock with
                        joins =
                          (Identifier.get_id jname, jblock)
                          :: genv_succblock.joins;
                      },
                      jblock )
              | None -> pure (genv_succblock, succblock)
            in
            let%bind ollval = resolve_id_value accenv (Some builder) o in
            (* Load the tag from ollval. *)
            let tagval_gep =
              Llvm.build_struct_gep ollval 0
                (tempname (Identifier.get_id o ^ "_tag"))
                builder
            in
            let tagval =
              Llvm.build_load tagval_gep
                (tempname (Identifier.get_id o ^ "_tag"))
                builder
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
                               (Identifier.get_id o))
                            (Identifier.get_rep o).ea_loc
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
                         (Identifier.get_id o))
                      (Identifier.get_rep o).ea_loc
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
                          Llvm.build_alloca (Llvm.type_of ollval)
                            (Identifier.get_id v) builder'
                        in
                        let _ = Llvm.build_store ollval valloca builder' in
                        {
                          genv_joinblock with
                          llvals =
                            (Identifier.get_id v, Local valloca)
                            :: genv_joinblock.llvals;
                        }
                  in
                  let%bind () = genllvm_block genv' builder' clause_stmts in
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
                          (tempname (Identifier.get_id o))
                          builder'
                      in
                      let celm_tys = Llvm.struct_element_types llcty in
                      (* The LLVM struct type will have one additional field for the tag. *)
                      if Array.length celm_tys <> List.length cargs + 1 then
                        errm1
                          (sprintf
                             "matching %s: Constructor %s argument mismatch."
                             (Identifier.get_id o) cname)
                          (Identifier.get_rep o).ea_loc
                      else
                        (* Generate binding for each binder in cargs. *)
                        let binds_rev =
                          List.foldi cargs ~init:[] ~f:(fun i acc c ->
                              match c with
                              | Wildcard -> acc
                              | Binder v ->
                                  (* Bind v as a local variable. *)
                                  let vgep =
                                    (* Count from 1 since the 0th struct member is the tag. *)
                                    Llvm.build_struct_gep cobjp (i + 1)
                                      (tempname (Identifier.get_id v ^ "_gep"))
                                      builder'
                                  in
                                  let vloaded =
                                    Llvm.build_load vgep
                                      (tempname (Identifier.get_id v ^ "_load"))
                                      builder'
                                  in
                                  let valloca =
                                    Llvm.build_alloca (Llvm.type_of vloaded)
                                      (Identifier.get_id v) builder'
                                  in
                                  let _ =
                                    Llvm.build_store vloaded valloca builder'
                                  in
                                  (Identifier.get_id v, Local valloca) :: acc)
                        in
                        let genv' =
                          {
                            genv_joinblock with
                            llvals = List.rev binds_rev @ genv_joinblock.llvals;
                          }
                        in
                        let%bind () = genllvm_block genv' builder' body in
                        pure
                          (Llvm.const_int (Llvm.i8_type llctx) tag, clause_block)
                  | _ ->
                      errm1
                        (sprintf "matching %s: expected Constructor pattern."
                           (Identifier.get_id o))
                        (Identifier.get_rep o).ea_loc)
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
        | CallProc (procname, args) -> (
            let%bind procreslv = resolve_id accenv procname in
            let all_args =
              (* prepend append _amount and _sender to args *)
              let amount_typ = PrimType (Uint_typ Bits128) in
              let sender_typ = PrimType (Bystrx_typ address_length) in
              let lc = (Identifier.get_rep procname).ea_loc in
              Identifier.mk_id ContractUtil.MessagePayload.amount_label
                { ea_tp = Some amount_typ; ea_loc = lc; ea_auxi = None }
              :: Identifier.mk_id ContractUtil.MessagePayload.sender_label
                   { ea_tp = Some sender_typ; ea_loc = lc; ea_auxi = None }
              :: args
            in
            match procreslv with
            | FunDecl fptr ->
                let%bind _ =
                  build_call_helper llmod accenv builder procname fptr all_args
                    None
                in
                pure accenv
            | _ ->
                fail1
                  (sprintf
                     "GenLlvm: genllvm_stmts: internal error: Procedure call \
                      %s didn't resolve to defined function."
                     (Identifier.get_id procname))
                  (Identifier.get_rep procname).ea_loc )
        | MapGet (x, m, indices, fetch_val) ->
            genllvm_fetch_state llmod accenv builder x m indices fetch_val
        | Load (x, f) -> genllvm_fetch_state llmod accenv builder x f [] true
        | MapUpdate (m, indices, valopt) ->
            genllvm_update_state llmod accenv builder m indices valopt
        | Store (f, x) ->
            genllvm_update_state llmod accenv builder f [] (Some x)
        | _ -> pure accenv)
  in
  pure ()

(* Generate LLVM-IR for a block of statements.
 * Inserts a terminator instruction when needed.
 * If the sequence of statements have no natural successor
 * (branch/return) and nosucc_retvoid is set, then a "return void"
 * is automatically appended. Otherwise, having no successor is an error. *)
and genllvm_block ?(nosucc_retvoid = false) genv builder stmts =
  let%bind _ = genllvm_stmts genv builder stmts in
  let b = Llvm.insertion_block builder in
  let fname = Llvm.value_name (Llvm.block_parent b) in
  match Llvm.block_terminator b with
  | Some _ -> pure ()
  | None -> (
      match (genv.succblock, nosucc_retvoid) with
      | Some sb, _ ->
          let _ = Llvm.build_br sb builder in
          pure ()
      | None, true ->
          let _ = Llvm.build_ret_void builder in
          pure ()
      | _ ->
          fail0
            (sprintf
               "GenLlvm: genllvm_block: internal error: Unable to determine \
                successor block in %s."
               fname) )

let genllvm_closures llmod tydescrs topfuns =
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
        let envty_name =
          tempname (Identifier.get_id !(cr.thisfun).fname ^ "_env")
        in
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
              (Identifier.get_id !(cr.thisfun).fname)
              ret_ty_ll
              (penv_ty_ll :: args_ty_ll')
          else
            (* returns void (return value is via the stack),
             * env pointer type, type of pointer to return type, argument types *)
            let fargs_ty =
              penv_ty_ll :: Llvm.pointer_type ret_ty_ll :: args_ty_ll'
            in
            scilla_function_decl ~is_internal:true llmod
              (Identifier.get_id !(cr.thisfun).fname)
              (Llvm.void_type ctx) fargs_ty
        in
        pure @@ ((Identifier.get_id !(cr.thisfun).fname, decl) :: accenv))
  in

  let genv_fdecls =
    {
      llvals = List.map fdecls ~f:(fun (fname, decl) -> (fname, FunDecl decl));
      joins = [];
      retp = None;
      envparg = None;
      succblock =
        None (* No successor blocks when we begin to compile a function *);
      tdmap = tydescrs;
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
              (Identifier.get_rep fid).ea_loc
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
                     (Identifier.get_id varg) (Identifier.get_id fid))
                  (Identifier.get_rep fid).ea_loc
              in
              let%bind arg_llval' =
                if can_pass_by_val dl sty_llty then
                  if Base.Poly.(sty_llty = Llvm.type_of arg_llval) then
                    pure arg_llval
                  else arg_mismatch_err
                else if
                  Base.Poly.(
                    Llvm.pointer_type sty_llty = Llvm.type_of arg_llval)
                then
                  pure
                    (Llvm.build_load arg_llval (Identifier.get_id varg) builder)
                else arg_mismatch_err
              in
              pure
                ( {
                    accum_genv with
                    llvals =
                      (Identifier.get_id varg, FunArg arg_llval')
                      :: accum_genv.llvals;
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

(* Create globals for lib entries and a function to initialize them.
 * TODO: Library values are compile time constexpr values. We cannot
 *   however, currently, have const initializers for these globals
 *   because they may be dependent on executing functions or builtins.
 *   In the future we must use `Eval`, during compilation, to produce
 *   Scilla values and use those to initialize these globals.
 *)
let create_init_libs genv_fdecls llmod lstmts =
  let ctx = Llvm.module_context llmod in
  let%bind f =
    scilla_function_defn ~is_internal:false llmod "_init_libs"
      (Llvm.void_type ctx) []
  in
  let irbuilder = Llvm.builder_at_end ctx (Llvm.entry_block f) in
  let%bind () =
    genllvm_block ~nosucc_retvoid:true genv_fdecls irbuilder lstmts
  in
  (* genllvm_block creates bindings for LibVarDecls that we don't get back.
   * Let's just recreate them here. *)
  let%bind genv_libs =
    foldM lstmts ~init:genv_fdecls ~f:(fun accenv (lstmt, _) ->
        match lstmt with
        | LibVarDecl v -> (
            match Llvm.lookup_global (Identifier.get_id v) llmod with
            | Some g ->
                pure
                  {
                    accenv with
                    llvals = (Identifier.get_id v, Global g) :: accenv.llvals;
                  }
            | None ->
                fail1
                  (sprintf
                     "GenLlvm: create_init_libs: internal error: library name \
                      %s not already bound to global"
                     (Identifier.get_id v))
                  (Identifier.get_rep v).ea_loc )
        | _ -> pure accenv)
  in
  pure genv_libs

(* Generate LLVM function for a procedure or transition. *)
let genllvm_component genv llmod comp =
  let ctx = Llvm.module_context llmod in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in

  let amount_typ = PrimType (Uint_typ Bits128) in
  let sender_typ = PrimType (Bystrx_typ address_length) in
  let comp_loc = (Identifier.get_rep comp.comp_name).ea_loc in
  (* Prepend _amount and _sender to param list. *)
  let params =
    ( Identifier.mk_id ContractUtil.MessagePayload.amount_label
        { ea_tp = Some amount_typ; ea_loc = comp_loc; ea_auxi = None },
      amount_typ )
    :: ( Identifier.mk_id ContractUtil.MessagePayload.sender_label
           { ea_tp = Some sender_typ; ea_loc = comp_loc; ea_auxi = None },
         sender_typ )
    :: comp.comp_params
  in
  (* Convert params to LLVM (name,type) list. *)
  let%bind (_, ptys, _), params' =
    let%bind params' =
      mapM params ~f:(fun (pname, ty) ->
          let%bind llty = genllvm_typ_fst llmod ty in
          (* Check if the value is to be passed directly or through the stack. *)
          if can_pass_by_val dl llty then pure (pname, llty, true)
          else pure (pname, Llvm.pointer_type llty, false))
    in
    pure (List.unzip3 params', params')
  in
  (* Generate an empty function with the params we have computed. *)
  let%bind f =
    (* void component_name (_amount : Uint128, _sender : ByStr20, params...) *)
    (* We don't have procedures that can return values yet. *)
    scilla_function_defn ~is_internal:true llmod
      (* This is an internal function, hence a different name. We'll have a
       * wrapper for transitions later on that is exposed. *)
      (tempname (Identifier.get_id comp.comp_name))
      (Llvm.void_type ctx) ptys
  in
  let builder = Llvm.builder_at_end ctx (Llvm.entry_block f) in
  (* Bind parameters into genv for generating the body. *)
  let args_f = Array.to_list (Llvm.params f) in
  if List.length args_f <> List.length params' then
    fail0
      "GenLlvm: genllvm_component: internal error: incorrect number of args."
  else
    (* We don't have foldM3, so need to zip and do foldM. *)
    let params_args = List.zip_exn params' args_f in
    let%bind genv_args =
      foldM params_args ~init:genv
        ~f:(fun accenv ((pname, pty, pass_by_val), arg) ->
          if pass_by_val then
            let () = Llvm.set_value_name (Identifier.get_id pname) arg in
            pure
              {
                accenv with
                llvals = (Identifier.get_id pname, FunArg arg) :: accenv.llvals;
              }
          else if
            (* This is a pass by stack pointer, so load the value. *)
            Base.Poly.(Llvm.classify_type pty <> Llvm.TypeKind.Pointer)
          then
            fail0
              "GenLlvm: genllvm_component: internal error: type of non \
               pass-by-val arg is not pointer."
          else
            let () =
              Llvm.set_value_name (tempname (Identifier.get_id pname)) arg
            in
            let loaded_arg =
              Llvm.build_load arg (Identifier.get_id pname) builder
            in
            pure
              {
                accenv with
                llvals =
                  (Identifier.get_id pname, FunArg loaded_arg) :: accenv.llvals;
              })
    in
    (* Generate the body. *)
    let%bind () =
      genllvm_block ~nosucc_retvoid:true genv_args builder comp.comp_body
    in
    (* Bind the component name for later use. *)
    let genv_comp =
      {
        genv with
        llvals = (Identifier.get_id comp.comp_name, FunDecl f) :: genv.llvals;
      }
    in

    match comp.comp_type with
    | CompProc -> pure genv_comp
    | CompTrans ->
        (* Generate a wrapper around the transition to be called from the VM.
           * The virtual machine cannot have function declarations for transitions
           * (because it cannot statically know all transitions it will ever execute).
           * For this reason, it can only call transitions when all transitions have
           * the same signature. So we create such a transition wrapper:
           *   void foo ( void *params )
           * Here params is a pointer to a memory buffer that contains all parameters. *)
        let%bind wf =
          scilla_function_defn ~is_internal:false llmod
            (Identifier.get_id comp.comp_name)
            (Llvm.void_type ctx) [ void_ptr_type ctx ]
        in
        let builder = Llvm.builder_at_end ctx (Llvm.entry_block wf) in
        let%bind buffer_voidp = array_get (Llvm.params wf) 0 in
        (* Cast the argument to ( i8* ) for getting byte based offsets for each param. *)
        let bufferp =
          Llvm.build_pointercast buffer_voidp
            (Llvm.pointer_type (Llvm.i8_type ctx))
            (tempname "params") builder
        in
        let%bind _, args_rev =
          foldM params' ~init:(0, [])
            ~f:(fun (offset, arglist) (pname, pty, pass_by_val) ->
              let gep =
                Llvm.build_gep bufferp
                  [| Llvm.const_int (Llvm.i32_type ctx) offset |]
                  (tempname (Identifier.get_id pname))
                  builder
              in
              let%bind arg, inc =
                if pass_by_val then
                  let pty_ptr =
                    (* Pointer to our current argument. *)
                    Llvm.build_pointercast gep (Llvm.pointer_type pty)
                      (tempname (Identifier.get_id pname))
                      builder
                  in
                  (* Load the value from buffer and pass that. *)
                  pure
                    ( Llvm.build_load pty_ptr (Identifier.get_id pname) builder,
                      llsizeof dl pty )
                else
                  let arg =
                    Llvm.build_pointercast gep pty
                      (tempname (Identifier.get_id pname))
                      builder
                  in
                  let%bind pty_elty = ptr_element_type pty in
                  pure (arg, llsizeof dl pty_elty)
              in
              pure (offset + inc, arg :: arglist))
        in
        (* Insert a call to our internal function implementing the transition. *)
        let _ =
          Llvm.build_call f (Array.of_list (List.rev args_rev)) "" builder
        in
        let _ = Llvm.build_ret_void builder in
        pure genv_comp

(* Declare and zero initialize global "_execptr" : ( void* ) *)
let gen_execid llmod =
  let llctx = Llvm.module_context llmod in
  define_global "_execptr" (void_ptr_nullptr llctx) llmod ~const:false
    ~unnamed:false

(* Generate an LLVM module for a Scilla module. *)
let genllvm_module (cmod : cmodule) =
  let llcontext = Llvm.create_context () in
  let llmod =
    Llvm.create_module llcontext (Identifier.get_id cmod.contr.cname)
  in
  let _ = prepare_target llmod in
  let _ = gen_execid llmod in

  (* Gather all the top level functions. *)
  let topclos = gather_closures_cmod cmod in
  let%bind tydescr_map =
    TypeDescr.generate_type_descr_cmod llmod topclos cmod
  in
  (* Generate LLVM functions for all closures. *)
  let%bind genv_fdecls = genllvm_closures llmod tydescr_map topclos in
  (* Create a function to initialize library values. *)
  let%bind genv_libs = create_init_libs genv_fdecls llmod cmod.lib_stmts in
  (* Generate LLVM functions for procedures and transitions. *)
  let%bind _genv_comps =
    foldM cmod.contr.ccomps ~init:genv_libs ~f:(fun accenv comp ->
        genllvm_component accenv llmod comp)
  in
  (* Build a table containing all type descriptors.
   * This is needed for SRTL to parse types from JSONs *)
  let%bind _ =
    TypeDescr.build_tydescr_table llmod ~global_array_name:"_tydescr_table"
      ~global_array_length_name:"_tydescr_table_length" tydescr_map
  in

  (* printf "Before verify module: \n%s\n" (Llvm.string_of_llmodule llmod); *)
  match Llvm_analysis.verify_module llmod with
  | None ->
      DebugMessage.plog
        (sprintf "Before optimizations: \n%s\n" (Llvm.string_of_llmodule llmod));
      (* optimize_module llmod; *)
      pure (Llvm.string_of_llmodule llmod)
  | Some err -> fail0 ("GenLlvm: genllvm_module: internal error: " ^ err)

(* Generate an LLVM module for a statement sequence. *)
let genllvm_stmt_list_wrapper stmts =
  let llcontext = Llvm.create_context () in
  let llmod = Llvm.create_module llcontext "scilla_expr" in
  let _ = prepare_target llmod in
  let _ = gen_execid llmod in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in

  (* Gather all the top level functions. *)
  let topclos = gather_closures stmts in
  let%bind tydescr_map =
    TypeDescr.generate_type_descr_stmts_wrapper llmod topclos stmts
  in
  let%bind genv_fdecls = genllvm_closures llmod tydescr_map topclos in
  (* Create a function to initialize library values. *)
  let%bind genv_libs = create_init_libs genv_fdecls llmod [] in

  (* Create a function to house the instructions. *)
  let%bind fty, retty =
    (* Let's look at the last statement and try to infer a return type. *)
    match List.last stmts with
    | Some (Ret v, _) ->
        let%bind retty = rep_typ (Identifier.get_rep v) in
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
  let%bind f =
    scilla_function_defn ~is_internal:true llmod (tempname "scilla_expr")
      (Llvm.return_type fty)
      (Array.to_list (Llvm.param_types fty))
  in
  let%bind init_env =
    if Base.Poly.(Llvm.void_type llcontext = Llvm.return_type fty) then
      (* If return type is void, then second parameter is the pointer to return value. *)
      let%bind retp = array_get (Llvm.params f) 1 in
      pure { genv_libs with retp = Some retp }
    else pure { genv_libs with retp = None }
  in
  let irbuilder = Llvm.builder_at_end llcontext (Llvm.entry_block f) in
  let%bind _ = genllvm_block init_env irbuilder stmts in

  (* Generate a wrapper function scilla_main that'll call print on the result value. *)
  let%bind printer = GenSrtlDecls.decl_print_scilla_val llmod in
  let%bind mainb =
    let%bind fdef =
      scilla_function_defn ~is_internal:false llmod "scilla_main"
        (Llvm.void_type llcontext) []
    in
    pure @@ Llvm.entry_block fdef
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
          if not (is_boxed_typ retty) then
            let%bind _ =
              match retty with
              | PrimType _
              (* PrimType values aren't boxed. Assert that. *)
                when Base.Poly.(
                       Llvm.classify_type retty_ll <> Llvm.TypeKind.Pointer) ->
                  pure ()
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

  (* printf "Before verify module: \n%s\n" (Llvm.string_of_llmodule llmod); *)
  match Llvm_analysis.verify_module llmod with
  | None ->
      DebugMessage.plog
        (sprintf "Before optimizations: \n%s\n" (Llvm.string_of_llmodule llmod));
      (* optimize_module llmod; *)
      pure (Llvm.string_of_llmodule llmod)
  | Some err ->
      fail0 ("GenLlvm: genllvm_stmt_list_wrapper: internal error: " ^ err)
