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
 * Initialization, deployment and other globals:
 *  _execptr : ( ScillaJIT** ) A pointer to the JIT instance.
 *  _gasrem : ( uint64_t * ) Pointer to the gas counter.
 *  _init_libs : ( void (void) ) Initializes Scilla library entries.
 *  _init_state : ( void (void) ) Initializes all fields into the database.
 *
 * Representation of Scilla types in SRTL:
 *  SRTL needs to know the type of a value for many operations
 *  (for example, to print it to a JSON). Towards this cause, Scilla types
 *  are encoded into "type descriptors". These are C structs, all defined in
 *  ScillaTypes.h in the SRTL code.
 *
 *  This compiler encodes Scilla types into these type descriptors and a global
 *  array `_tydescr_table` (with its length in `_tydescr_table_length`) is
 *  created to hold type descriptors of all types in the module being compiled.
 *
 *  To enable SRTL to dynamically check contract and transition parameters,
 *  their type descriptors are generated too. See SRTL.ml for
 *  ParamDescr and TransDescr struct definitions.
 *    Contract parameters:
 *      - `_contract_parameters` is an array of ParmDescr.
 *      - `_contract_parameters_length`: uint32_t.
 *    Transition parameters:
 *      - `_transition_parameters` is an array of TransDescr.
 *      - `_transition_parameters_length`: uint32_t.
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
 * - Map KeyT ValT : These are represented by a pointer to a type Map_KeyT_ValT.
 *    The values are all created and operated on by SRTL functions. The
 *    SRTL Map functions operate on "void*" (to represent all Map types)
 *    and take a type descriptor argument.
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
 * - Message, Event and Exceptions.
 *     All three of these are fully boxed (represented by a pointer) and have the
 *     following common memory layout.
 *       <{ i8 tag, (String, TypDescr *, field_value)* }>
 *     i.e., a contiguous memory area with
 *       1. First byte denoting the number of fields the MsgObj has
 *       2. A list of triples (number of such triples is given by (1)), with each
 *            (a) String : String object representing the field name.
 *            (b) A type descriptor pointer, for the type of the field's value.
 *            (c) The value itself.
 * - BNum: Fully boxed, represented with just a pointer ( i8* / void* )
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
 *  Dynamic dispatch tables for TFunMap (monomorphized versions of expressions):
 *    A TFunMap expressions is represented as an array of closures. Each of these
 *    closures is of type `() -> X` where `X` is the type of the monomorphized
 *    version of the sub-expression which was in the `TFun` Scilla expression
 *    before monomorphization. EnumTAppArgs.lookup_typ_idx provides a unique
 *    index for every type that may be used to index into this array.
 *    For types (i.e., it's index) that aren't specialized here, the closure
 *    pointers will be nullptr.
 *    Unlike normal closures (described above), closures here are represented as
 *    { void*, void* } for the function pointer (first component) to remain general.
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
open Result.Let_syntax
open Scilla_base
module Literal = Literal.GlobalLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open MonadUtil
open Syntax
open UncurriedSyntax.Uncurried_Syntax
module TU = TypeUtilities
open ClosuredSyntax
open LoweringUtils
open LLGenUtils
open Printf
open TypeLLConv

let array_get arr idx =
  try pure @@ arr.(idx)
  with Invalid_argument _ -> fail0 "GenLlvm: array_get: Invalid array index"

(* Convert a Scilla literal (compile time constant value) into LLVM-IR. *)
let rec genllvm_literal llmod builder l =
  let ctx = Llvm.module_context llmod in
  let i8_type = Llvm.i8_type ctx in
  let%bind sty = TypeUtilities.literal_type l in
  let%bind llty, llctys = genllvm_typ llmod sty in

  match l with
  | StringLit s ->
      (* Represented by scilla_string_ty. *)
      define_string_value llmod llty ~name:(tempname "stringlit") ~strval:s
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
           (match il with
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
               |])
  | UintLit uil ->
      pure
      @@ Llvm.const_named_struct llty
           (match uil with
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
               |])
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
      let%bind lits_ll = mapM lits ~f:(genllvm_literal llmod builder) in
      (* Prepend the tag to the constructor object we're building. *)
      let lits' = Llvm.const_int i8_type tag :: lits_ll in
      let ctrval = Llvm.const_named_struct llcty (Array.of_list lits') in
      (* Since ADTValues are boxed, i.e., represented by a pointer to the struct,
       * we are forced to create an unnamed global constant to get an address. *)
      let p_ctrval =
        define_global ~const:true ~unnamed:true (tempname "adtlit") ctrval llmod
      in
      (* The pointer to the constructor type should be cast to the adt type. *)
      let _p_adtval = Llvm.const_bitcast p_ctrval llty in
      (* Unless there's a constant propagation implemented, we can't have
       * ADTValue in the IR. When it is implemented, return p_adtval. *)
      fail0 "GenLlvm: genllvm_literal: ADT literals cannot exist statically."
  | Map ((kt, vt), m) ->
      if Caml.Hashtbl.length m = 0 then
        SRTL.build_new_empty_map llmod builder (MapType (kt, vt))
      else
        (* Without a constant propagation like optimization pass, we can't
         * can't non-empty Map values in the IR. Insert m's values into
         * the map when we end up having such an optimization. *)
        fail0
          "GenLlvm: genllvm_literal: Non-empty Map literals cannot exist \
           statically."
  | BNum b -> SRTL.build_new_bnum llmod builder b
  | Msg _ ->
      fail0
        "GenLlvm: genllvm_literal: Message literals cannot exist statically."

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
  (* Pair of closure record and a pointer to the allocated closure env. *)
  | CloP of (Llvm.llvalue * Llvm.llvalue)

type gen_env = {
  (* Resolve input AST name to a processed LLVM value *)
  llvals : (eannot Identifier.t * value_scope) list;
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
  (* type index map. *)
  timap : EnumTAppArgs.typ_idx_map;
}

let try_resolve_id genv id =
  List.Assoc.find genv.llvals ~equal:Identifier.equal id

(* Resolve a name from the identifier. *)
let resolve_id genv id =
  match try_resolve_id genv id with
  | Some scope -> pure scope
  | None ->
      fail1
        (sprintf "GenLlvm: internal error: cannot resolve id %s."
           (Identifier.as_string id))
        (Identifier.get_rep id).ea_loc

(* Resolve id, and if it's a memory location, load it. *)
let resolve_id_value env builder_opt id =
  let%bind resolved = resolve_id env id in
  match resolved with
  | FunDecl llval | FunArg llval | CloP (llval, _) -> pure llval
  | Local llval | Global llval -> (
      match builder_opt with
      | Some builder ->
          pure
          @@ Llvm.build_load llval (tempname (Identifier.as_string id)) builder
      | None ->
          fail1
            (sprintf
               "GenLlvm: resolve_id: internal error: llbuilder not provided to \
                load from memory for %s."
               (Identifier.as_string id))
            (Identifier.get_rep id).ea_loc)

(* Resolve id to an alloca / global memory location or fail. *)
let resolve_id_memloc genv id =
  let%bind xresolv = resolve_id genv id in
  match xresolv with
  | Local a | Global a -> pure a
  | _ ->
      fail1
        (sprintf
           "GenLlvm: resolve_id_local: %s did not resolve to a memory location."
           (Identifier.as_string id))
        (Identifier.get_rep id).ea_loc

let resolve_jblock genv b =
  match
    List.Assoc.find genv.joins ~equal:String.( = ) (Identifier.as_string b)
  with
  | Some joinp -> pure joinp
  | None ->
      fail1
        (sprintf "GenLlvm: internal error: cannot resolve join point %s."
           (Identifier.as_string b))
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
         (Identifier.as_string fname))
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
        (tempname (Identifier.as_string fname))
        builder
    in
    let envp_void =
      Llvm.build_pointercast envp (void_ptr_type ctx)
        (tempname (Identifier.as_string fname ^ "_env_voidp"))
        builder
    in
    let%bind cloval =
      build_insertvalue tmp envp_void 1
        (tempname (Identifier.as_string fname ^ "_cloval"))
        builder
    in
    pure cloval

(* Build call for Scilla function applications (App). *)
let build_call_helper llmod genv builder discope callee_id callee args
    envptr_opt =
  let llctx = Llvm.module_context llmod in
  let envptr = match envptr_opt with Some envptr -> [ envptr ] | None -> [] in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  let fname, sloc =
    (Identifier.as_string callee_id, (Identifier.get_rep callee_id).ea_loc)
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
          let%bind argmem =
            build_alloca arg_ty
              (tempname (fname ^ "_" ^ Identifier.as_string arg))
              builder
          in
          let%bind arg' = resolve_id_value genv (Some builder) arg in
          let _ = Llvm.build_store arg' argmem builder in
          pure argmem)
  in
  let param_tys = Llvm.param_types fty in
  (* Scilla function application (App) calls have an envptr argument. *)
  let num_call_args = List.length args_ll + List.length envptr in
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
    let call =
      Llvm.build_call callee (Array.of_list (envptr @ args_ll)) callname builder
    in
    let%bind () = DebugInfo.set_inst_loc llctx discope call sloc in
    pure call
  else if Array.length param_tys = num_call_args + 1 then
    (* Allocate a temporary stack variable for the return value. *)
    let%bind pretty_ty = array_get param_tys (List.length envptr) in
    let%bind retty = ptr_element_type pretty_ty in
    let%bind alloca =
      build_alloca retty (tempname (fname ^ "_retalloca")) builder
    in
    let call =
      Llvm.build_call callee
        (Array.of_list (envptr @ alloca :: args_ll))
        "" builder
    in
    let%bind () = DebugInfo.set_inst_loc llctx discope call sloc in
    (* Load from ret_alloca. *)
    pure @@ Llvm.build_load alloca (tempname (fname ^ "_ret")) builder
  else
    fail1
      (sprintf "%s %s."
         ("GenLlvm: genllvm_expr: internal error: Incorrect number of arguments"
        ^ " when compiling function application")
         fname)
      sloc

let genllvm_expr genv builder discope (e, erep) =
  let llmod =
    Llvm.insertion_block builder |> Llvm.block_parent |> Llvm.global_parent
  in
  let llctx = Llvm.module_context llmod in

  match e with
  | Literal l -> genllvm_literal llmod builder l
  | Var v -> resolve_id_value genv (Some builder) v
  | Constr (cname, _, cargs) ->
      let%bind sty = rep_typ erep in
      let%bind llty, llctys = genllvm_typ llmod sty in
      let%bind llcty, tag = get_ctr_struct llctys (Identifier.get_id cname) in
      let%bind cargs_ll =
        mapM cargs ~f:(resolve_id_value genv (Some builder))
      in
      (* Append the tag to the struct elements. *)
      let cargs_ll' = Llvm.const_int (Llvm.i8_type llctx) tag :: cargs_ll in
      let%bind cmem = SRTL.build_salloc llcty (tempname "adtval") builder in
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
                 "GenLlvm: genllvm_expr: Expected closure for %s with \
                  non-empty environment."
                 (Identifier.as_string fname))
              erep.ea_loc
          else
            (* Build a closure object with empty environment. *)
            let envp = void_ptr_nullptr llctx in
            let%bind clo_ty_ll = id_typ_ll llmod fname in
            let%bind cloval = build_closure builder clo_ty_ll gv fname envp in
            pure cloval
      | _ ->
          fail1
            (sprintf "GenLlvm: genllvm_expr: Incorrect resolution of %s."
               (Identifier.as_string fname))
            erep.ea_loc)
  | TFunMap tbodies -> (
      let%bind t = rep_typ erep in
      let%bind t' = genllvm_typ_fst llmod t in
      match tbodies with
      (* If there are no specializations, return a null value. *)
      | [] -> pure (Llvm.const_null t')
      | (curt, cl) :: rest ->
          let build_closure_all envp tbodies =
            mapM tbodies ~f:(fun (t, tbody) ->
                let fname = !(tbody.thisfun).fname in
                match%bind resolve_id genv fname with
                | FunDecl gv ->
                    let%bind clo_ty = id_typ_ll llmod fname in
                    let%bind closure =
                      build_closure builder clo_ty gv fname envp
                    in
                    pure (t, closure)
                | _ ->
                    fail1
                      (sprintf
                         "GenLlvm: genllvm_expr: Expected FunDecl resolution")
                      erep.ea_loc)
          in
          let%bind tbodies' =
            match%bind resolve_id genv (fst cl.envvars) with
            | CloP (cp, envp) ->
                let%bind rest' = build_closure_all envp rest in
                pure @@ (curt, cp) :: rest'
            | FunDecl _ ->
                (* Looks like no AllocCloEnv, assert empty environment. *)
                if not (List.is_empty (snd cl.envvars)) then
                  fail1
                    (sprintf
                       "GenLlvm: genllvm_expr: Expected closure for for \
                        non-empty environment.")
                    erep.ea_loc
                else
                  let envp = void_ptr_nullptr llctx in
                  build_closure_all envp tbodies
            | _ ->
                fail1
                  (sprintf "GenLlvm: genllvm_expr: Incorrect resolution of %s."
                     (Identifier.as_string (fst cl.envvars)))
                  erep.ea_loc
          in
          (* Allocate a dyndisp table. *)
          let%bind clo_ty = ptr_element_type t' in
          let ddt_size = EnumTAppArgs.size genv.timap in
          let%bind ddt =
            SRTL.build_array_salloc clo_ty ddt_size (tempname "dyndisp_table")
              builder
          in
          let%bind () =
            forallM tbodies' ~f:(fun (t, tbody) ->
                let%bind tidx = EnumTAppArgs.lookup_typ_idx genv.timap t in
                let addr =
                  Llvm.build_gep ddt
                    [| Llvm.const_int (Llvm.i32_type llctx) tidx |]
                    (tempname "dyndisp_gep") builder
                in
                let addr' =
                  Llvm.build_pointercast addr
                    (Llvm.pointer_type @@ Llvm.type_of tbody)
                    (tempname "dyndisp_pcast") builder
                in
                let _ = Llvm.build_store tbody addr' builder in
                pure ())
          in
          let ddt' = Llvm.build_pointercast ddt t' "dyndisp_table" builder in
          pure ddt')
  | App (f, args) ->
      (* Resolve f (to a closure value) *)
      let%bind fclo_ll = resolve_id_value genv (Some builder) f in
      (* and extract the fundef and environment pointers. *)
      let%bind fptr =
        build_extractvalue fclo_ll 0
          (tempname (Identifier.as_string f ^ "_fptr"))
          builder
      in
      let%bind envptr =
        build_extractvalue fclo_ll 1
          (tempname (Identifier.as_string f ^ "_envptr"))
          builder
      in
      build_call_helper llmod genv builder discope f fptr args (Some envptr)
  | TFunSel (tf, targs) ->
      let tfs = Identifier.as_string tf in
      let specialize_polyfun pf t =
        match pf with
        | PolyFun (tv, t') -> pure @@ TU.subst_type_in_type tv t t'
        | _ ->
            fail0 "GenLlvm: genllvm_expr: expected universally quantified type."
      in
      let%bind tf' = resolve_id_value genv (Some builder) tf in
      let%bind tf_typ = id_typ tf in
      let%bind v, _ =
        foldM ~init:(tf', tf_typ) targs ~f:(fun (curtf, curtf_ty) targ ->
            let%bind tidx = EnumTAppArgs.lookup_typ_idx genv.timap targ in
            let addr =
              Llvm.build_gep curtf
                [| Llvm.const_int (Llvm.i32_type llctx) tidx |]
                (tempname tfs) builder
            in
            let%bind retty = specialize_polyfun curtf_ty targ in
            let fty = FunType ([], retty) in
            let%bind clo_ty = genllvm_typ_fst llmod fty in
            let addr' =
              Llvm.build_pointercast addr (Llvm.pointer_type clo_ty)
                (tempname tfs) builder
            in
            let curclo = Llvm.build_load addr' (tempname tfs) builder in
            (* and extract the fundef and environment pointers. *)
            let%bind fptr =
              build_extractvalue curclo 0
                (tempname (Identifier.as_string tf ^ "_fptr"))
                builder
            in
            let%bind envptr =
              build_extractvalue curclo 1
                (tempname (Identifier.as_string tf ^ "_envptr"))
                builder
            in
            let%bind curtf' =
              build_call_helper llmod genv builder discope tf fptr []
                (Some envptr)
            in
            pure (curtf', retty))
      in
      pure v
  | Builtin (b, _ts, args) ->
      let id_resolver = resolve_id_value genv in
      let td_resolver = TypeDescr.resolve_typdescr genv.tdmap in
      SRTL.build_builtin_call llmod discope id_resolver td_resolver builder b
        args
  | Message spl_l ->
      let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
      let%bind string_ll_ty = genllvm_typ_fst llmod (PrimType String_typ) in
      (* 1. String for the name of the field. *)
      let string_size = llsizeof dl string_ll_ty in
      (* 2. Type descriptor for the value. *)
      let ptr_size = llsizeof dl (void_ptr_type llctx) in
      let%bind size, size_type_l =
        fold_mapM spl_l ~init:0 ~f:(fun accum_size (_, pl) ->
            let%bind sty =
              match pl with
              | MLit l -> TypeUtilities.literal_type l
              | MVar v -> id_typ v
            in
            let%bind llty = genllvm_typ_fst llmod sty in
            (* 3. The value itself. *)
            let v_size = llsizeof dl llty in
            let entry_size = string_size + ptr_size + v_size in
            pure (accum_size + entry_size, (entry_size, sty)))
      in
      let%bind mem =
        (* 1 byte at the beginning is for the number of fields. *)
        SRTL.build_array_salloc (Llvm.i8_type llctx) (size + 1)
          (tempname "msgobj") builder
      in
      let n = Llvm.const_int (Llvm.i8_type llctx) (List.length spl_l) in
      (* Write out the number of fields we have. *)
      let (_ : Llvm.llvalue) = Llvm.build_store n mem builder in
      (* Write out each field as a triple (1, 2, 3) as commented above. *)
      let%bind (_ : int) =
        fold2M spl_l size_type_l ~init:1
          ~f:(fun off (s, pl) (size, ty) ->
            let%bind sl = genllvm_literal llmod builder (StringLit s) in
            (* 1. store the field name *)
            let gep_sl =
              Llvm.build_gep mem
                [| Llvm.const_int (Llvm.i32_type llctx) off |]
                (tempname "msgobj_fname") builder
            in
            let ptr_sl =
              Llvm.build_pointercast gep_sl
                (Llvm.pointer_type (Llvm.type_of sl))
                (tempname "msgobj_fname") builder
            in
            let (_ : Llvm.llvalue) = Llvm.build_store sl ptr_sl builder in
            let off' = off + llsizeof dl (Llvm.type_of sl) in
            (* 2. Store the type descriptor. *)
            let ty' = TypeUtilities.erase_address_in_type ty in
            let%bind td = TypeDescr.resolve_typdescr genv.tdmap ty' in
            let gep_td =
              Llvm.build_gep mem
                [| Llvm.const_int (Llvm.i32_type llctx) off' |]
                (tempname "msgobj_td") builder
            in
            let ptr_td =
              Llvm.build_pointercast gep_td
                (Llvm.pointer_type (Llvm.type_of td))
                (tempname "msgobj_td") builder
            in
            let (_ : Llvm.llvalue) = Llvm.build_store td ptr_td builder in
            let off'' = off' + llsizeof dl (Llvm.type_of td) in
            (* 3. Store the value itself. *)
            let%bind v =
              match pl with
              | MLit l -> genllvm_literal llmod builder l
              | MVar v -> resolve_id_value genv (Some builder) v
            in
            let gep_v =
              Llvm.build_gep mem
                [| Llvm.const_int (Llvm.i32_type llctx) off'' |]
                (tempname "msgobj_v") builder
            in
            let ptr_v =
              Llvm.build_pointercast gep_v
                (Llvm.pointer_type (Llvm.type_of v))
                (tempname "msgobj_v") builder
            in
            let (_ : Llvm.llvalue) = Llvm.build_store v ptr_v builder in
            pure (off + size))
          ~msg:(fun () ->
            ErrorUtils.mk_error1
              "GenLlvm: genllvm_expr: Message: list length mismatch" erep.ea_loc)
      in
      let%bind msgobj_ty = rep_typ erep in
      let%bind msgobj_ty_ll = genllvm_typ_fst llmod msgobj_ty in
      let mem' =
        Llvm.build_pointercast mem msgobj_ty_ll (tempname "msgobj") builder
      in
      pure mem'

(* Allocates memory for indices, puts them in there and returns a pointer. *)
let prepare_state_access_indices llmod genv builder indices =
  let llctx = Llvm.module_context llmod in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  if List.is_empty indices then
    pure @@ Llvm.const_pointer_null (Llvm.pointer_type (Llvm.i8_type llctx))
  else
    let%bind indices_types = mapM indices ~f:(id_typ_ll llmod) in
    let membuf_size =
      List.fold indices_types ~init:0 ~f:(fun s t -> s + llsizeof dl t)
    in
    let%bind membuf =
      SRTL.build_array_salloc (Llvm.i8_type llctx) membuf_size
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
let genllvm_fetch_state llmod genv builder discope loc dest addropt fname
    indices fetch_val =
  let llctx = Llvm.module_context llmod in
  let%bind indices_buf =
    prepare_state_access_indices llmod genv builder indices
  in
  let%bind f =
    if Option.is_some addropt then SRTL.decl_fetch_remote_field llmod
    else SRTL.decl_fetch_field llmod
  in
  let%bind mty = id_typ fname in
  let%bind tyd = TypeDescr.resolve_typdescr genv.tdmap mty in
  let fieldname =
    Llvm.const_pointercast
      (define_global
         (tempname (Identifier.as_string fname))
         (Llvm.const_stringz llctx (Identifier.as_string fname))
         llmod ~const:true ~unnamed:true)
      (Llvm.pointer_type (Llvm.i8_type llctx))
  in
  let num_indices =
    Llvm.const_int (Llvm.i32_type llctx) (List.length indices)
  in
  let fetchval_ll =
    Llvm.const_int (Llvm.i32_type llctx) (Bool.to_int fetch_val)
  in
  let%bind retty = id_typ dest in
  (* We have all the arguments built, build the call. *)
  let%bind retval =
    let args =
      Option.to_list (Option.map ~f:(fun v -> SRTL.CALLArg_ScillaVal v) addropt)
      @ List.map ~f:(fun v -> SRTL.CALLArg_LLVMVal v)
      @@ [ fieldname; tyd; num_indices; indices_buf; fetchval_ll ]
    in
    let id_resolver = resolve_id_value genv in
    SRTL.build_builtin_call_helper ~execptr_b:true
      (Some (discope, loc))
      llmod id_resolver builder
      (Identifier.as_string dest)
      f args retty
  in
  let%bind retloc = resolve_id_memloc genv dest in
  let _ = Llvm.build_store retval retloc builder in
  pure genv

(* Translate state updates. *)
let genllvm_update_state llmod genv builder discope loc fname indices valopt =
  let llctx = Llvm.module_context llmod in
  let%bind indices_buf =
    prepare_state_access_indices llmod genv builder indices
  in
  let%bind f = SRTL.decl_update_field llmod in
  let%bind mty = id_typ fname in
  let%bind tyd = TypeDescr.resolve_typdescr genv.tdmap mty in
  let%bind execptr = prepare_execptr llmod builder in
  let fieldname =
    Llvm.const_pointercast
      (define_global
         (tempname (Identifier.as_string fname))
         (Llvm.const_stringz llctx (Identifier.as_string fname))
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
        let%bind boxed_typ = is_boxed_typ vty in
        if boxed_typ then
          let%bind () =
            (* This is a pointer already, just pass that directly. *)
            if Base.Poly.(Llvm.classify_type vty_ll <> Llvm.TypeKind.Pointer)
            then
              fail0
                ("GenLlvm: genllvm_update_state: internal error. Expected \
                  pointer value, but got "
                ^ Llvm.string_of_lltype vty_ll
                ^ " for " ^ pp_typ vty)
            else pure ()
          in
          let castedvalue =
            Llvm.build_pointercast value_ll (void_ptr_type llctx)
              (tempname "update_value") builder
          in
          pure castedvalue
        else
          (* Build alloca for the value and pass the alloca. *)
          let%bind alloca =
            build_alloca vty_ll (tempname "update_value") builder
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
  let call_update =
    Llvm.build_call f
      [| execptr; fieldname; tyd; num_indices; indices_buf; value_ll |]
      "" builder
  in
  let%bind () = DebugInfo.set_inst_loc llctx discope call_update loc in
  pure genv

(* void* _read_blockchain (void* execptr, String VName) *)
let build_read_blockchain genv llmod discope builder dest loc vname =
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  let%bind decl, bnum_string_ty = SRTL.decl_read_blockchain llmod in
  let dummy_resolver _ _ =
    fail0 "GenLlvm: build_new_empty_map: Nothing to resolve."
  in
  let%bind retty = id_typ dest in
  let%bind arg =
    define_string_value llmod bnum_string_ty
      ~name:(tempname "read_blockchain")
      ~strval:vname
  in
  let%bind () =
    ensure
      (can_pass_by_val dl bnum_string_ty)
      "GenLlvm: build_new_bnum: Internal error: Cannot pass string by value"
  in
  let%bind retval =
    SRTL.build_builtin_call_helper ~execptr_b:true
      (Some (discope, loc))
      llmod dummy_resolver builder
      (Identifier.as_string dest)
      decl
      [ SRTL.CALLArg_LLVMVal arg ]
      retty
  in
  let%bind retloc = resolve_id_memloc genv dest in
  let _ = Llvm.build_store retval retloc builder in
  pure genv

(* Translate stmts into LLVM-IR by inserting instructions through irbuilder, *)
let rec genllvm_stmts genv builder dibuilder discope stmts =
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
    foldM stmts ~init:genv ~f:(fun accenv (stmt, ann) ->
        match stmt with
        | LocalDecl x ->
            (* Local variables are stored to and loaded from allocas.
             * Running the mem2reg pass will take care of this. *)
            let%bind xty_ll = id_typ_ll llmod x in
            let%bind xll =
              build_alloca xty_ll (Identifier.as_string x) builder
            in
            pure @@ { accenv with llvals = (x, Local xll) :: accenv.llvals }
        | LibVarDecl v ->
            let%bind vty_ll = id_typ_ll llmod v in
            let vll =
              (* Global variables need to be zero initialized.
               * Only declaring would lead to an `extern` linkage. *)
              let init = Llvm.const_null vty_ll in
              define_global (Identifier.as_string v) init llmod ~const:false
                ~unnamed:false
            in
            pure { accenv with llvals = (v, Global vll) :: accenv.llvals }
        | Bind (x, e) ->
            (* Find the allocation for x and store to it. *)
            let%bind xll = resolve_id_memloc accenv x in
            let%bind e_val = genllvm_expr accenv builder discope e in
            let store = Llvm.build_store e_val xll builder in
            let%bind () =
              DebugInfo.set_inst_loc llctx discope store ann.ea_loc
            in
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
                SRTL.build_salloc env_ty
                  (tempname (Identifier.as_string fname ^ "_envp"))
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
                      llvals = (fname, CloP (cloval, envp)) :: accenv.llvals;
                    }
              | _ ->
                  errm1
                    (sprintf "%s did not resolve to global declaration."
                       (Identifier.as_string fname))
                    (Identifier.get_rep fname).ea_loc)
        | StoreEnv (envvar, v, (fname, envvars)) -> (
            let%bind resolved_fname = resolve_id accenv fname in
            match resolved_fname with
            | CloP (_cloval, envp) ->
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
                           (Identifier.as_string envvar)
                           (Identifier.as_string fname))
                        (Identifier.get_rep fname).ea_loc
                in
                (* Store v into envp[i] *)
                let envp_i =
                  Llvm.build_struct_gep envp i
                    (tempname
                       (Identifier.as_string fname ^ "_env_"
                       ^ Identifier.as_string envvar))
                    builder
                in
                let%bind vresolved = resolve_id_value accenv (Some builder) v in
                let _ = Llvm.build_store vresolved envp_i builder in
                (* This operation doesn't affect our codegen environment. *)
                pure accenv
            | _ ->
                errm1
                  (sprintf "expected %s to resolve to closure."
                     (Identifier.as_string fname))
                  (Identifier.get_rep fname).ea_loc)
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
                           (Identifier.as_string envvar)
                           (Identifier.as_string fname))
                        (Identifier.get_rep fname).ea_loc
                in
                (* Load from envp[i] into v *)
                let envp_i =
                  Llvm.build_struct_gep envp i
                    (tempname
                       (Identifier.as_string fname ^ "_env_"
                       ^ Identifier.as_string envvar))
                    builder
                in
                let loadi =
                  Llvm.build_load envp_i
                    (tempname (Identifier.as_string v ^ "_envload"))
                    builder
                in
                (* Put the loaded value into a local variable, so that we can bind it as a Local. *)
                let%bind loadi_alloca =
                  build_alloca (Llvm.type_of loadi) (Identifier.as_string v)
                    builder
                in
                let _ = Llvm.build_store loadi loadi_alloca builder in
                pure
                  {
                    accenv with
                    llvals = (v, Local loadi_alloca) :: accenv.llvals;
                  }
            | None ->
                errm1
                  (sprintf "expected envparg when compiling fundef %s."
                     (Identifier.as_string fname))
                  (Identifier.get_rep fname).ea_loc)
        | MatchStmt (o, clauses, jopt) ->
            let%bind discope' =
              DebugInfo.create_sub_scope dibuilder discope ann.ea_loc
            in
            let match_block = Llvm.insertion_block builder in
            (* Let's first generate the successor block for this entire match block. *)
            let succblock =
              new_block_after llctx (tempname "matchsucc") match_block
            in
            let genv_succblock = { accenv with succblock = Some succblock } in
            (* Given a variable (with loc) and statements:
               1. If loc is not empty, use that to build a subscope
               2. If not, use the first statement's location,
               3. If not, return back argument scope. *)
            let best_effort_disubscope scope loc stmts =
              if Base.Poly.(loc <> ErrorUtils.dummy_loc) then
                DebugInfo.create_sub_scope dibuilder scope loc
              else
                match stmts with
                | (_, first_annot) :: _ ->
                    DebugInfo.create_sub_scope dibuilder scope
                      first_annot.ea_loc
                | _ -> pure discope'
            in
            (* Let's next generate jopt as there may be jumps to it from clauses. *)
            let%bind genv_joinblock, insert_before_block =
              match jopt with
              | Some (jname, jsts) ->
                  let jblock =
                    new_block_after llctx
                      (Identifier.as_string jname)
                      match_block
                  in
                  let builder' = Llvm.builder_at_end llctx jblock in
                  let%bind discope'' =
                    best_effort_disubscope discope'
                      (Identifier.get_rep jname).ea_loc jsts
                  in
                  let%bind () =
                    genllvm_block genv_succblock builder' dibuilder discope''
                      jsts
                  in
                  (* Bind this block. *)
                  pure
                    ( {
                        genv_succblock with
                        joins =
                          (Identifier.as_string jname, jblock)
                          :: genv_succblock.joins;
                      },
                      jblock )
              | None -> pure (genv_succblock, succblock)
            in
            let%bind ollval = resolve_id_value accenv (Some builder) o in
            (* Load the tag from ollval. *)
            let tagval_gep =
              Llvm.build_struct_gep ollval 0
                (tempname (Identifier.as_string o ^ "_tag"))
                builder
            in
            let tagval =
              Llvm.build_load tagval_gep
                (tempname (Identifier.as_string o ^ "_tag"))
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
                               (Identifier.as_string o))
                            (Identifier.get_rep o).ea_loc
                    | Constructor _ ->
                        (* Accummulate this and process further. *)
                        go rest_clauses
                          (clause :: cons_clauses, default_clause_opt))
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
                         (Identifier.as_string o))
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
                  let%bind genv' =
                    match c with
                    | Wildcard -> pure genv_joinblock
                    | Binder v ->
                        (* Bind v as a local variable. *)
                        let%bind valloca =
                          build_alloca (Llvm.type_of ollval)
                            (Identifier.as_string v) builder'
                        in
                        let _ = Llvm.build_store ollval valloca builder' in
                        pure
                          {
                            genv_joinblock with
                            llvals = (v, Local valloca) :: genv_joinblock.llvals;
                          }
                  in
                  let%bind discope'' =
                    best_effort_disubscope discope'
                      (match c with
                      | Wildcard -> ErrorUtils.dummy_loc
                      | Binder b -> (Identifier.get_rep b).ea_loc)
                      clause_stmts
                  in
                  let%bind () =
                    genllvm_block genv' builder' dibuilder discope''
                      clause_stmts
                  in
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
                      let%bind llcty, tag =
                        get_ctr_struct llctys (Identifier.get_id cname)
                      in
                      let clause_block =
                        new_block_before llctx
                          (tempname (Identifier.as_string cname))
                          default_block
                      in
                      let builder' = Llvm.builder_at_end llctx clause_block in
                      let cobjp =
                        Llvm.build_bitcast ollval (Llvm.pointer_type llcty)
                          (tempname (Identifier.as_string o))
                          builder'
                      in
                      let celm_tys = Llvm.struct_element_types llcty in
                      (* The LLVM struct type will have one additional field for the tag. *)
                      if Array.length celm_tys <> List.length cargs + 1 then
                        errm1
                          (sprintf
                             "matching %s: Constructor %s argument mismatch."
                             (Identifier.as_error_string o)
                             (Identifier.as_error_string cname))
                          (Identifier.get_rep o).ea_loc
                      else
                        (* Generate binding for each binder in cargs. *)
                        let%bind _, binds_rev =
                          foldM cargs ~init:(0, []) ~f:(fun (i, acc) c ->
                              match c with
                              | Wildcard -> pure (i + 1, acc)
                              | Binder v ->
                                  (* Bind v as a local variable. *)
                                  let vgep =
                                    (* Count from 1 since the 0th struct member is the tag. *)
                                    Llvm.build_struct_gep cobjp (i + 1)
                                      (tempname
                                         (Identifier.as_string v ^ "_gep"))
                                      builder'
                                  in
                                  let vloaded =
                                    Llvm.build_load vgep
                                      (tempname
                                         (Identifier.as_string v ^ "_load"))
                                      builder'
                                  in
                                  let%bind valloca =
                                    build_alloca (Llvm.type_of vloaded)
                                      (Identifier.as_string v) builder'
                                  in
                                  let _ =
                                    Llvm.build_store vloaded valloca builder'
                                  in
                                  pure (i + 1, (v, Local valloca) :: acc))
                        in
                        let genv' =
                          {
                            genv_joinblock with
                            llvals = List.rev binds_rev @ genv_joinblock.llvals;
                          }
                        in
                        let%bind discope'' =
                          best_effort_disubscope discope'
                            (Identifier.get_rep cname).ea_loc body
                        in
                        let%bind () =
                          genllvm_block genv' builder' dibuilder discope'' body
                        in
                        pure
                          (Llvm.const_int (Llvm.i8_type llctx) tag, clause_block)
                  | _ ->
                      errm1
                        (sprintf "matching %s: expected Constructor pattern."
                           (Identifier.as_string o))
                        (Identifier.get_rep o).ea_loc)
            in
            (* Create the switch statement and add all clauses to it. *)
            let sw =
              Llvm.build_switch tagval default_block
                (List.length tag_block_list)
                builder
            in
            let%bind () = DebugInfo.set_inst_loc llctx discope sw ann.ea_loc in
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
              (* prepend append _amount, _origin and _sender to args *)
              let amount_typ = PrimType (Uint_typ Bits128) in
              let address_typ = Address None in
              let lc = (Identifier.get_rep procname).ea_loc in
              Identifier.mk_id
                (Identifier.Name.parse_simple_name
                   ContractUtil.MessagePayload.amount_label)
                { ea_tp = Some amount_typ; ea_loc = lc; ea_auxi = None }
              ::
              Identifier.mk_id
                (Identifier.Name.parse_simple_name
                   ContractUtil.MessagePayload.origin_label)
                { ea_tp = Some address_typ; ea_loc = lc; ea_auxi = None }
              ::
              Identifier.mk_id
                (Identifier.Name.parse_simple_name
                   ContractUtil.MessagePayload.sender_label)
                { ea_tp = Some address_typ; ea_loc = lc; ea_auxi = None }
              :: args
            in
            match procreslv with
            | FunDecl fptr ->
                let%bind _ =
                  build_call_helper llmod accenv builder discope procname fptr
                    all_args None
                in
                pure accenv
            | _ ->
                fail1
                  (sprintf
                     "GenLlvm: genllvm_stmts: internal error: Procedure call \
                      %s didn't resolve to defined function."
                     (Identifier.as_string procname))
                  (Identifier.get_rep procname).ea_loc)
        | MapGet (x, m, indices, fetch_val) ->
            genllvm_fetch_state llmod accenv builder discope ann.ea_loc x None m
              indices fetch_val
        | RemoteMapGet (x, addr, m, indices, fetch_val) ->
            genllvm_fetch_state llmod accenv builder discope ann.ea_loc x
              (Some addr) m indices fetch_val
        | Load (x, f) ->
            genllvm_fetch_state llmod accenv builder discope ann.ea_loc x None f
              [] true
        | RemoteLoad (x, addr, f) ->
            genllvm_fetch_state llmod accenv builder discope ann.ea_loc x
              (Some addr) f [] true
        | MapUpdate (m, indices, valopt) ->
            genllvm_update_state llmod accenv builder discope ann.ea_loc m
              indices valopt
        | Store (f, x) ->
            genllvm_update_state llmod accenv builder discope ann.ea_loc f []
              (Some x)
        | SendMsgs m ->
            let%bind f = SRTL.decl_send llmod in
            let%bind execptr = prepare_execptr llmod builder in
            let%bind td =
              TypeDescr.resolve_typdescr accenv.tdmap
                (ADT
                   ( Identifier.mk_loc_id
                       (Identifier.Name.parse_simple_name "List"),
                     [ PrimType Msg_typ ] ))
            in
            let%bind m' = resolve_id_value accenv (Some builder) m in
            let (send_call : Llvm.llvalue) =
              Llvm.build_call f [| execptr; td; m' |] "" builder
            in
            let%bind () =
              DebugInfo.set_inst_loc llctx discope send_call ann.ea_loc
            in
            pure accenv
        | CreateEvnt e ->
            let%bind f = SRTL.decl_event llmod in
            let%bind execptr = prepare_execptr llmod builder in
            let%bind td =
              TypeDescr.resolve_typdescr accenv.tdmap (PrimType Event_typ)
            in
            let%bind e' = resolve_id_value accenv (Some builder) e in
            let (event_call : Llvm.llvalue) =
              Llvm.build_call f [| execptr; td; e' |] "" builder
            in
            let%bind () =
              DebugInfo.set_inst_loc llctx discope event_call ann.ea_loc
            in
            pure accenv
        | Throw eopt ->
            let%bind f = SRTL.decl_throw llmod in
            let%bind execptr = prepare_execptr llmod builder in
            let%bind td =
              TypeDescr.resolve_typdescr accenv.tdmap (PrimType Exception_typ)
            in
            let%bind e' =
              match eopt with
              | Some e -> resolve_id_value accenv (Some builder) e
              | None -> pure (void_ptr_nullptr llctx)
            in
            let (throw_call : Llvm.llvalue) =
              Llvm.build_call f [| execptr; td; e' |] "" builder
            in
            let%bind () =
              DebugInfo.set_inst_loc llctx discope throw_call ann.ea_loc
            in
            pure accenv
        | AcceptPayment ->
            let%bind f = SRTL.decl_accept llmod in
            let%bind execptr = prepare_execptr llmod builder in
            let (accept_call : Llvm.llvalue) =
              Llvm.build_call f [| execptr |] "" builder
            in
            let%bind () =
              DebugInfo.set_inst_loc llctx discope accept_call ann.ea_loc
            in
            pure accenv
        | GasStmt g ->
            let id_resolver = resolve_id_value accenv in
            let td_resolver = TypeDescr.resolve_typdescr accenv.tdmap in
            let try_resolver id =
              Option.map
                (List.find accenv.llvals ~f:(fun (lid, _) ->
                     Identifier.Name.equal (Identifier.get_id lid) id))
                ~f:fst
            in
            let%bind g_ll =
              GasChargeGen.gen_gas_charge llmod builder td_resolver id_resolver
                try_resolver g
            in
            let%bind gasrem_p = lookup_global "_gasrem" llmod in
            let gasrem = Llvm.build_load gasrem_p (tempname "gasrem") builder in
            (* if (g_ll > gasrem) {
             *   _out_of_gas();
             * }
             * gasrem -= g_ll;
             * ...
             *)
            let cmp =
              Llvm.build_icmp Llvm.Icmp.Ugt g_ll gasrem (tempname "gascmp")
                builder
            in
            let oog_block =
              new_block_after llctx (tempname "out_of_gas")
                (Llvm.insertion_block builder)
            in
            let succ_block =
              new_block_after llctx (tempname "have_gas") oog_block
            in
            let _ = Llvm.build_cond_br cmp oog_block succ_block builder in
            (* Let's build inside oog_block. *)
            let () = Llvm.position_at_end oog_block builder in
            let%bind oog = SRTL.decl_out_of_gas llmod in
            let _ = Llvm.build_call oog [||] "" builder in
            let _ = Llvm.build_br succ_block builder in
            (* We'll now resume back in the successor block, and consume gas. *)
            let () = Llvm.position_at_end succ_block builder in
            let gasrem' =
              Llvm.build_sub gasrem g_ll (tempname "consume") builder
            in
            let _ = Llvm.build_store gasrem' gasrem_p builder in
            pure accenv
        | ReadFromBC (x, bsv) ->
            build_read_blockchain accenv llmod discope builder x ann.ea_loc bsv
        | _ -> fail0 "GenLlvm: genllvm_stmts: Statement not supported yet")
  in
  pure ()

(* Generate LLVM-IR for a block of statements.
 * Inserts a terminator instruction when needed.
 * If the sequence of statements have no natural successor
 * (branch/return) and nosucc_retvoid is set, then a "return void"
 * is automatically appended. Otherwise, having no successor is an error. *)
and genllvm_block ?(nosucc_retvoid = false) genv builder dibuilder discope stmts
    =
  let%bind _ = genllvm_stmts genv builder dibuilder discope stmts in
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
               fname))

let genllvm_closures dibuilder llmod tydescrs tidxs topfuns =
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
          tempname (Identifier.as_string !(cr.thisfun).fname ^ "_env")
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
              (Identifier.as_string !(cr.thisfun).fname)
              ret_ty_ll
              (penv_ty_ll :: args_ty_ll')
          else
            (* returns void (return value is via the stack),
             * env pointer type, type of pointer to return type, argument types *)
            let fargs_ty =
              penv_ty_ll :: Llvm.pointer_type ret_ty_ll :: args_ty_ll'
            in
            scilla_function_decl ~is_internal:true llmod
              (Identifier.as_string !(cr.thisfun).fname)
              (Llvm.void_type ctx) fargs_ty
        in
        pure @@ (!(cr.thisfun).fname, decl) :: accenv)
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
      timap = tidxs;
    }
  in

  (* Let us now define each of these functions. *)
  let fdecl_cr_l = List.zip_exn fdecls topfuns in
  let%bind _ =
    forallM fdecl_cr_l ~f:(fun ((fname, f), cr) ->
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
                 (Identifier.as_string fname))
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
                     (Identifier.as_string varg)
                     (Identifier.as_string fid))
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
                    (Llvm.build_load arg_llval
                       (Identifier.as_string varg)
                       builder)
                else arg_mismatch_err
              in
              pure
                ( {
                    accum_genv with
                    llvals = (varg, FunArg arg_llval') :: accum_genv.llvals;
                  },
                  idx - 1 ))
        in
        let md_subprogram = DebugInfo.gen_fun dibuilder !(cr.thisfun).fname f in
        (* We now have the environment to generate the function body. *)
        genllvm_block genv_args builder dibuilder md_subprogram
          !(cr.thisfun).fbody)
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
  let () = Llvm.set_target_triple triple llmod in
  let () = Llvm.set_data_layout lldly llmod in
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
let create_init_libs dibuilder genv llmod lstmts =
  let ctx = Llvm.module_context llmod in
  let fname = "_init_libs" in
  let%bind f =
    scilla_function_defn ~is_internal:false llmod "_init_libs"
      (Llvm.void_type ctx) []
  in
  let irbuilder = Llvm.builder_at_end ctx (Llvm.entry_block f) in
  (* TODO: Get actual location from the first statement. *)
  let di_fun = DebugInfo.gen_fun_loc dibuilder fname ErrorUtils.dummy_loc f in
  let%bind () =
    genllvm_block ~nosucc_retvoid:true genv irbuilder dibuilder di_fun lstmts
  in
  (* genllvm_block creates bindings for LibVarDecls that we don't get back.
   * Let's just recreate them here. *)
  let%bind genv_libs =
    foldM lstmts ~init:genv ~f:(fun accenv (lstmt, _) ->
        match lstmt with
        | LibVarDecl v ->
            let%bind g = lookup_global (Identifier.as_string v) llmod in
            pure { accenv with llvals = (v, Global g) :: accenv.llvals }
        | _ -> pure accenv)
  in
  pure genv_libs

(* Create _init_state() that initializes database state of contract fields
 * with their initial values as defined in the contract source. *)
let create_init_state dibuilder genv llmod fields =
  let si_stmts =
    List.concat @@ List.map fields ~f:(fun (_, _, fstmts) -> fstmts)
  in
  let fname = "_init_state" in
  let ctx = Llvm.module_context llmod in
  let%bind f =
    scilla_function_defn ~is_internal:false llmod fname (Llvm.void_type ctx) []
  in
  let irbuilder = Llvm.builder_at_end ctx (Llvm.entry_block f) in
  (* TODO: Get actual location from the first statement. *)
  let di_fun = DebugInfo.gen_fun_loc dibuilder fname ErrorUtils.dummy_loc f in
  genllvm_block ~nosucc_retvoid:true genv irbuilder dibuilder di_fun si_stmts

(* Generate LLVM function for a procedure or transition. *)
let genllvm_component dibuilder genv llmod comp =
  let ctx = Llvm.module_context llmod in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  (* Convert params to LLVM (name,type) list. *)
  let%bind (_, ptys, _), params' =
    let%bind params' =
      mapM comp.comp_params ~f:(fun (pname, ty) ->
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
      (tempname (Identifier.as_string comp.comp_name))
      (Llvm.void_type ctx) ptys
  in
  let di_fun = DebugInfo.gen_fun dibuilder comp.comp_name f in
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
            let () = Llvm.set_value_name (Identifier.as_string pname) arg in
            pure { accenv with llvals = (pname, FunArg arg) :: accenv.llvals }
          else if
            (* This is a pass by stack pointer, so load the value. *)
            Base.Poly.(Llvm.classify_type pty <> Llvm.TypeKind.Pointer)
          then
            fail0
              "GenLlvm: genllvm_component: internal error: type of non \
               pass-by-val arg is not pointer."
          else
            let () =
              Llvm.set_value_name (tempname (Identifier.as_string pname)) arg
            in
            let loaded_arg =
              Llvm.build_load arg (Identifier.as_string pname) builder
            in
            pure
              {
                accenv with
                llvals = (pname, FunArg loaded_arg) :: accenv.llvals;
              })
    in
    (* Generate the body. *)
    let%bind () =
      genllvm_block ~nosucc_retvoid:true genv_args builder dibuilder di_fun
        comp.comp_body
    in
    (* Bind the component name for later use. *)
    let genv_comp =
      { genv with llvals = (comp.comp_name, FunDecl f) :: genv.llvals }
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
            (Identifier.as_string comp.comp_name)
            (Llvm.void_type ctx) [ void_ptr_type ctx ]
        in
        let di_fun = DebugInfo.gen_fun dibuilder comp.comp_name wf in
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
                  (tempname (Identifier.as_string pname))
                  builder
              in
              let%bind arg, inc =
                if pass_by_val then
                  let pty_ptr =
                    (* Pointer to our current argument. *)
                    Llvm.build_pointercast gep (Llvm.pointer_type pty)
                      (tempname (Identifier.as_string pname))
                      builder
                  in
                  (* Load the value from buffer and pass that. *)
                  pure
                    ( Llvm.build_load pty_ptr
                        (Identifier.as_string pname)
                        builder,
                      llsizeof dl pty )
                else
                  let arg =
                    Llvm.build_pointercast gep pty
                      (tempname (Identifier.as_string pname))
                      builder
                  in
                  let%bind pty_elty = ptr_element_type pty in
                  pure (arg, llsizeof dl pty_elty)
              in
              pure (offset + inc, arg :: arglist))
        in
        (* Insert a call to our internal function implementing the transition. *)
        let trans_call =
          Llvm.build_call f (Array.of_list (List.rev args_rev)) "" builder
        in
        let%bind () =
          DebugInfo.set_inst_loc ctx di_fun trans_call
            (Identifier.get_rep comp.comp_name).ea_loc
        in
        let _ = Llvm.build_ret_void builder in
        pure genv_comp

(* Declare and zero initialize SRTL common globals *)
let gen_common_globals llmod =
  let llctx = Llvm.module_context llmod in
  let _ =
    define_global "_execptr" (void_ptr_nullptr llctx) llmod ~const:false
      ~unnamed:false
  in
  let _ =
    define_global "_gasrem"
      (Llvm.const_null (Llvm.i64_type llctx))
      llmod ~const:false ~unnamed:false
  in
  ()

(* Declare and zero initialize contract parameters; bind them as globals.
 * Their actual value will be filled in before execution. *)
let declare_bind_cparams genv llmod cparams =
  foldM cparams ~init:genv ~f:(fun accenv (pname, pty) ->
      let%bind llpty = genllvm_typ_fst llmod pty in
      let init = Llvm.const_null llpty in
      let g =
        define_global
          (Identifier.as_string pname)
          init llmod ~const:false ~unnamed:false
      in
      pure @@ { accenv with llvals = (pname, Global g) :: accenv.llvals })

(* Generate an LLVM module for a Scilla module. *)
let genllvm_module filename (cmod : cmodule) =
  let llcontext = Llvm.create_context () in
  let llmod =
    Llvm.create_module llcontext (Identifier.as_string cmod.contr.cname)
  in

  let dibuilder = DebugInfo.create_dibuilder llmod in
  let () = DebugInfo.gen_common dibuilder llmod filename in

  let () = prepare_target llmod in
  let () = gen_common_globals llmod in

  (* Gather all the top level functions. *)
  let topclos = gather_closures_cmod cmod in
  let%bind tydescr_map =
    TypeDescr.generate_type_descr_cmod llmod topclos cmod
  in
  let tidx_map = EnumTAppArgs.enumerate_tapp_args_cmod topclos cmod in
  (* Generate LLVM functions for all closures. *)
  let%bind genv_fdecls =
    genllvm_closures dibuilder llmod tydescr_map tidx_map topclos
  in
  (* Create a function to initialize library values. *)
  let%bind genv_libs =
    create_init_libs dibuilder genv_fdecls llmod cmod.lib_stmts
  in
  (* Declare, zero initialize contract parameters as globals. *)
  let%bind genv_cparams =
    declare_bind_cparams genv_libs llmod cmod.contr.cparams
  in
  let%bind () =
    create_init_state dibuilder genv_cparams llmod cmod.contr.cfields
  in
  (* Generate LLVM functions for procedures and transitions. *)
  let%bind _genv_comps =
    foldM cmod.contr.ccomps ~init:genv_cparams ~f:(fun accenv comp ->
        genllvm_component dibuilder accenv llmod comp)
  in
  (* Build a table containing all type descriptors.
   * This is needed for SRTL to parse types from JSONs *)
  let%bind _ =
    TypeDescr.build_tydescr_table llmod ~global_array_name:"_tydescr_table"
      ~global_array_length_name:"_tydescr_table_length" tydescr_map
  in
  let%bind () = SRTL.gen_param_descrs (Some cmod) llmod tydescr_map in

  (* Finalize the debug-info builder. *)
  let () = DebugInfo.finalize_dibuilder dibuilder in

  (* printf "Before verify module: \n%s\n" (Llvm.string_of_llmodule llmod); *)
  match Llvm_analysis.verify_module llmod with
  | None ->
      DebugMessage.pvlog (fun () ->
          sprintf "Before optimizations: \n%s\n" (Llvm.string_of_llmodule llmod));
      (* optimize_module llmod; *)
      pure llmod
  | Some err -> fail0 ("GenLlvm: genllvm_module: internal error: " ^ err)

(* Generate an LLVM module for a statement sequence. *)
let genllvm_stmt_list_wrapper filename stmts =
  let llcontext = Llvm.create_context () in
  let llmod = Llvm.create_module llcontext "scilla_expr" in
  let dibuilder = DebugInfo.create_dibuilder llmod in
  let () = DebugInfo.gen_common dibuilder llmod filename in

  let () = prepare_target llmod in
  let () = gen_common_globals llmod in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in

  (* Gather all the top level functions. *)
  let topclos = gather_closures stmts in
  let%bind tydescr_map =
    TypeDescr.generate_type_descr_stmts_wrapper llmod topclos stmts
  in
  let tidx_map = EnumTAppArgs.enumerate_tapp_args_stmts_wrapper topclos stmts in
  let%bind genv_fdecls =
    genllvm_closures dibuilder llmod tydescr_map tidx_map topclos
  in
  (* Create a function to initialize library values. *)
  let%bind genv_libs = create_init_libs dibuilder genv_fdecls llmod [] in

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
  let fname = "_scilla_expr_fun" in
  let%bind f =
    scilla_function_defn ~is_internal:true llmod fname (Llvm.return_type fty)
      (Array.to_list (Llvm.param_types fty))
  in
  let fannot =
    match stmts with (_, first_ea) :: _ -> first_ea | [] -> empty_annot
  in
  let f_di =
    DebugInfo.gen_fun dibuilder ~is_local_to_unit:false
      (mk_annot_id fname fannot) f
  in
  let%bind init_env =
    if Base.Poly.(Llvm.void_type llcontext = Llvm.return_type fty) then
      (* If return type is void, then second parameter is the pointer to return value. *)
      let%bind retp = array_get (Llvm.params f) 1 in
      pure { genv_libs with retp = Some retp }
    else pure { genv_libs with retp = None }
  in
  let irbuilder = Llvm.builder_at_end llcontext (Llvm.entry_block f) in
  let%bind _ = genllvm_block init_env irbuilder dibuilder f_di stmts in

  (* Generate a wrapper function scilla_main that'll call print on the result value. *)
  let%bind printer = SRTL.decl_print_scilla_val llmod in
  let%bind mainb =
    let%bind fdef =
      scilla_function_defn ~is_internal:false llmod "scilla_main"
        (Llvm.void_type llcontext) []
    in
    pure @@ Llvm.entry_block fdef
  in
  let builder_mainb = Llvm.builder_at_end llcontext mainb in
  let id_resolver = resolve_id_value init_env in
  let%bind _ =
    if TypeUtilities.is_legal_field_type retty then
      let%bind tydescr_ll = TypeDescr.resolve_typdescr tydescr_map retty in
      match init_env.retp with
      | Some retp ->
          (* Returns value on the stack through a pointer. *)
          let%bind _ =
            match retty with
            | PrimType _ -> pure ()
            | _ ->
                fail0 "GenLlvm: Stack (indirect) return of non PrimType value"
          in
          (* Allocate memory for return value. *)
          let%bind retty = ptr_element_type (Llvm.type_of retp) in
          let%bind memv =
            build_alloca retty (tempname "mainval") builder_mainb
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
          let%bind _ =
            SRTL.build_builtin_call_helper ~execptr_b:true None llmod
              id_resolver builder_mainb "print_res" printer
              [ CALLArg_LLVMVal tydescr_ll; CALLArg_LLVMVal memv_voidp ]
              Unit
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
          (* Non boxed types need to be boxed now. *)
          let%bind boxed_typ = is_boxed_typ retty in
          if not boxed_typ then
            let%bind memv =
              build_alloca retty_ll (tempname "pval") builder_mainb
            in
            let memv_voidp =
              Llvm.build_pointercast memv (void_ptr_type llcontext)
                (tempname "memvoidcast") builder_mainb
            in
            let _ = Llvm.build_store calli memv builder_mainb in
            let%bind _ =
              SRTL.build_builtin_call_helper ~execptr_b:true None llmod
                id_resolver builder_mainb "print_res" printer
                [ CALLArg_LLVMVal tydescr_ll; CALLArg_LLVMVal memv_voidp ]
                Unit
            in
            pure ()
          else
            let memv_voidp =
              Llvm.build_pointercast calli (void_ptr_type llcontext)
                (tempname "memvoidcast") builder_mainb
            in
            let%bind _ =
              SRTL.build_builtin_call_helper ~execptr_b:true None llmod
                id_resolver builder_mainb "print_res" printer
                [ CALLArg_LLVMVal tydescr_ll; CALLArg_LLVMVal memv_voidp ]
                Unit
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

  (* Build a table containing all type descriptors.
   * This is needed for SRTL to parse types from JSONs *)
  let%bind _ =
    TypeDescr.build_tydescr_table llmod ~global_array_name:"_tydescr_table"
      ~global_array_length_name:"_tydescr_table_length" tydescr_map
  in
  let%bind () = SRTL.gen_param_descrs None llmod tydescr_map in

  (* Finalize the debug-info builder. *)
  let () = DebugInfo.finalize_dibuilder dibuilder in

  (* printf "Before verify module: \n%s\n" (Llvm.string_of_llmodule llmod); *)
  match Llvm_analysis.verify_module llmod with
  | None ->
      DebugMessage.pvlog (fun () ->
          sprintf "Before optimizations: \n%s\n" (Llvm.string_of_llmodule llmod));
      (* optimize_module llmod; *)
      pure llmod
  | Some err ->
      fail0 ("GenLlvm: genllvm_stmt_list_wrapper: internal error: " ^ err)
