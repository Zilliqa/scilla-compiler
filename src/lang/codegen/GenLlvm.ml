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
 *    at runtime (as a string), so that SRTL can parse the type, and based on that,
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
open ClosuredSyntax
open CodegenUtils
open Printf
open UncurriedSyntax.Uncurried_Syntax
open Datatypes

let array_get arr idx =
  try
    pure @@ Array.get arr idx
  with
  | Invalid_argument _ -> fail0 "GenLlvm: array_get: Invalid array index"

(* Create a named struct with types from tyarr. *)
let named_struct_type ?(is_packed=false) llmod name tyarr =
  let ctx = Llvm.module_context llmod in
  match Llvm.type_by_name llmod name with
  | Some ty ->
    (* If ty is an opaque type, we fill its body now. *)
    if Llvm.classify_type ty <> Llvm.TypeKind.Struct
    then fail0
      (sprintf "GenLlvm: named_struct_type: internal error. Type %s already exists but is not struct." name)
    else (
      if Llvm.is_opaque ty then Llvm.struct_set_body ty tyarr is_packed;
      pure ty
    )
  | None ->
    let t = Llvm.named_struct_type ctx name in
    let _ = Llvm.struct_set_body t tyarr is_packed in
    pure t

let void_ptr_type ctx = Llvm.pointer_type (Llvm.void_type ctx)

let newname base =
  get_id (global_newnamer base ExplicitAnnotationSyntax.empty_annot)

(*
 * To avoid ABI complexities, we allow passing by value only
 * when the object size is not larger than two eight-bytes.
 * Otherwise, it needs to be passed in memory (via a pointer).
 * See https://stackoverflow.com/a/42413484/2128804
 *)
let can_pass_by_val dl ty =
  not
    (Llvm.type_is_sized ty &&
      (Int64.compare (Llvm_target.DataLayout.size_in_bits ty dl) (Int64.of_int 128)) > 0
    )

(* Create a function declaration of the given type signature,
 * Fails if the return type or arg types cannot be passed by value. *)
let scilla_function_decl llmod fname retty argtys =
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  let%bind _ = iterM (retty :: argtys) ~f:(fun ty ->
    if not (can_pass_by_val dl ty)
    then fail0 "Attempting to pass by value greater than 128 bytes"
    else pure ()
  ) in
  let ft = Llvm.function_type retty (Array.of_list argtys) in
  pure @@ Llvm.declare_function fname ft llmod

(* Translate Scilla types to LLVM types.
 * In case of ADTs, the LLVM types for each constructor is returned
 * as the second component of the result. In all other cases, the
 * second component of the result is an empty list. *)
let genllvm_typ llmod sty =

  let ctx = Llvm.module_context llmod in
  let i8_type = Llvm.i8_type ctx in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in

  (* Create a StructType "type { i8*, i32 }".
   * This type can represent Scilla String and ByStr values.
   * Note: We cannot use LLVM's Array type to represent bytes because
   *       that requires the length to be known at compile time. *)
  let scilla_bytes_ty ty_name =
    let ctx = Llvm.module_context llmod in
    let charp_ty = Llvm.pointer_type i8_type in
    let len_ty = Llvm.i32_type ctx in
    named_struct_type llmod ty_name [|charp_ty;len_ty|]
  in

  (* Given an ADT name or one of it's constructors' and the instantiation types,
   * concatenate them to create a name for the instantiated type. *)
  let type_instantiated_adt_name name ts =
    let%bind ts' = mapM ts ~f:(fun t ->
      if TypeUtilities.is_ground_type t
      then pure (pp_typ t)
      else fail0 "GenLlvm: unexpected polymorphic ADT"
    ) in
    pure @@ name ^ "_" ^ (String.concat ~sep:"_" ts')
  in

  let rec go ~inprocess sty =
    match sty with
    | PrimType pty ->
      let%bind llty = (match pty with
        (* Build integer types, by wrapping LLMV's i* type in structs with names. *)
        | Int_typ bw | Uint_typ bw ->
          let bwi = match bw with | Bits32 -> 32 | Bits64 -> 64 | Bits128 -> 128 | Bits256 -> 256 in
          named_struct_type llmod (pp_prim_typ pty) [|Llvm.integer_type ctx bwi|]
        (* An instantiation of scilla_bytes_ty for Scilla String. *)
        | String_typ -> scilla_bytes_ty "String"
        (* An instantiation of scilla_bytes_ty for Scilla Bystr. *)
        | Bystr_typ -> scilla_bytes_ty "Bystr"
        (* ByStrX represented as an LLVM array of length X. *)
        | Bystrx_typ bytes -> pure @@ Llvm.array_type i8_type bytes
        | Msg_typ | Event_typ | Exception_typ | Bnum_typ -> fail0 "GenLlvm: genllvm_prim_typ: unimplemented"
        ) in
      pure (llty, [])
    | ADT (tname, ts) ->
      let%bind name_ll = type_instantiated_adt_name tname ts in
      (* If this type is already being translated, return an opaque type. *)
      if List.exists inprocess ~f:(TypeUtilities.type_equiv sty)
      then pure ((Llvm.named_struct_type ctx name_ll |> Llvm.pointer_type), []) else

      let%bind adt = Datatypes.DataTypeDictionary.lookup_name tname in
      (* Let's get / create the types for each constructed ADTValue. *)
      let%bind cnames_ctrs_ty_ll = mapM adt.tconstr ~f:(fun ct ->
        let%bind arg_types = TypeUtilities.constr_pattern_arg_types sty ct.cname in
        let%bind arg_types_ll = mapM arg_types ~f:(fun t ->
          (* Ensure that we mark sty as "in process" before making the recursive call. *)
          let%bind (llty, _) = go ~inprocess:(sty :: inprocess) t in
          pure llty
        ) in
        (* In addition to the member literal types, we add a tag at the beginning. *)
        let tagged_arg_types_ll = Array.of_list @@ i8_type :: arg_types_ll in
        (* Come up with a name by suffixing the constructor name with the instantiated types. *)
        let%bind cname_ll = type_instantiated_adt_name ct.cname ts in
        let%bind ctr_ty_ll = named_struct_type ~is_packed:true llmod cname_ll tagged_arg_types_ll in
        (* We now have an llvm struct type to represent an object of this constructed type. *)
        pure (ct.cname, Llvm.pointer_type ctr_ty_ll)
      ) in
      let (_, ctrs_ty_ll) = List.unzip cnames_ctrs_ty_ll in
      (* We "union" the types of each constructed object type with a struct type that has a tag
      * at the start, and a list of pointers to each constructed object. The latter is only
      * to be able to verify that the constructor types and the main type are all related.
      * The tag is the only real element that will ever be accessed *)
      let%bind ty_ll = named_struct_type llmod name_ll (Array.of_list (i8_type :: ctrs_ty_ll)) in
      (* The final type will be a pointer to this struct. *)
      pure ((Llvm.pointer_type ty_ll), cnames_ctrs_ty_ll)
    | FunType (argts, rett) ->
      (* We don't know the type of the environment with just the "typ" of a function.
       * We make do with using a "void*" for it instead. *)
      let envty = void_ptr_type ctx in
      let%bind argts_ll = mapM argts ~f:(fun argt ->
        let%bind (argt_ll, _) = go ~inprocess:(sty :: inprocess) argt in
        if can_pass_by_val dl argt_ll then pure argt_ll else pure @@ Llvm.pointer_type argt_ll
      ) in
      let%bind (rett_ll, _) = go ~inprocess:(sty :: inprocess) rett in
      let funty = 
        if can_pass_by_val dl rett_ll
        then
        (* if return is by value, then "retval (envpointer, args ...)" *)
          Llvm.function_type rett_ll (Array.of_list (envty :: argts_ll))
        else
          let argts_final = envty :: (Llvm.pointer_type rett_ll) :: argts_ll in
          (* If return is not by value, then 1. env pointer, 2. ret value pointer, 3. args *)
          Llvm.function_type (Llvm.void_type ctx) (Array.of_list argts_final)
      in
      (* Functions are represented with closures, so return the closure type. *)
      pure (Llvm.struct_type ctx [|Llvm.pointer_type funty;void_ptr_type ctx|], [])
    | MapType _ -> fail0 "GenLlvm: genllvm_typ: MapType not supported yet"
    | PolyFun _ | TypeVar _ | Unit -> fail0 "GenLlvm: genllvm_typ: unsupported type"
  in
  go ~inprocess:[] sty

(* Returns only the first component of genllvm_typ. *)
let genllvm_typ_fst llmod sty =
  let%bind (sty', _) = genllvm_typ llmod sty in
  pure sty'

let rep_typ rep =
  match rep.ea_tp with
  | Some ty -> pure ty
  | None -> fail1 (sprintf "GenLlvm: rep_typ: not type annotated.")
            rep.ea_loc

let id_typ id = rep_typ (get_rep id)

let id_typ_ll llmod id =
  let%bind ty = id_typ id in
  let%bind (llty, _) = genllvm_typ llmod ty in
  pure llty

let ptr_element_type ptr_llty =
  match Llvm.classify_type ptr_llty with
  | Llvm.TypeKind.Pointer -> pure @@ Llvm.element_type ptr_llty
  | _ -> fail0 "GenLlvm: internal error: expected pointer type"

let struct_element_types sty =
  match Llvm.classify_type sty with
  | Llvm.TypeKind.Struct -> pure (Llvm.struct_element_types sty)
  | _ -> fail0 "GenLlvm: internal error: expected struct type"


(* Get the LLVM struct that holds an ADT's constructed object. Get its tag too.
 * Typically used on the output of genllvm_typ for ADT type. *)
let get_ctr_struct adt_llty_map cname =
  match List.Assoc.find adt_llty_map ~equal:(=) cname with
  | Some ptr_llcty -> (* We have a pointer type to the constructor's LLVM type. *)
    let%bind ctr_struct = ptr_element_type ptr_llcty in
    let%bind (adt, _) = DataTypeDictionary.lookup_constructor cname in
    (match List.findi adt.tconstr ~f:(fun _ cn -> cname = cn.cname) with
    | Some (tag, _) -> pure (ctr_struct, tag)
    | None -> fail0 (sprintf "GenLlvm: get_ctr_struct: internal error: constructor %s for adt %s not found" 
                      cname (adt.tname))
    )
  | None -> fail0 (sprintf "GenLlvm get_constr_type: LLVM type for ADT constructor %s not built" cname)

(* Convert a Scilla literal (compile time constant value) into LLVM-IR. *)
let rec genllvm_literal llmod l =
  let ctx = Llvm.module_context llmod in
  let i8_type = Llvm.i8_type ctx in
  let%bind sty = TypeUtilities.literal_type l in
  let%bind (llty, llctys) = genllvm_typ llmod sty in
  let build_scilla_bytes chars len =
    (* Mark chars to be an unnamed constant. *)
    Llvm.set_unnamed_addr true chars; Llvm.set_global_constant true chars;
    (* The global constant we just created is [slen x i8]*, cast it to ( i8* ) *)
    let chars' = Llvm.const_pointercast chars (Llvm.pointer_type i8_type) in
    (* Build a scilla_string_ty structure { i8*, i32 } *)
    let struct_elms = [|chars'; Llvm.const_int (Llvm.i32_type ctx) len|] in
    let conststruct = Llvm.const_named_struct llty struct_elms in
    (* We now have a ConstantStruct that represents our String/Bystr literal. *)
    conststruct
  in
  match l with
  | StringLit s -> (* Represented by scilla_string_ty. *)
    (* Build an array of characters. *)
    let chars = Llvm.define_global (newname "stringlit") (Llvm.const_string ctx s) llmod in
    pure @@ build_scilla_bytes chars (String.length s)
  | ByStr bs ->
    let i8s = Array.map (String.to_array @@ Bystr.to_raw_bytes bs) ~f:(fun c -> 
      Llvm.const_int i8_type (Char.to_int c)
    ) in
    let i8_array = Llvm.const_array i8_type i8s in
    let chars = Llvm.define_global (newname "bystrlit") i8_array llmod in
    pure @@ build_scilla_bytes chars (Array.length i8s)
  | IntLit il ->
    (* No better way to convert to LLVM integer than via strings :-(.
     * LLVM provides APIs that use APInt, but they aren't exposed via the OCaml API. *)
    pure @@ Llvm.const_named_struct llty
    (match il with
    | Int32L i -> [|(Llvm.const_int_of_string (Llvm.i32_type ctx) (Int32.to_string i) 10)|]
    | Int64L i -> [|Llvm.const_int_of_string (Llvm.i64_type ctx) (Int64.to_string i) 10|]
    | Int128L i -> [|Llvm.const_int_of_string (Llvm.integer_type ctx 128) (Stdint.Int128.to_string i) 10|]
    | Int256L i -> [|Llvm.const_int_of_string (Llvm.integer_type ctx 256) (Integer256.Int256.to_string i) 10|]
    )
  | UintLit uil ->
    pure @@ Llvm.const_named_struct llty
    (match uil with
    | Uint32L ui -> [|Llvm.const_int_of_string (Llvm.i32_type ctx) (Stdint.Uint32.to_string ui) 10|]
    | Uint64L ui -> [|Llvm.const_int_of_string (Llvm.i64_type ctx) (Stdint.Uint64.to_string ui) 10|]
    | Uint128L ui -> [|Llvm.const_int_of_string (Llvm.integer_type ctx 128) (Stdint.Uint128.to_string ui) 10|]
    | Uint256L ui -> [|Llvm.const_int_of_string (Llvm.integer_type ctx 256) (Integer256.Uint256.to_string ui) 10|]
    )
  | ByStrX bs ->
    let i8s = Array.map (String.to_array @@ Bystrx.to_raw_bytes bs) ~f:(fun c -> 
      Llvm.const_int i8_type (Char.to_int c)
    ) in
    pure @@ Llvm.const_array i8_type i8s
  | ADTValue (cname, _, lits) ->
      (* LLVM struct that'll hold this ADTValue. *)
      let%bind (llcty, tag) = get_ctr_struct llctys cname in
      let%bind lits_ll = mapM lits ~f:(genllvm_literal llmod) in
      (* Prepend the tag to the constructor object we're building. *)
      let lits' = (Llvm.const_int i8_type tag) :: lits_ll in
      let ctrval = Llvm.const_named_struct llcty (Array.of_list lits') in
      let p_ctrval = Llvm.define_global (newname "adtlit") ctrval llmod in
      (* Since ADTValues are boxed, i.e., represented by a pointer to the struct,
       * we are forced to create an unnamed global constant to get an address. *)
      Llvm.set_unnamed_addr true p_ctrval; Llvm.set_global_constant true p_ctrval;
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
  llvals : (string * value_scope) list; (* Resolve input AST name to a processed LLVM value *)
  retp : Llvm.llvalue option; (* For currently being generated function, return via memory? *)
  envparg : Llvm.llvalue option; (* Env pointer for the currently compiled function *)
}

(* Resolve a name from the identifier. *)
let resolve_id env id =
  match List.Assoc.find env.llvals ~equal:(=) (get_id id) with
  | Some scope -> pure scope
  | None -> fail1 (sprintf "GenLlvm: internal error: cannot resolve %s." (get_id id))
              (get_rep id).ea_loc

(* Resolve id, and if it's alloca, load the alloca. *)
let resolve_id_value env builder_opt id =
  let%bind resolved = resolve_id env id in
  match resolved with
  | Global llval | FunArg llval | CloP (llval, _) -> pure llval
  | Local llval ->
    (match builder_opt with
    | Some builder ->
      pure @@ Llvm.build_load llval (newname (get_id id)) builder
    | None -> fail1
      (sprintf "GenLlvm: resolve_id: internal error: llbuilder not provided to load alloca for %s."
      (get_id id)) (get_rep id).ea_loc
    )

(* Build a struct val of that type using the function declaration and env pointer.
 * The type of fundecl itself isn't used because it can have strong type for the
 * closure environment argument (the first argument of the function), but we want
 * to use a void* for the first argument when building a closure for compatibility
 * with other Scilla functions of the same type but different environment type.
 *)
let build_closure builder cloty_ll fundecl fname envp =
  if Llvm.classify_value fundecl <> Llvm.ValueKind.Function
  then fail1 (sprintf "GenLlvm: build_closure: internal error: Expected LLVM function declaration for %s."
          (get_id fname)) (get_rep fname).ea_loc
  else

  let ctx = Llvm.type_context cloty_ll in
  (* The fundef type is the first component of the closure type. *)
  let%bind clotys = struct_element_types cloty_ll in
  let%bind fundef_ty = array_get clotys 0 in
  (* Build a struct value for the closure. *)
  let fundecl' = Llvm.const_pointercast fundecl fundef_ty in
  let tmp = Llvm.build_insertvalue (Llvm.undef cloty_ll) fundecl' 0 (newname (get_id fname)) builder in
  let envp_void = Llvm.build_pointercast envp (void_ptr_type ctx)
    (newname ((get_id fname) ^ "_env_voidp")) builder in
  let cloval = Llvm.build_insertvalue tmp envp_void 1 (newname ((get_id fname) ^ "_cloval")) builder in
  pure cloval

(* Insert alloca at the beginning of the function. *)
let build_alloca_fn func llty name =
  let llctx = Llvm.global_parent func |> Llvm.module_context in 
  let insert_point = Llvm.instr_begin (Llvm.entry_block func) in
  (* This is a bit heavy weight, to creat a new builder everytime,
   * but we have no option to save and restore builder position
   * in the LLVM C-API (and hence the OCaml API). *)
  let builder = Llvm.builder_at llctx insert_point in
  Llvm.build_alloca llty name builder

let genllvm_expr genv builder (e, erep) =
  let llmod = Llvm.insertion_block builder |> Llvm.block_parent |> Llvm.global_parent in
  let llctx = Llvm.module_context llmod in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in

  match e with
  | Literal l -> genllvm_literal llmod l
  | Var v -> resolve_id_value genv (Some builder) v
  | Constr (cname, _, cargs) ->
    let%bind sty = rep_typ erep in
    let%bind (llty, llctys) = genllvm_typ llmod sty in
    let%bind (llcty, tag) = get_ctr_struct llctys cname in
    let%bind cargs_ll = mapM cargs ~f:(resolve_id_value genv (Some builder)) in
    (* Append the tag to the struct elements. *)
    let cargs_ll' = (Llvm.const_int (Llvm.i8_type llctx) tag) :: cargs_ll in
    let cmem = Llvm.build_malloc llcty (newname "adtval") builder in
    (* Store each element of the struct into the malloc'd memory. *)
    List.iteri cargs_ll' ~f:(fun i el ->
      let gep = Llvm.build_struct_gep cmem i (newname "adtgep") builder in
      let _ = Llvm.build_store el gep builder in
      ()
    );
    let adtp = Llvm.build_bitcast cmem llty (newname "adtptr") builder in
    pure adtp
  | FunClo fc ->
    let fname = fst fc.envvars in
    let%bind resolved = resolve_id genv fname in
    (match resolved with
    | CloP (cp, _) -> (* TODO: Ensure initialized. Requires stronger type for cloenv. *)
      pure cp
    | Global gv ->
      (* If the function resolves to a declaration, it means we haven't allocated
       * a closure for it (i.e., no AllocCloEnv statement). Ensure empty environment. *)
      if not (List.is_empty (snd fc.envvars)) then
      fail1 (sprintf "GenLlvm: genllvm_expr: Expected closure for %s with empty environment."
              (get_id fname)) erep.ea_loc
      else
        (* Build a closure object with empty environment. *)
        let envp = Llvm.const_null (void_ptr_type llctx) in
        let%bind fundef_ty_ll = id_typ_ll llmod fname in
        let%bind cloval = build_closure builder fundef_ty_ll gv fname envp in
        pure cloval
    | _ -> fail1 (sprintf "GenLlvm: genllvm:expr: Incorrect resolution of %s."
            (get_id fname)) erep.ea_loc
    )
  | App (f, args) ->
    (* Resolve f (to a closure value) *) 
    let%bind fclo_ll = resolve_id_value genv (Some builder) f in
    (* and extract the fundef and environment pointers. *)
    let fptr = Llvm.build_extractvalue fclo_ll 0 (newname ((get_id f) ^ "_fptr")) builder in
    let%bind fty = ptr_element_type (Llvm.type_of fptr) in
    let envptr = Llvm.build_extractvalue fclo_ll 1 (newname ((get_id f) ^ "_envptr")) builder in
    (* Resolve all arguments. *)
    let%bind args_ll = mapM args ~f:(fun arg ->
      let%bind arg_ty = id_typ_ll llmod arg in
      if can_pass_by_val dl arg_ty
      then resolve_id_value genv (Some builder) arg
      else
        (* Create an alloca, write the value to it, and pass the address. *)
        let argmem = Llvm.build_alloca arg_ty (newname ((get_id f) ^ "_" ^ (get_id arg))) builder in
        let%bind arg' = resolve_id_value genv (Some builder) arg in
        let _ = Llvm.build_store arg' argmem builder in
        pure argmem
    ) in
    let param_tys = Llvm.param_types fty in
    if Array.length param_tys = (List.length args) + 1
    then
      (* Return by value. *)
      pure @@
        Llvm.build_call fptr (Array.of_list (envptr :: args_ll)) (newname ((get_id f) ^ "_call")) builder
    else if Array.length param_tys = (List.length args) + 2
    then
      (* Allocate a temporary stack variable for the return value. *)
      let%bind pretty_ty = array_get param_tys 1 in
      let%bind retty = ptr_element_type pretty_ty in
      (* No need to use build_alloca_fn as value is one time use only. *)
      let ret_alloca = Llvm.build_alloca retty (newname ((get_id f) ^ "_retalloca")) builder in
      let _ =
        Llvm.build_call fptr (Array.of_list (envptr :: ret_alloca :: args_ll)) "" builder
      in
      (* Load from ret_alloca. *)
      pure @@ Llvm.build_load ret_alloca (newname ((get_id f) ^ "_ret")) builder
    else
      fail1 (sprintf "%s %s." ("GenLlvm: genllvm_expr: internal error: Incorrect number of arguments" ^
        " when compiling function application") (get_id f)) erep.ea_loc
  | _ -> fail1 "GenLlvm: genllvm_expr: unimplimented" erep.ea_loc

(* Translate stmts into LLVM-IR by inserting instructions through irbuilder.
 * Local variables are held in function-wide allocas since we don't know their scope.
 * Name clashes aren't a problem as it was taken care of in the ScopingRename pass.
 * The mem2reg pass will promote these allocas to virtual registers, no worries. *)
let genllvm_stmts genv builder stmts =
  let func = Llvm.insertion_block builder |> Llvm.block_parent in
  let llmod = Llvm.global_parent func in

  (* Check that the LLVM struct type for an env matches the list of env vars we know. *)
  let validate_envvars_type env_ty evars =
    let%bind struct_types = struct_element_types env_ty in
    if Array.length struct_types <> List.length evars
    then fail0 "GenLlvm: genllvm_stmts: internal error: closure environment lengths mismatch."
    else
      let%bind evars_typs_ll = mapM evars ~f:(fun (_, t) -> genllvm_typ_fst llmod t) in
      if List.equal (Array.to_list struct_types) evars_typs_ll ~equal:(=) then pure ()
      else fail0 "GenLlvm: genllvm_stmts: internal error: closure environment types mismatch."
  in

  let%bind _ = foldM stmts ~init:genv ~f:(fun accenv (stmt, _) ->
    match stmt with
    | Bind (x, e) ->
      let%bind xty_ll = id_typ_ll llmod x in
      let xll = build_alloca_fn func xty_ll (get_id x)  in
      let%bind e_val = genllvm_expr accenv builder e in
      let _ = Llvm.build_store e_val xll builder in
      pure @@ { accenv with llvals = (get_id x, (Local xll)) :: accenv.llvals }
    | Ret v ->
      let%bind vll = resolve_id_value accenv (Some builder) v in
      let _ = (match accenv.retp with
      | None ->
        Llvm.build_ret vll builder
      | Some p ->
        let _ = Llvm.build_store vll p builder in
        Llvm.build_ret_void builder
      ) in
      pure accenv
    | AllocCloEnv (fname, evars) -> (* Allocate memory for the environment and build a closure object. *)
      (* We don't pass the builder because we expect fname to resolve to a global function. *)
      let%bind fdecl = resolve_id_value accenv None fname in
      let%bind fun_ty = ptr_element_type (Llvm.type_of fdecl) in
      if Llvm.classify_type fun_ty <> Llvm.TypeKind.Function
      then fail0 "GenLlvm: genllvm_stmts: internal error: Expected function type." else
      (* The first argument of fdecl is to the environment *)
      let%bind env_ty_p = array_get (Llvm.param_types fun_ty) 0 in
      let%bind env_ty = ptr_element_type env_ty_p in
      let%bind _ = validate_envvars_type env_ty evars in
      (* Allocate the environment. *)
      let envp = Llvm.build_malloc env_ty (newname ((get_id fname) ^ "_envp")) builder in
      let%bind clo_ty_ll = id_typ_ll llmod fname in
      let%bind resolved_fname = resolve_id accenv fname in
      (match resolved_fname with
      | Global fd ->
        let%bind cloval = build_closure builder clo_ty_ll fd fname envp in
        (* Now we bind fname to cloval instead of the function declaration it originally was bound to. *)
        pure { accenv with llvals = ((get_id fname), CloP (cloval, env_ty)) :: accenv.llvals }
      | _ -> fail1 (sprintf "GenLlvm: genllvm_stmts: %s did not resolve to global declaration."
                (get_id fname)) (get_rep fname).ea_loc
      )
    | StoreEnv (envvar, v, (fname, envvars)) ->
      let%bind resolved_fname = resolve_id accenv fname in
      (match resolved_fname with
      | CloP (cloval, envty) ->
        let%bind _ = validate_envvars_type envty envvars in
        (* Get the second component of cloval (the envptr) and cast it to right type. *)
        let envvoidp = Llvm.build_extractvalue cloval 1 (newname ((get_id fname) ^ "_envp")) builder in
        let envp = Llvm.build_bitcast envvoidp (Llvm.pointer_type envty)
          (newname ((get_id fname) ^ "_envp")) builder in
        (* Search for envvar in envvars and get its index. *)
        let%bind i =
          (match List.findi envvars ~f:(fun _ (envvar', _) -> equal_id envvar envvar') with
          | Some (i, _) -> pure i
          | None -> fail1 (sprintf "GenLlvm: genllvm_stmts: internal error: %s not found in env of %s."
                      (get_id envvar) (get_id fname)) (get_rep fname).ea_loc
          )
        in
        (* Store v into envp[i] *)
        let envp_i = Llvm.build_struct_gep envp i
          (newname ((get_id fname) ^ "_env_" ^ (get_id envvar))) builder
        in
        let%bind vresolved = resolve_id_value accenv (Some builder) v in
        let _ = Llvm.build_store vresolved envp_i builder in
        (* This operation doesn't affect our codegen environment. *)
        pure accenv
      | _ -> fail1 (sprintf "GenLlvm: genllvm_stmts: internal error: expected %s to resolve to closure."
                    (get_id fname)) (get_rep fname).ea_loc
      )
    | LoadEnv (v, envvar, (fname, envvars)) ->
      (match accenv.envparg with
      | Some envp ->
        let%bind envty = ptr_element_type (Llvm.type_of envp) in
        let%bind _ = validate_envvars_type envty envvars in
        (* Search for envvar in envvars and get its index. *)
        let%bind i =
          (match List.findi envvars ~f:(fun _ (envvar', _) -> equal_id envvar envvar') with
          | Some (i, _) -> pure i
          | None -> fail1 (sprintf "GenLlvm: genllvm_stmts: internal error: %s not found in env of %s."
                      (get_id envvar) (get_id fname)) (get_rep fname).ea_loc
          )
        in
        (* Load from envp[i] into v *)
        let envp_i = Llvm.build_struct_gep envp i
          (newname ((get_id fname) ^ "_env_" ^ (get_id envvar))) builder
        in
        let loadi = Llvm.build_load envp_i (newname ((get_id v) ^ "_envload")) builder in
        (* Put the loaded value into a local variable, so that we can bind it as a Local. *)
        let loadi_alloca = build_alloca_fn func (Llvm.type_of loadi) (get_id v)  in
        let _ = Llvm.build_store loadi loadi_alloca builder in
        pure { accenv with llvals = (get_id v, Local loadi_alloca) :: accenv.llvals }
      | None -> fail1 (sprintf "GenLlvm: genllvm_stmts: internal error: expected envparg when compiling fundef %s."
                    (get_id fname)) (get_rep fname).ea_loc
      )
    | _ -> pure accenv
  ) in
  pure ()

let genllvm_closures llmod topfuns =
  let ctx = Llvm.module_context llmod in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  (* We translate closures in two passes, the first pass declares them
   * all and the second one does the actual translation of the bodies. *)
  let%bind fdecls = foldrM topfuns ~init:[] ~f:(fun accenv cr ->
    let%bind ret_ty_ll = genllvm_typ_fst llmod !(cr.thisfun).fretty in
    let%bind envars_ty_ll = mapM (snd cr.envvars) ~f:(Fn.compose (genllvm_typ_fst llmod) snd) in
    let envty_name = newname (get_id !(cr.thisfun).fname ^ "_env") in
    let%bind env_ty_ll = named_struct_type llmod envty_name (Array.of_list envars_ty_ll) in
    let penv_ty_ll = Llvm.pointer_type env_ty_ll in
    let%bind args_ty_ll = mapM !(cr.thisfun).fargs ~f:(Fn.compose (genllvm_typ_fst llmod) snd) in
    (* Check if an argument needs to be passed through a pointer. *)
    let args_ty_ll' = List.map args_ty_ll ~f:(fun llt ->
      if can_pass_by_val dl llt then llt else Llvm.pointer_type llt
    ) in
    let%bind decl =
      (* We can't use "genllvm_typ" because it doesn't know the type of the environment. *)
      if can_pass_by_val dl ret_ty_ll
      (* return type, env pointer type, argument types *)
      then scilla_function_decl llmod (get_id !(cr.thisfun).fname) ret_ty_ll (penv_ty_ll :: args_ty_ll')
      else
        (* returns void (return value is via the stack),
         * env pointer type, type of pointer to return type, argument types *)
        let fargs_ty = penv_ty_ll :: (Llvm.pointer_type ret_ty_ll) :: args_ty_ll' in
        scilla_function_decl llmod (get_id !(cr.thisfun).fname) (Llvm.void_type ctx) fargs_ty
    in
    pure @@ ((get_id !(cr.thisfun).fname), decl) :: accenv
  ) in

  let genv_fdecls = {
    llvals = List.map fdecls ~f:(fun (fname, decl) -> (fname, Global decl));
    retp = None;
    envparg = None;
  } in

  (* Let us now define each of these functions. *)
  let fdecl_cr_l = List.zip_exn fdecls topfuns in
  let%bind _ = iterM fdecl_cr_l ~f:(fun ((fname, f), cr) ->
    let fid = !(cr.thisfun).fname in
    (* The function f doesn't have a body yet, so insert a basic block. *)
    let _ = Llvm.append_block ctx "entry" f in
    let builder = Llvm.builder_at_end ctx (Llvm.entry_block f) in
    let sfdef_args = !(cr.thisfun).fargs in
    let f_params = (Llvm.params f) in
    let%bind envparg = array_get f_params 0 in
    (* Bind the envptr arg for codegen inside the function. *)
    let genv_envparg = { genv_fdecls with envparg = Some envparg } in
    (* Bind the return value argument if via a pointer. *)
    let%bind args_begin, genv_retp = 
      if (List.length sfdef_args + 1) = Array.length f_params then
      (* Return value is not through a pointer. *)
      pure (1, genv_envparg)
      else if (List.length sfdef_args + 2) = Array.length f_params then
        (* Return value is through the second argument, a pointer. *)
        let%bind retp = array_get f_params 1 in
        pure (2, { genv_envparg with retp = Some retp })
      else fail1 (sprintf
        "GenLlvm: genllvm_closures: internal error compiling fundef %s. Incorrect number of arguments."
        fname) (get_rep fid).ea_loc
    in
    (* Now bind each function argument. *)
    let%bind (genv_args, _) = foldrM sfdef_args ~init:(genv_retp, (List.length sfdef_args) - 1)
    ~f:(fun (accum_genv, idx) (varg, sty) ->
      let%bind arg_llval = array_get f_params (args_begin + idx) in
      let%bind sty_llty = genllvm_typ_fst llmod sty in
      let arg_mismatch_err =
        fail1 (sprintf "GenLlvm: genllvm_closures: type mismatch in argument %s compiling function %s."
          (get_id varg) (get_id fid)) (get_rep fid).ea_loc
      in
      let%bind arg_llval' =
        if can_pass_by_val dl sty_llty
        then
          if sty_llty = Llvm.type_of arg_llval then pure arg_llval else arg_mismatch_err
        else
          if Llvm.pointer_type sty_llty = (Llvm.type_of arg_llval)
          then pure (Llvm.build_load arg_llval (get_id varg) builder)
          else arg_mismatch_err
      in
      pure (
        { accum_genv with llvals = (get_id varg, FunArg arg_llval') :: accum_genv.llvals }, (idx-1)
      )
    ) in
    (* We now have the environment to generate the function body. *)
    genllvm_stmts genv_args builder !(cr.thisfun).fbody
  ) in

  pure genv_fdecls

let prepare_target llmod =
  (* We only support generating code for x86_64. *)
  Llvm_X86.initialize();
  let triple = Llvm_target.Target.default_triple () in
  let lltarget  = Llvm_target.Target.by_triple triple in
  let llmachine = Llvm_target.TargetMachine.create ~triple:triple lltarget in
  let lldly     = Llvm_target.DataLayout.as_string (Llvm_target.TargetMachine.data_layout llmachine) in
  let _ = Llvm.set_target_triple triple llmod in
  let _ = Llvm.set_data_layout lldly llmod in
  ()

(* Generate an LLVM module for a Scilla module. *)
let genllvm_module (cmod : cmodule) =
  let llcontext = Llvm.create_context () in
  let llmod = Llvm.create_module llcontext (get_id cmod.contr.cname) in
  let _ = prepare_target llmod in

  (* printf "\n%s\n" (Llvm.string_of_llmodule llmod); *)

  match Llvm_analysis.verify_module llmod with
  | None ->
    pure (Llvm.string_of_llmodule llmod)
  | Some err -> fail0 ("GenLlvm: genllvm_module: internal error: " ^ err)

(* Generate an LLVM module for a statement sequence. *)
let genllvm_stmt_list_wrapper stmts =
  let llcontext = Llvm.create_context () in
  let llmod = Llvm.create_module llcontext "scilla_expr" in
  let _ = prepare_target llmod in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in

  (* Gather all the top level functions. *)
  let topclos = gather_closures stmts in
  let%bind genv_fdecls = genllvm_closures llmod topclos in

  (* Create a function to house the instructions. *)
  let%bind fty =
    (* Let's look at the last statement and try to infer a return type. *)
    match List.last stmts with
    | Some ((Ret v), _) ->
      let%bind retty_ll = id_typ_ll llmod v in
      if can_pass_by_val dl retty_ll
      (* First argument, as per convention, is an (empty) envptr. *)
      then pure @@ Llvm.function_type retty_ll [|void_ptr_type llcontext|]
      (* First argument is an (empty) envptr and second is the pointer to return value. *)
      else pure @@ Llvm.function_type (Llvm.void_type llcontext)
        [|void_ptr_type llcontext;Llvm.pointer_type retty_ll|]
    | _ -> fail0 "GenLlvm: genllvm_stmt_list_wrapper: expected last statment to be Ret"
  in
  let f = Llvm.define_function (newname "scilla_expr") fty llmod in
  let%bind init_env =
    if Llvm.void_type llcontext = Llvm.return_type fty
    then
      (* If return type is void, then second parameter is the pointer to return value. *)
      let%bind retp = array_get (Llvm.params f) 1 in
      pure { genv_fdecls with retp = Some retp }
    else
      pure { genv_fdecls with retp = None }
  in
  let irbuilder = Llvm.builder_at_end llcontext (Llvm.entry_block f) in
  let%bind _ = genllvm_stmts init_env irbuilder stmts in

  (* printf "\n%s\n" (Llvm.string_of_llmodule llmod); *)

  match Llvm_analysis.verify_module llmod with
  | None ->
    pure (Llvm.string_of_llmodule llmod)
  | Some err -> fail0 ("GenLlvm: genllvm_stmt_list_wrapper: internal error: " ^ err)