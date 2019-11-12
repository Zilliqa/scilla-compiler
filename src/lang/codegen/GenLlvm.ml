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
 *)

open Core
open Result.Let_syntax
open MonadUtil
open Syntax
open ClosuredSyntax
open CodegenUtils
open TypeUtil
open Datatypes

(* Create a named struct with types from tyarr. *)
let named_struct_type ?(is_packed=false) llmod name tyarr =
  let ctx = Llvm.module_context llmod in
  match Llvm.type_by_name llmod name with
  | Some ty -> ty
  | None ->
    let t = Llvm.named_struct_type ctx name in
    let _ = Llvm.struct_set_body t tyarr is_packed in
    t

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
 * The definition is expected to be written in C/C++ in SRTL.
 * Fails if the return type or arg types cannot be passed by value. *)
let srtl_function_decl llmod fname retty argtys =
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
let rec genllvm_typ llmod sty =

  let ctx = Llvm.module_context llmod in
  let i8_type = Llvm.i8_type ctx in

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

  match sty with
  | PrimType pty ->
    let%bind llty = (match pty with
      (* Build integer types, by wrapping LLMV's i* type in structs with names. *)
      | Int_typ bw | Uint_typ bw ->
        let bwi = match bw with | Bits32 -> 32 | Bits64 -> 64 | Bits128 -> 128 | Bits256 -> 256 in
        pure @@ named_struct_type llmod (pp_prim_typ pty) [|Llvm.integer_type ctx bwi|]
      (* An instantiation of scilla_bytes_ty for Scilla String. *)
      | String_typ -> pure @@ scilla_bytes_ty "String"
      (* An instantiation of scilla_bytes_ty for Scilla Bystr. *)
      | Bystr_typ -> pure @@ scilla_bytes_ty "Bystr"
      (* ByStrX represented as an LLVM array of length X. *)
      | Bystrx_typ bytes -> pure @@ Llvm.array_type i8_type bytes
      | Msg_typ | Event_typ | Exception_typ | Bnum_typ -> fail0 "GenLlvm: genllvm_prim_typ: unimplemented"
      ) in
    pure (llty, [])
  | ADT (tname, ts) ->
    let%bind adt = Datatypes.DataTypeDictionary.lookup_name tname in
    (* Let's get / create the types for each constructed ADTValue. *)
    let%bind cnames_ctrs_ty_ll = mapM adt.tconstr ~f:(fun ct ->
      let%bind arg_types = TypeUtilities.constr_pattern_arg_types sty ct.cname in
      let%bind arg_types_ll = mapM arg_types ~f:(fun t ->
        let%bind (llty, _) = genllvm_typ llmod t in
        pure llty
      ) in
      (* In addition to the member literal types, we add a tag at the beginning. *)
      let tagged_arg_types_ll = Array.of_list @@ i8_type :: arg_types_ll in
      (* Come up with a name by suffixing the constructor name with the instantiated types. *)
      let%bind cname_ll = type_instantiated_adt_name ct.cname ts in
      let ctr_ty_ll = named_struct_type ~is_packed:true llmod cname_ll tagged_arg_types_ll in
      (* We now have an llvm struct type to represent an object of this constructed type. *)
      pure (ct.cname, Llvm.pointer_type ctr_ty_ll)
    ) in
    let (_, ctrs_ty_ll) = List.unzip cnames_ctrs_ty_ll in
    (* We "union" the types of each constructed object type with a struct type that has a tag
     * at the start, and a list of pointers to each constructed object. The latter is only
     * to be able to verify that the constructor types and the main type are all related.
     * The tag is the only real element that will ever be accessed *)
    let%bind name_ll = type_instantiated_adt_name tname ts in
    let ty_ll = named_struct_type llmod name_ll (Array.of_list (i8_type :: ctrs_ty_ll)) in
    (* The final type will be a pointer to this struct. *)
    pure ((Llvm.pointer_type ty_ll), cnames_ctrs_ty_ll)
  | MapType _ -> fail0 "GenLlvm: genllvm_typ: MapType not supported yet"
  | FunType _ | PolyFun _ | TypeVar _ | Unit -> fail0 "GenLlvm: genllvm_typ: unsupported type"

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
    (* LLVM type name for the struct that'll hold this ADTValue. *)
    (match List.Assoc.find llctys ~equal:(=) cname with
    | Some ptr_llcty -> (* We have a pointer type to the constructor's LLVM type. *)
      let%bind llcty =
        match Llvm.classify_type ptr_llcty with
        | Llvm.TypeKind.Pointer -> pure @@ Llvm.element_type ptr_llcty
        | _ -> fail0 "GenLlvm: internal error: expected pointer to constructor's LLVM struct type"
      in
      let%bind lits_ll = mapM lits ~f:(genllvm_literal llmod) in
      let%bind adt = DataTypeDictionary.lookup_name cname in
      (match List.findi adt.tconstr ~f:(fun _ cn -> cname = cn.cname) with
      | Some (tag, _) ->
        (* Prepend the tag to the constructor object we're building. *)
        let lits' = (Llvm.const_int i8_type tag) :: lits_ll in
        let adtval = Llvm.const_named_struct llcty (Array.of_list lits') in
        let p_adtval = Llvm.define_global (newname "adtlit") adtval llmod in
        Llvm.set_unnamed_addr true p_adtval; Llvm.set_global_constant true p_adtval;
        (* Since ADTValues are boxed, i.e., represented by a pointer to the struct,
         * we are forced to create an unnamed global constant to get an address. *)
        pure p_adtval
      | None ->
        fail0 (Printf.sprintf "GenLlvm: internal error: constructor %s for adt %s not found" cname (adt.tname))
      )
    | None -> 
      fail0 (Printf.sprintf "GenLlvm: internal error: type for ADT constructor %s not built" cname)
    )
  | BNum _ | Msg _ | Map _ -> fail0 "GenLlvm: Unimplemented"
  | Clo _ | TAbs _ -> fail0 "GenLlvm: Cannot translate runtime literals"

open CloCnvSyntax

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

  match Llvm_analysis.verify_module llmod with
  | None ->
    pure (Llvm.string_of_llmodule llmod)
  | Some err -> fail0 ("GenLlvm: genllvm_module: internal error: " ^ err)

(* Generate an LLVM module for a statement sequence. *)
let genllvm_stmt_list_wrapper _stmts =
  let llcontext = Llvm.create_context () in
  let llmod = Llvm.create_module llcontext "scilla_expr" in
  let _ = prepare_target llmod in

  match Llvm_analysis.verify_module llmod with
  | None ->
    pure (Llvm.string_of_llmodule llmod)
  | Some err -> fail0 ("GenLlvm: genllvm_expr_wrapper: internal error: " ^ err)