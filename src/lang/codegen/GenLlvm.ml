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
 *    All ADTs are boxed, i.e., represented by a pointer to a
 *    packed struct containing the actual ADTValue. Record description:
 *      %cnameI_ts1_..._tsn = type { i8, [type of each element of ls] }
 *      %tname_ts1_..._tsn = type { i8 } ;; contains just the tag
 *      %p = %tname_ts1_...tsn* <bitcast> pointer_type (%cnameI_ts1_..._tsn)
 *    Each constructor cnameI of a Scilla ADT will have a type "cnameI_ts1_..tsn"
 *    and they will all be bitcasted into "tname_ts1_...tsn" where tname and
 *    cname stand for ADT type name and constructor names, and the "_ts1...tsn"
 *    are the particular polymorphic instantiation.
 *    The structs are packed so that it's straightforward to parse them from
 *    handwritten C++ code in the SRTL without worrying about padding.
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

(* Create a StructType "scilla_bytes_ty" = type { i8*, i32 }. 
 * This type can represent Scilla String and ByStr values.
 * Note: We cannot use LLVM's Array type to represent bytes because
 *       that requires the length to be known at compile time. *)
let scilla_bytes_ty ty_name llmod =
  let ctx = Llvm.module_context llmod in
  let charp_ty = Llvm.pointer_type (Llvm.i8_type ctx) in
  let len_ty = Llvm.i32_type ctx in
  named_struct_type llmod ty_name [|charp_ty;len_ty|]

(* An instantiation of scilla_bytes_ty for Scilla Strings. *)
let scilla_string_ty = scilla_bytes_ty "String"
(* An instantiation of scilla_bytes_ty for Scilla Bystr. *)
let scilla_bystr_ty = scilla_bytes_ty "Bystr"

(* Build integer types, by wrapping LLMV's i* type in structs with names. *)
let scilla_int_ty llmod sty =
  let ctx = Llvm.module_context llmod in
  match sty with
  | PrimType (Int_typ bw as pty) | PrimType (Uint_typ bw as pty) ->
    let bwi = match bw with | Bits32 -> 32 | Bits64 -> 64 | Bits128 -> 128 | Bits256 -> 256 in
    pure @@ named_struct_type llmod (pp_prim_typ pty) [|Llvm.integer_type ctx bwi|]
  | _ -> fail0 "GenLlvm: scilla_int_ty: not integer type"

(* Convert a Scilla literal (compile time constant value) into LLVM-IR. *)
let genllvm_literal llmod l =
  let ctx = Llvm.module_context llmod in
  let%bind sty = TypeUtilities.literal_type l in
  match l with
  | StringLit s -> (* Represented by scilla_string_ty. *)
    (* Build an array of characters. *)
    let chars = Llvm.define_global (newname "stringlit") (Llvm.const_string ctx s) llmod in
    (* Mark chars to be an unnamed constant. *)
    Llvm.set_unnamed_addr true chars; Llvm.set_global_constant true chars;
    (* The global constant we just created is [slen x i8]*, cast it to ( i8* ) *)
    let chars' = Llvm.const_pointercast chars (Llvm.pointer_type (Llvm.i8_type ctx)) in
    (* Build a scilla_string_ty structure { i8*, i32 } *)
    let struct_elms = [|chars'; Llvm.const_int (Llvm.i32_type ctx) (String.length s)|] in
    let conststruct = Llvm.const_named_struct (scilla_string_ty llmod) struct_elms in
    (* We now have a ConstantStruct that represents our String literal. *)
    pure conststruct
  | IntLit il ->
    let%bind ty = scilla_int_ty llmod sty in
    (* No better way to convert to LLVM integer than via strings :-(.
     * LLVM provides APIs that use APInt, but they aren't exposed via the OCaml API. *)
    pure @@ Llvm.const_named_struct ty
    (match il with
    | Int32L i -> [|(Llvm.const_int_of_string (Llvm.i32_type ctx) (Int32.to_string i) 10)|]
    | Int64L i -> [|Llvm.const_int_of_string (Llvm.i64_type ctx) (Int64.to_string i) 10|]
    | Int128L i -> [|Llvm.const_int_of_string (Llvm.integer_type ctx 128) (Stdint.Int128.to_string i) 10|]
    | Int256L i -> [|Llvm.const_int_of_string (Llvm.integer_type ctx 256) (Integer256.Int256.to_string i) 10|]
    )
  | UintLit uil ->
    let%bind ty = scilla_int_ty llmod sty in
    pure @@ Llvm.const_named_struct ty
    (match uil with
    | Uint32L ui -> [|Llvm.const_int_of_string (Llvm.i32_type ctx) (Stdint.Uint32.to_string ui) 10|]
    | Uint64L ui -> [|Llvm.const_int_of_string (Llvm.i64_type ctx) (Stdint.Uint64.to_string ui) 10|]
    | Uint128L ui -> [|Llvm.const_int_of_string (Llvm.integer_type ctx 128) (Stdint.Uint128.to_string ui) 10|]
    | Uint256L ui -> [|Llvm.const_int_of_string (Llvm.integer_type ctx 256) (Integer256.Uint256.to_string ui) 10|]
    )
  | BNum _bns -> pure @@ Llvm.const_pointer_null (Llvm.void_type ctx)
  | ByStrX _bs -> pure @@ Llvm.const_pointer_null (Llvm.void_type ctx)
  | ByStr _bs -> pure @@ Llvm.const_pointer_null (Llvm.void_type ctx)
  | Msg _sls -> pure @@ Llvm.const_pointer_null (Llvm.void_type ctx)
  | Map (_, _htbl) -> pure @@ Llvm.const_pointer_null (Llvm.void_type ctx)
  | ADTValue (_cname, _tls, _lits) -> pure @@ Llvm.const_pointer_null (Llvm.void_type ctx)
  | Clo _ | TAbs _ -> fail0 "GenLlvm: Cannot translate runtime literals"

(* A function to demo linking to an external function to print Scilla String. *)
let demo_link_to_string_print llmod =
  let llcontext = Llvm.module_context llmod in
  (*
      /* Contents of C code to link against */

      #include <stdio.h>

      typedef struct
      {
        uint8_t *buf;
        int len;
      } String;

      void scilla_string_print(String a)
      {
        for (int i = 0; i < a.len; i++)
          putchar(a.buf[i]);
        putchar('\n');
      }

      extern void call_scilla_string_print(void);

      int main() {
        call_scilla_string_print();
        return 0;
      }
  *)
  (* Let us generate a function that can link to the C snippet shown just above. *)
  let%bind scilla_string_print_decl = srtl_function_decl llmod "scilla_string_print" 
    (Llvm.void_type llcontext) [scilla_string_ty llmod] in
  let call_scilla_string_print_ty = Llvm.function_type (Llvm.void_type llcontext) [||] in
  let f = Llvm.define_function "call_scilla_string_print" call_scilla_string_print_ty llmod in
  let l = StringLit "hello" in
  let%bind ll = genllvm_literal llmod l in
  let%bind _ =
    let%bind intlit = genllvm_literal llmod (UintLit (Uint128L (Stdint.Uint128.of_int 44))) in
    let intlitg = Llvm.define_global (newname "intlit") intlit llmod in
    Llvm.set_unnamed_addr true intlitg; Llvm.set_global_constant true intlitg;
    pure ()
  in
  let eblock = Llvm.entry_block f in
  let builder = Llvm.builder_at_end llcontext eblock in
  let _ = Llvm.build_call scilla_string_print_decl [|ll|] "" builder in
  let _ = Llvm.build_ret_void builder in
  pure llmod

let genllvm_module (cmod : CloCnvSyntax.cmodule) =
  let llcontext = Llvm.create_context () in
  (* We only support generating code for x86_64. *)
  Llvm_X86.initialize();
  (* Setup a module, a target etc ... *)
  let llmod = Llvm.create_module llcontext (get_id cmod.contr.cname) in
  let triple = Llvm_target.Target.default_triple () in
  let lltarget  = Llvm_target.Target.by_triple triple in
  let llmachine = Llvm_target.TargetMachine.create ~triple:triple lltarget in
  let lldly     = Llvm_target.DataLayout.as_string (Llvm_target.TargetMachine.data_layout llmachine) in
  let _ = Llvm.set_target_triple triple llmod in
  let _ = Llvm.set_data_layout lldly llmod in

  (* Generate a demo to link against an external function that prints a Scilla string. *)
  (* let%bind _ = demo_link_to_string_print llmod in *)

  match Llvm_analysis.verify_module llmod with
  | None ->
    pure (Llvm.string_of_llmodule llmod)
  | Some err -> fail0 ("GenLlvm internal error: " ^ err)
