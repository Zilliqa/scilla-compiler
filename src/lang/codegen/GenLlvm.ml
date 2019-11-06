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

(* This file translates the closure converted AST into LLVM-IR. *)

open Core
open Result.Let_syntax
open MonadUtil
open Syntax
open ClosuredSyntax
open CodegenUtils

(* Create a named struct with types from tyarr. *)
let named_struct_type ctx name tyarr =
  let t = Llvm.named_struct_type ctx name in
  let _ = Llvm.struct_set_body t tyarr false in
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
  match Llvm.type_by_name llmod ty_name with
  | None ->
    let charp_ty = Llvm.pointer_type (Llvm.i8_type ctx) in
    let len_ty = Llvm.i32_type ctx in
    named_struct_type ctx ty_name [|charp_ty;len_ty|]
  | Some ty -> ty

(* An instantiation of scilla_bytes_ty for Scilla Strings. *)
let scilla_string_ty = scilla_bytes_ty "scilla_string_ty"

let genllvm_literal ctx llmod l =
  let i32_ty = Llvm.i32_type ctx in
  match l with
  | StringLit s -> (* Represented by scilla_string_ty. *)
    (* Build an array of characters. *)
    let chars = Llvm.define_global (newname "stringlit") (Llvm.const_string ctx s) llmod in
    (* Mark chars to be an unnamed constant. *)
    Llvm.set_unnamed_addr true chars; Llvm.set_global_constant true chars;
    (* The global constant we just created is [slen x i8]*, cast it to ( i8* ) *)
    let chars' = Llvm.const_pointercast chars (Llvm.pointer_type (Llvm.i8_type ctx)) in
    (* Build a scilla_string_ty structure { i8*, i32 } *)
    let struct_elms = [|chars'; Llvm.const_int i32_ty (String.length s)|] in
    let conststruct = Llvm.const_named_struct (scilla_string_ty llmod) struct_elms in
    (* We now have a ConstantStruct that represents our String literal. *)
    pure conststruct
  | IntLit il ->
    (* No better way to convert to LLVM integer than via strings :-(.
     * LLVM provides APIs that use APInt, but they aren't exposed via the OCaml API. *)
    pure @@ (match il with
    | Int32L i -> Llvm.const_int_of_string i32_ty (Int32.to_string i) 10
    | Int64L i -> Llvm.const_int_of_string (Llvm.i64_type ctx) (Int64.to_string i) 10
    | Int128L i -> Llvm.const_int_of_string (Llvm.integer_type ctx 128) (Stdint.Int128.to_string i) 10
    | Int256L i -> Llvm.const_int_of_string (Llvm.integer_type ctx 256) (Integer256.Int256.to_string i) 10
    )
  | UintLit uil ->
    pure @@ (match uil with
    (* LLVM uses i32 etc for unsinged integers as well. *)
    | Uint32L ui -> Llvm.const_int_of_string i32_ty (Stdint.Uint32.to_string ui) 10
    | Uint64L ui -> Llvm.const_int_of_string (Llvm.i64_type ctx) (Stdint.Uint64.to_string ui) 10
    | Uint128L ui -> Llvm.const_int_of_string (Llvm.integer_type ctx 128) (Stdint.Uint128.to_string ui) 10
    | Uint256L ui -> Llvm.const_int_of_string (Llvm.integer_type ctx 256) (Integer256.Uint256.to_string ui) 10
    )
  | BNum _bns -> pure @@ Llvm.const_pointer_null i32_ty
  | ByStrX _bs -> pure @@ Llvm.const_pointer_null i32_ty
  | ByStr _bs -> pure @@ Llvm.const_pointer_null i32_ty
  | Msg _sls -> pure @@ Llvm.const_pointer_null i32_ty
  | Map (_, _htbl) -> pure @@ Llvm.const_pointer_null i32_ty
  | ADTValue (_cname, _tls, _lits) -> pure @@ Llvm.const_pointer_null i32_ty
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
      } scilla_bytes;

      void scilla_string_print(scilla_bytes a)
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
  let%bind ll = genllvm_literal llcontext llmod l in
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
