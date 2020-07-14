(*
  This file is part of scilla.

  Copyright (c) 2020 - present Zilliqa Research Pvt. Ltd.

  scilla is free software: you can redistribute it and/or modify it under the
  terms of the GNU General Public License as published by the Free Software
  Foundation, either version 3 of the License, or (at your option) any later
  version.

  scilla is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
  A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

  You should have received a copy of the GNU General Public License along with
*)

open Core_kernel
open! Int.Replace_polymorphic_compare
open Result.Let_syntax
open Scilla_base
module Literal = Literal.FlattenedLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open UncurriedSyntax.Uncurried_Syntax
open MonadUtil
open LoweringUtils

let define_global name llval llmod ~const ~unnamed =
  let g = Llvm.define_global name llval llmod in
  if unnamed then Llvm.set_unnamed_addr true g;
  if const then Llvm.set_global_constant true g;
  g

let declare_global llty name llmod ~const ~unnamed =
  let g = Llvm.declare_global llty name llmod in
  if unnamed then Llvm.set_unnamed_addr true g;
  if const then Llvm.set_global_constant true g;
  g

let lookup_global name llmod =
  match Llvm.lookup_global name llmod with
  | Some g -> pure g
  | None -> fail0 (sprintf "GenLlvm: lookup_global: %s not found." name)

let build_scilla_bytes llctx bytes_ty chars =
  let chars_ty = Llvm.type_of chars in
  let i8_type = Llvm.i8_type llctx in

  (* Check that chars is [len x i8]* *)
  if
    Base.Poly.(
      Llvm.classify_type chars_ty <> Llvm.TypeKind.Pointer
      || Llvm.classify_type (Llvm.element_type chars_ty) <> Llvm.TypeKind.Array
      || Llvm.element_type (Llvm.element_type chars_ty) <> i8_type)
  then fail0 "GenLlvm: build_scilla_bytes: Non byte-array type."
  else
    let len = Llvm.array_length (Llvm.element_type chars_ty) in
    (* The global constant "chars" is [len x i8]*, cast it to ( i8* ) *)
    let chars' = Llvm.const_pointercast chars (Llvm.pointer_type i8_type) in
    (* Build a scilla_bytes_ty structure { i8*, i32 } *)
    let struct_elms = [| chars'; Llvm.const_int (Llvm.i32_type llctx) len |] in
    let conststruct = Llvm.const_named_struct bytes_ty struct_elms in
    (* We now have a ConstantStruct that represents our String/Bystr literal. *)
    pure conststruct

let llsizeof dl ty =
  Int64.to_int_trunc (Llvm_target.DataLayout.size_in_bits ty dl) / 8

let can_pass_by_val dl ty =
  not
    ( Llvm.type_is_sized ty
    && Int64.compare
         (Llvm_target.DataLayout.size_in_bits ty dl)
         (Int64.of_int 128)
       > 0 )

let ptr_element_type ptr_llty =
  match Llvm.classify_type ptr_llty with
  | Llvm.TypeKind.Pointer -> pure @@ Llvm.element_type ptr_llty
  | _ -> fail0 "GenLlvm: internal error: expected pointer type"

let struct_element_types sty =
  match Llvm.classify_type sty with
  | Llvm.TypeKind.Struct -> pure (Llvm.struct_element_types sty)
  | _ -> fail0 "GenLlvm: internal error: expected struct type"

let scilla_function_decl ?(is_internal = false) llmod fname retty argtys =
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  let%bind _ =
    forallM (retty :: argtys) ~f:(fun ty ->
        if not (can_pass_by_val dl ty) then
          fail0 "Attempting to pass by value greater than 128 bytes"
        else pure ())
  in
  let ft = Llvm.function_type retty (Array.of_list argtys) in
  match Llvm.lookup_function fname llmod with
  | Some fdecl ->
      let%bind ft' = ptr_element_type (Llvm.type_of fdecl) in
      if Base.Poly.(ft' <> ft) then
        fail0
          (sprintf
             "GenLlvm: CodegenUtils: Type mismatch for function declaration \
              %s: %s vs %s"
             fname (Llvm.string_of_lltype ft)
             (Llvm.string_of_lltype ft'))
      else pure fdecl
  | None ->
      let f = Llvm.declare_function fname ft llmod in
      if is_internal then Llvm.set_linkage Llvm.Linkage.Internal f;
      pure f

let scilla_function_defn ?(is_internal = false) llmod fname retty argtys =
  let%bind f = scilla_function_decl ~is_internal llmod fname retty argtys in
  let _ = Llvm.append_block (Llvm.module_context llmod) "entry" f in
  pure f

let void_ptr_type ctx = Llvm.pointer_type (Llvm.i8_type ctx)

let void_ptr_nullptr ctx = Llvm.const_pointer_null (void_ptr_type ctx)

let new_block_before llctx name pos_block =
  Llvm.insert_block llctx name pos_block

let new_block_after llctx name pos_block =
  let n = Llvm.insert_block llctx name pos_block in
  let _ = Llvm.move_block_after pos_block n in
  n

let build_extractvalue agg index name b =
  let ty = Llvm.type_of agg in
  if
    Base.Poly.(Llvm.classify_type ty <> Llvm.TypeKind.Struct)
    || Array.length (Llvm.struct_element_types ty) <= index
  then fail0 "GenLlvm: build_extractvalue: internall error, invalid type"
  else pure @@ Llvm.build_extractvalue agg index name b

let build_insertvalue agg value index name b =
  let ty = Llvm.type_of agg in
  if
    Base.Poly.(Llvm.classify_type ty <> Llvm.TypeKind.Struct)
    || Array.length (Llvm.struct_element_types ty) <= index
  then fail0 "GenLlvm: build_extractvalue: internall error, invalid type"
  else pure @@ Llvm.build_insertvalue agg value index name b

type build_call_arg_type =
  | BCAT_ScillaVal of eannot Identifier.t
  | BCAT_LLVMVal of Llvm.llvalue

let build_call_all_scilla_args args =
  List.map args ~f:(fun arg -> BCAT_ScillaVal arg)

let prepare_execptr llmod builder =
  let%bind execptr = lookup_global "_execptr" llmod in
  let execptr' = Llvm.build_load execptr (tempname "to_nat_load") builder in
  pure execptr'
