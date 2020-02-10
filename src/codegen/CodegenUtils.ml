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

open Core_kernel
open! Int.Replace_polymorphic_compare
open Result.Let_syntax
open MonadUtil
open Syntax

let newname_prefix_char = "$"

let newname_creator () =
  let name_counter = ref 0 in
  fun base rep ->
    (* system generated names will begin with "$" for uniqueness. *)
    let n = newname_prefix_char ^ base ^ "_" ^ Int.to_string !name_counter in
    name_counter := !name_counter + 1;
    asIdL n rep

let global_name_counter = ref 0

let global_newnamer
    (* Cannot just call newname_creator() because of OCaml's weak type limitation. *)
      base rep =
  (* system generated names will begin with "$" for uniqueness. *)
  let n =
    newname_prefix_char ^ base ^ "_" ^ Int.to_string !global_name_counter
  in
  global_name_counter := !global_name_counter + 1;
  asIdL n rep

let tempname base =
  get_id (global_newnamer base ExplicitAnnotationSyntax.empty_annot)

let define_unnamed_const_global name llval llmod =
  let g = Llvm.define_global name llval llmod in
  let _ = Llvm.set_unnamed_addr true g in
  let _ = Llvm.set_global_constant true g in
  g

let declare_unnamed_const_global llty name llmod =
  let g = Llvm.declare_global llty name llmod in
  let _ = Llvm.set_unnamed_addr true g in
  let _ = Llvm.set_global_constant true g in
  g

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

let can_pass_by_val dl ty =
  not
    ( Llvm.type_is_sized ty
    && Int64.compare
         (Llvm_target.DataLayout.size_in_bits ty dl)
         (Int64.of_int 128)
       > 0 )

let scilla_function_decl ?(is_internal = false) llmod fname retty argtys =
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  let%bind _ =
    iterM (retty :: argtys) ~f:(fun ty ->
        if not (can_pass_by_val dl ty) then
          fail0 "Attempting to pass by value greater than 128 bytes"
        else pure ())
  in
  match Llvm.lookup_function fname llmod with
  | Some ft ->
      if
        Base.Poly.(
          Llvm.type_of ft <> Llvm.function_type retty (Array.of_list argtys))
      then
        fail0
          "GenLlvm: CodegenUtils: function declaration already exists with \
           different type"
      else pure ft
  | None ->
      let ft = Llvm.function_type retty (Array.of_list argtys) in
      let f = Llvm.declare_function fname ft llmod in
      if is_internal then Llvm.set_linkage Llvm.Linkage.Internal f;
      pure f

let void_ptr_type ctx = Llvm.pointer_type (Llvm.i8_type ctx)

let void_ptr_nullptr ctx = Llvm.const_pointer_null (void_ptr_type ctx)

let new_block_before llctx name pos_block =
  Llvm.insert_block llctx name pos_block

let new_block_after llctx name pos_block =
  let n = Llvm.insert_block llctx name pos_block in
  let _ = Llvm.move_block_after pos_block n in
  n
