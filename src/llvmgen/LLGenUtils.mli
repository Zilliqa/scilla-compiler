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

open Scilla_base
module Literal = Literal.GlobalLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open ErrorUtils

(* Build an (unnamed) (constant) global value. *)
val define_global :
  string ->
  Llvm.llvalue ->
  Llvm.llmodule ->
  const:bool ->
  unnamed:bool ->
  Llvm.llvalue

(* Declare an (unnamed) (constant) global. *)
val declare_global :
  Llvm.lltype ->
  string ->
  Llvm.llmodule ->
  const:bool ->
  unnamed:bool ->
  Llvm.llvalue

(* Llvm.lookup_global with error monad wrapper. *)
val lookup_global :
  string -> Llvm.llmodule -> (Llvm.llvalue, scilla_error list) result

(* Build a global scilla_bytes_ty value, given a byte array. *)
(* The bytes_ty arguments is used to distinguish different scilla_bytes_ty
 * which have the same structure but a different name. *)
val build_scilla_bytes :
  Llvm.llcontext ->
  Llvm.lltype ->
  Llvm.llvalue ->
  (Llvm.llvalue, scilla_error list) result

(* Wrapper around build_scilla_bytes that creates a character array
 * of strval and passes it on to build_scilla_bytes. *)
val define_string_value :
  Llvm.llmodule ->
  Llvm.lltype ->
  name:string ->
  strval:string ->
  (Llvm.llvalue, ErrorUtils.scilla_error list) result

(* Size of an LLVM type in bytes. *)
val llsizeof : Llvm_target.DataLayout.t -> Llvm.lltype -> int

(*
 * To avoid ABI complexities, we allow passing by value only
 * when the object size is not larger than two eight-bytes.
 * Otherwise, it needs to be passed in memory (via a pointer).
 * See https://stackoverflow.com/a/42413484/2128804
 *)
val can_pass_by_val : Llvm_target.DataLayout.t -> Llvm.lltype -> bool

(* A pointer's element type. *)
val ptr_element_type : Llvm.lltype -> (Llvm.lltype, scilla_error list) result

(* The type of each component of a struct. *)
val struct_element_types :
  Llvm.lltype -> (Llvm.lltype array, scilla_error list) result

(* Get a function declaration of the given type signature.
 * Fails if 
  - the return type or arg types cannot be passed by value.
  - Function declaration already exists but with different signature.
 * The parameter "is_internal" sets the Llvm.Linkage.Internal attribute.
 *)
val scilla_function_decl :
  ?is_internal:bool ->
  Llvm.llmodule ->
  string ->
  Llvm.lltype ->
  Llvm.lltype list ->
  (Llvm.llvalue, scilla_error list) result

(* Declares a function using scilla_function_decl and adds entry block *)
val scilla_function_defn :
  ?is_internal:bool ->
  Llvm.llmodule ->
  string ->
  Llvm.lltype ->
  Llvm.lltype list ->
  (Llvm.llvalue, scilla_error list) result

(* The ( void* ) type *)
val void_ptr_type : Llvm.llcontext -> Llvm.lltype

(* ( void* ) nullptr *)
val void_ptr_nullptr : Llvm.llcontext -> Llvm.llvalue

(* Create a new block before pos_block. *)
val new_block_before :
  Llvm.llcontext -> string -> Llvm.llbasicblock -> Llvm.llbasicblock

(* Create a new block after pos_block. *)
val new_block_after :
  Llvm.llcontext -> string -> Llvm.llbasicblock -> Llvm.llbasicblock

(* Type safe version of Llvm.build_extractvalue *)
val build_extractvalue :
  Llvm.llvalue ->
  int ->
  string ->
  Llvm.llbuilder ->
  (Llvm.llvalue, scilla_error list) result

(* Type safe version of Llvm.build_insertvalue *)
val build_insertvalue :
  Llvm.llvalue ->
  Llvm.llvalue ->
  int ->
  string ->
  Llvm.llbuilder ->
  (Llvm.llvalue, scilla_error list) result

(* Asserts that we don't build a void alloca. *)
val build_alloca :
  Llvm.lltype ->
  string ->
  Llvm.llbuilder ->
  (Llvm.llvalue, scilla_error list) result

(* Prepare _execptr for use by loading the global. *)
val prepare_execptr :
  Llvm.llmodule -> Llvm.llbuilder -> (Llvm.llvalue, scilla_error list) result

(* An assert for use in monadic code *)
val ensure :
  ?loc:ErrorUtils.loc ->
  bool ->
  string ->
  (unit, ErrorUtils.scilla_error list) result

val decl_uint64_min : Llvm.llmodule -> (Llvm.llvalue, scilla_error list) result
val decl_f64_log : Llvm.llmodule -> (Llvm.llvalue, scilla_error list) result
val decl_f64_pow : Llvm.llmodule -> (Llvm.llvalue, scilla_error list) result
val decl_i256_bswap : Llvm.llmodule -> (Llvm.llvalue, scilla_error list) result
