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
open UncurriedSyntax.Uncurried_Syntax
open ClosuredSyntax.CloCnvSyntax

(* Create a named struct with types from tyarr. *)
(* In contrast to Llvm.named_struct_type, it checks if type already exists. *)
val named_struct_type :
  ?is_packed:bool ->
  ?is_opaque:bool ->
  Llvm.llmodule ->
  string ->
  Llvm.lltype array ->
  (Llvm.lltype, scilla_error list) result

(* Translate Scilla types to LLVM types.
 * In case of ADTs, the LLVM types for each constructor is returned
 * as the second component of the result. In all other cases, the
 * second component of the result is an empty list. *)
val genllvm_typ :
  Llvm.llmodule ->
  typ ->
  ( Llvm.lltype * (Identifier.Name.t * Llvm.lltype) list,
    scilla_error list )
  result

(* Returns only the first component of genllvm_typ. *)
val genllvm_typ_fst :
  Llvm.llmodule -> typ -> (Llvm.lltype, scilla_error list) result

(* Return a rep's annotated type. *)
val rep_typ : eannot -> (typ, scilla_error list) result

(* The annotated type of an identifier. *)
val id_typ : eannot Identifier.t -> (typ, scilla_error list) result

(* The annotated type of an identifier, translated to LLVM type. *)
val id_typ_ll :
  Llvm.llmodule ->
  eannot Identifier.t ->
  (Llvm.lltype, scilla_error list) result

val is_boxed_typ : typ -> bool

(* Get the LLVM struct that holds an ADT's constructed object. Get its tag too.
 * Typically used on the output of genllvm_typ for ADT type. *)
val get_ctr_struct :
  (Identifier.Name.t * Llvm.lltype) list ->
  Identifier.Name.t ->
  (Llvm.lltype * int, scilla_error list) result

(* Describe each Scilla type as static data in the LLVM-IR module.
 * The description records conform to ScillaTypes definition in SRTL. *)
module TypeDescr : sig
  type typ_descr

  (* LLVM type for struct Typ in SRTL. *)
  (* The union in Typ is represented as a void* *)
  val srtl_typ_ll : Llvm.llmodule -> (Llvm.lltype, scilla_error list) result

  (* Generate LLVM type descriptor for all types in "stmts"
   * and return a dictionary to resolve each Scilla type to the
   * LLVM value that describes it *)
  val generate_type_descr_stmts_wrapper :
    Llvm.llmodule ->
    clorec list ->
    stmt_annot list ->
    (typ_descr, scilla_error list) result

  (* Generate LLVM type descriptor for all types in the contract module
   * and return a dictionary to resolve each Scilla type to the
   * LLVM value that describes it *)
  val generate_type_descr_cmod :
    Llvm.llmodule ->
    clorec list ->
    cmodule ->
    (typ_descr, scilla_error list) result

  (* For a Scilla type, return a pointer to it's type description in LLVM. *)
  val resolve_typdescr :
    typ_descr -> typ -> (Llvm.llvalue, scilla_error list) result

  (* Insert into module two globals:
   * 1. Am array with pointers to all typedescrs we have. 
   * 2. An i32 containing the length of this array. *)
  val build_tydescr_table :
    Llvm.llmodule ->
    global_array_name:string ->
    global_array_length_name:string ->
    typ_descr ->
    (Llvm.llvalue * Llvm.llvalue, scilla_error list) result
end

(* Enumerate all (closed) types used as arguments in a type application. *)
module EnumTAppArgs : sig
  type typ_idx_map

  val enumerate_tapp_args_stmts_wrapper :
    clorec list -> stmt_annot list -> typ_idx_map

  val enumerate_tapp_args_cmod : clorec list -> cmodule -> typ_idx_map

  val lookup_typ_idx : typ_idx_map -> typ -> (int, scilla_error list) result

  val size : typ_idx_map -> int
end
