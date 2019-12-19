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

open ErrorUtils
open Syntax
open UncurriedSyntax.Uncurried_Syntax
open ClosuredSyntax.CloCnvSyntax

(*
 * To avoid ABI complexities, we allow passing by value only
 * when the object size is not larger than two eight-bytes.
 * Otherwise, it needs to be passed in memory (via a pointer).
 * See https://stackoverflow.com/a/42413484/2128804
 *)
val can_pass_by_val : Llvm_target.DataLayout.t -> Llvm.lltype -> bool

(* Create a named struct with types from tyarr. *)
val named_struct_type : ?is_packed:bool -> Llvm.llmodule -> string -> Llvm.lltype array ->
  (Llvm.lltype, scilla_error list) result

(* Translate Scilla types to LLVM types.
 * In case of ADTs, the LLVM types for each constructor is returned
 * as the second component of the result. In all other cases, the
 * second component of the result is an empty list. *)
val genllvm_typ : Llvm.llmodule -> typ ->
  ((Llvm.lltype * (string * Llvm.lltype) list), scilla_error list) result

(* Returns only the first component of genllvm_typ. *)
val genllvm_typ_fst : Llvm.llmodule -> typ -> (Llvm.lltype, scilla_error list) result

(* Return a rep's annotated type. *)
val rep_typ : eannot -> (typ, scilla_error list) result

(* The annotated type of an identifier. *)
val id_typ : eannot ident -> (typ, scilla_error list) result

(* The annotated type of an identifier, translated to LLVM type. *)
val id_typ_ll : Llvm.llmodule -> eannot ident ->
  (Llvm.lltype, scilla_error list) result

(* Get the LLVM struct that holds an ADT's constructed object. Get its tag too.
 * Typically used on the output of genllvm_typ for ADT type. *)
val get_ctr_struct : (string * Llvm.lltype) list -> string ->
(Llvm.lltype * int, scilla_error list) result

(* A pointer's element type. *)
val ptr_element_type : Llvm.lltype -> (Llvm.lltype, scilla_error list) result

(* The type of each component of a struct. *)
val struct_element_types : Llvm.lltype -> (Llvm.lltype array, scilla_error list) result

(* The ( void* ) type *)
val void_ptr_type : Llvm.llcontext -> Llvm.lltype

(* Describe each Scilla type as static data in the LLVM-IR module.
 * The description records conform to ScillaTypes definition in SRTL. *)
module TypeDescr : sig

  type typ_descr

  (* Generate LLVM type descriptor for all types in "stmts"
   * and return a dictionary to resolve each Scilla type to the
   * LLVM value that describes it *)
  val generate_type_descr_stmts_wrapper : Llvm.llmodule ->
    clorec list -> stmt_annot list -> (typ_descr, scilla_error list) result

  (* Generate LLVM type descriptor for all types in the contract module
   * and return a dictionary to resolve each Scilla type to the
   * LLVM value that describes it *)
  val generate_type_descr_cmod : Llvm.llmodule ->
    clorec list -> cmodule -> (typ_descr, scilla_error list) result

  (* For a Scilla type, return a pointer to it's type description in LLVM. *)
  val resolve_typdescr : typ_descr -> typ -> (Llvm.llvalue, scilla_error list) result

end
