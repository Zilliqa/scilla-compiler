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

(* Provide declarations for functions in the SRTL we want to call. *)

open Core_kernel
open! Int.Replace_polymorphic_compare
open Result.Let_syntax
open CodegenUtils

(* "void print_scilla_val (Typ*, void* )" *)
let decl_print_scilla_val llmod =
  let llctx = Llvm.module_context llmod in
  let%bind tydesrc_ty = TypeLLConv.TypeDescr.srtl_typ_ll llmod in
  scilla_function_decl llmod "_print_scilla_val" (Llvm.void_type llctx)
    [ Llvm.pointer_type tydesrc_ty; void_ptr_type llctx ]
