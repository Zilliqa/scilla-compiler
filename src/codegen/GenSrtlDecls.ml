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
open Syntax
open UncurriedSyntax.Uncurried_Syntax
open MonadUtil

(* "void print_scilla_val (Typ*, void* )" *)
let decl_print_scilla_val llmod =
  let llctx = Llvm.module_context llmod in
  let%bind tydesrc_ty = TypeLLConv.TypeDescr.srtl_typ_ll llmod in
  scilla_function_decl llmod "_print_scilla_val" (Llvm.void_type llctx)
    [ Llvm.pointer_type tydesrc_ty; void_ptr_type llctx ]

(* Add integers *)
(* "int(32/64/128) _add_int(32/64/128) ( Int(32/64/128), Int(32/64/128 )" *)
(* "void _add_int256 ( Int256*, Int256*, Int256* )"  *)
let decl_add llmod sty =
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  let llctx = Llvm.module_context llmod in
  match sty with
  | PrimType (Int_typ bw as pt) | PrimType (Uint_typ bw as pt) -> (
      let fname = "_add_" ^ pp_prim_typ pt in
      let%bind ty = TypeLLConv.genllvm_typ_fst llmod sty in
      match bw with
      | Bits32 | Bits64 | Bits128 ->
          if can_pass_by_val dl ty then
            scilla_function_decl llmod fname ty [ ty; ty ]
          else
            fail0
              "GenLlvm: decl_add: internal error, cannot pass integer by value"
      | Bits256 ->
          let ty_ptr = Llvm.pointer_type ty in
          scilla_function_decl llmod fname (Llvm.void_type llctx)
            [ ty_ptr; ty_ptr; ty_ptr ] )
  | _ -> fail0 "GenLlvm: decl_add: expected integer type"

let decl_builtins llmod b opds =
  match b with
  | Builtin_add -> (
      match opds with
      | Ident (_, { ea_tp = Some ty; _ }) :: _ -> decl_add llmod ty
      | _ ->
          fail0
            "GenLlvm: decl_builtins: unable to determine operand type for add" )
  | _ -> fail0 "GenLlvm: decl_builtins: not yet implimented"