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
open Scilla_base
module PrimType = Type.PrimType
module Literal = Literal.FlattenedLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open LoweringUtils
open LLGenUtils
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
      let fname = "_add_" ^ PrimType.pp_prim_typ pt in
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

let decl_builtins builder llmod b opds =
  let llctx = Llvm.module_context llmod in
  match b with
  | Builtin_add -> (
      match opds with
      | Identifier.Ident (_, { ea_tp = Some ty; _ }) :: _ ->
          let%bind decl = decl_add llmod ty in
          pure (decl, build_call_all_scilla_args opds)
      | _ ->
          fail0
            "GenLlvm: decl_builtins: unable to determine operand type for add" )
  | Builtin_to_nat -> (
      (* # Nat* (void*, i32)
         # nat_value _to_nat (execptr, uint32_value)
      *)
      match opds with
      | Identifier.Ident (_, { ea_tp = Some (PrimType (Uint_typ Bits32)); _ })
        :: _ ->
          let%bind nat_ty =
            TypeLLConv.genllvm_typ_fst llmod
              (ADT (Identifier.mk_loc_id "Nat", []))
          in
          let%bind uint32_ty =
            TypeLLConv.genllvm_typ_fst llmod TypeUtilities.PrimTypes.uint32_typ
          in
          let%bind decl =
            scilla_function_decl llmod "_to_nat" nat_ty
              [ void_ptr_type llctx; uint32_ty ]
          in
          (* This builtin takes _execptr as the first argument. *)
          let%bind execptr = lookup_global "_execptr" llmod in
          let execptr' =
            Llvm.build_load execptr (tempname "to_nat_load") builder
          in
          pure (decl, BCAT_LLVMVal execptr' :: build_call_all_scilla_args opds)
      | _ -> fail0 "GenLlvm: decl_builtins: to_nat expects Uint32 argument." )
  | _ -> fail0 "GenLlvm: decl_builtins: not yet implimented"

(* Build an function signature for fetching state fields.
 *   # void* ( void*, const char *, Typ*, i32, i8*, i32 )
 *   # fetched_val ( execptr field_name field_tydescr num_indices indices fetchval )
 * execptr points to the JIT execution instance.
 * indices points to a memory buffer containing the indices
 * with num_indices conveying the number of indices being passed.
 * The type of each index is derivable (by SRTL) from the field's type.
 * The returned value is always a pointer. For boxed types, this is the
 * boxing pointer. Otherwise, the caller must load from this pointer.
 * fetchval indicates if the actual value is needed or we just want
 * to know if it exists. *)
let decl_fetch_field llmod =
  let llctx = Llvm.module_context llmod in
  let%bind tydesrc_ty = TypeLLConv.TypeDescr.srtl_typ_ll llmod in
  scilla_function_decl ~is_internal:false llmod "_fetch_field"
    (void_ptr_type llctx)
    [
      void_ptr_type llctx;
      Llvm.pointer_type (Llvm.i8_type llctx);
      Llvm.pointer_type tydesrc_ty;
      Llvm.i32_type llctx;
      Llvm.pointer_type (Llvm.i8_type llctx);
      Llvm.i32_type llctx;
    ]

(* Build an function signature for updating state fields.
 *   # void ( void*, const char *, Typ*, i32, i8*, void* )
 *   # void ( execptr field_name field_tydescr num_indices indices value )
 * execptr points to the JIT execution instance.
 * indices points to a memory buffer containing the indices
 * with num_indices conveying the number of indices being passed.
 * The type of each index is derivable (by SRTL) from the field's type.
 * The "value" to be updated is always a pointer. For boxed types, this is
 * the boxing pointer. Otherwise, the callee will load from this pointer.
 * "value" can be NULL and this indicates (in case of map updates) that
 * the key is to be deleted. The type of "value" is derivable too. *)
let decl_update_field llmod =
  let llctx = Llvm.module_context llmod in
  let%bind tydesrc_ty = TypeLLConv.TypeDescr.srtl_typ_ll llmod in
  scilla_function_decl ~is_internal:false llmod "_update_field"
    (Llvm.void_type llctx)
    [
      void_ptr_type llctx;
      Llvm.pointer_type (Llvm.i8_type llctx);
      Llvm.pointer_type tydesrc_ty;
      Llvm.i32_type llctx;
      Llvm.pointer_type (Llvm.i8_type llctx);
      void_ptr_type llctx;
    ]

(* salloc: Same as malloc, but takes in execptr as first parameter *)
(* void* salloc ( void*, size_t s ) *)
let decl_salloc llmod =
  let llctx = Llvm.module_context llmod in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  scilla_function_decl ~is_internal:false llmod "_salloc" (void_ptr_type llctx)
    [ void_ptr_type llctx; Llvm_target.DataLayout.intptr_type llctx dl ]

(* Scilla memory allocator.
 * Same as malloc, but takes in execid as first parameter. *)
let build_salloc llty name builder =
  let llmod =
    Llvm.global_parent (Llvm.block_parent (Llvm.insertion_block builder))
  in
  let llctx = Llvm.module_context llmod in
  let%bind execptr = lookup_global "_execptr" llmod in
  let execptr' = Llvm.build_load execptr (name ^ "_load") builder in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  let size = llsizeof dl llty in
  let intptr_ty = Llvm_target.DataLayout.intptr_type llctx dl in
  let%bind salloc = decl_salloc llmod in
  let mem =
    Llvm.build_call salloc
      [| execptr'; Llvm.const_int intptr_ty size |]
      (name ^ "_salloc") builder
  in
  (* cast mem to llty* *)
  pure (Llvm.build_pointercast mem (Llvm.pointer_type llty) name builder)

(* Allocate an array of llty. Returns a value whose type is pointer to llty. *)
let build_array_salloc llty len name builder =
  let%bind al =
    build_salloc (Llvm.array_type llty len) (name ^ "_salloc") builder
  in
  pure @@ Llvm.build_pointercast al (Llvm.pointer_type llty) name builder
