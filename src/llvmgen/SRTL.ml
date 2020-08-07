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
open TypeLLConv

type val_cast_type = Cast_None | Cast_VoidPtr

type call_arg_type =
  (* This is a regular Scilla value. Resolve it and pass as per convention. *)
  | CALLArg_ScillaVal of eannot Identifier.t
  (* Force passing this Scilla value (after resolving) via memory. *)
  | CALLArg_ScillaMemVal of eannot Identifier.t
  (* This is already resolved to an LLVM value. *)
  | CALLArg_LLVMVal of Llvm.llvalue

type call_ret_type =
  (* Returning via an "sret" parameter, possibly casted to "void*" *)
  | CALLRet_SRet of typ * val_cast_type
  (* Return by value *)
  | CALLRet_Val

let build_builtin_call_helper ?(execptr_b = true) llmod id_resolver builder
    bname callee args =
  let llctx = Llvm.module_context llmod in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  let%bind execptr =
    if execptr_b then
      let%bind ep = prepare_execptr llmod builder in
      pure [ ep ]
    else pure []
  in
  let%bind fty = ptr_element_type (Llvm.type_of callee) in
  (* Resolve all arguments. *)
  let%bind args_ll =
    (* A helper function to pass argument via the stack. *)
    let build_mem_call arg arg_ty =
      (* Create an alloca, write the value to it, and pass the address. *)
      let%bind argmem =
        build_alloca arg_ty
          (tempname (bname ^ "_" ^ Identifier.get_id arg))
          builder
      in
      let%bind arg' = id_resolver (Some builder) arg in
      let _ = Llvm.build_store arg' argmem builder in
      pure argmem
    in
    mapM args ~f:(function
      | CALLArg_ScillaVal arg ->
          let%bind arg_ty = id_typ_ll llmod arg in
          if can_pass_by_val dl arg_ty then
            let%bind arg' = id_resolver (Some builder) arg in
            pure arg'
          else
            let%bind arg' = build_mem_call arg arg_ty in
            pure arg'
      | CALLArg_ScillaMemVal arg ->
          let%bind arg_ty = id_typ_ll llmod arg in
          let%bind arg' =
            if Base.Poly.(Llvm.classify_type arg_ty = Llvm.TypeKind.Pointer)
            then
              (* This is already a pointer, just pass that by value. *)
              id_resolver (Some builder) arg
            else build_mem_call arg arg_ty
          in
          let arg'' =
            Llvm.build_pointercast arg' (void_ptr_type llctx)
              (tempname (Llvm.value_name arg'))
              builder
          in
          pure arg''
      | CALLArg_LLVMVal arg -> pure arg)
  in
  let callname =
    (* Calls to function returning void must not have a name. *)
    if Base.Poly.(Llvm.return_type fty <> Llvm.void_type llctx) then
      tempname (bname ^ "_call")
    else ""
  in
  pure
  @@ Llvm.build_call callee (Array.of_list (execptr @ args_ll)) callname builder

(* "void print_scilla_val (Typ*, void* )" *)
let decl_print_scilla_val llmod =
  let llctx = Llvm.module_context llmod in
  let%bind tydesrc_ty = TypeDescr.srtl_typ_ll llmod in
  scilla_function_decl llmod "_print_scilla_val" (Llvm.void_type llctx)
    [ Llvm.pointer_type tydesrc_ty; void_ptr_type llctx ]

let build_builtin_call llmod id_resolver td_resolver builder (b, brep) opds =
  let llctx = Llvm.module_context llmod in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  let bname = pp_builtin b in
  match b with
  | Builtin_add -> (
      (* "int(32/64/128) _add_int(32/64/128) ( Int(32/64/128), Int(32/64/128 )" *)
      (* "Int256* _add_int256 ( void* _execptr, Int256*, Int256* )"  *)
      match opds with
      | [ (Identifier.Ident (_, { ea_tp = Some sty; _ }) as opd1); opd2 ] -> (
          let opds' = [ CALLArg_ScillaVal opd1; CALLArg_ScillaVal opd2 ] in
          match sty with
          | PrimType (Int_typ bw as pt) | PrimType (Uint_typ bw as pt) -> (
              let fname = "_add_" ^ PrimType.pp_prim_typ pt in
              let%bind ty = genllvm_typ_fst llmod sty in
              match bw with
              | Bits32 | Bits64 | Bits128 ->
                  if can_pass_by_val dl ty then
                    let%bind decl =
                      scilla_function_decl llmod fname ty [ ty; ty ]
                    in
                    build_builtin_call_helper ~execptr_b:false llmod id_resolver
                      builder bname decl opds'
                  else
                    fail1
                      "GenLlvm: decl_add: internal error, cannot pass integer \
                       by value"
                      brep.ea_loc
              | Bits256 ->
                  let ty_ptr = Llvm.pointer_type ty in
                  let%bind decl =
                    scilla_function_decl llmod fname ty_ptr
                      [ void_ptr_type llctx; ty_ptr; ty_ptr ]
                  in
                  let%bind call =
                    build_builtin_call_helper llmod id_resolver builder bname
                      decl opds'
                  in
                  pure @@ Llvm.build_load call (tempname bname) builder )
          | _ -> fail1 "GenLlvm: decl_add: expected integer type" brep.ea_loc )
      | _ ->
          fail1 "GenLlvm: decl_builtins: Incorrect arguments for add"
            brep.ea_loc )
  | Builtin_eq -> (
      match opds with
      | Identifier.Ident (_, { ea_tp = Some (PrimType pt as sty); _ }) :: _ -> (
          let%bind ty = genllvm_typ_fst llmod sty in
          let%bind retty =
            genllvm_typ_fst llmod (ADT (Identifier.mk_loc_id "Bool", []))
          in
          match pt with
          | Bystrx_typ b ->
              (* Bool _eq_ByStrX ( void* _execptr, i32 X, void*, void* ) *)
              let fname = "_eq_ByStrX" in
              let%bind decl =
                scilla_function_decl llmod fname retty
                  [
                    void_ptr_type llctx;
                    Llvm.i32_type llctx;
                    void_ptr_type llctx;
                    void_ptr_type llctx;
                  ]
              in
              let i32_b = Llvm.const_int (Llvm.i32_type llctx) b in
              (* Unconditionally pass through memory. *)
              let opds' =
                List.map opds ~f:(fun opd -> CALLArg_ScillaMemVal opd)
              in
              build_builtin_call_helper llmod id_resolver builder bname decl
                (CALLArg_LLVMVal i32_b :: opds')
          | _ ->
              (* For all PrimTypes T, except ByStrX:
               *   Bool _eq_T ( void* _execptr, T, T )    when can_pass_by_val
               *   Bool _eq_T ( void* _execptr, T*, T* )  otherwise *)
              let fname = "_eq_" ^ pp_typ sty in
              let opds' = List.map opds ~f:(fun a -> CALLArg_ScillaVal a) in
              let ty_ptr = Llvm.pointer_type ty in
              let%bind decl =
                if can_pass_by_val dl ty then
                  scilla_function_decl llmod fname retty
                    [ void_ptr_type llctx; ty; ty ]
                else
                  scilla_function_decl llmod fname retty
                    [ void_ptr_type llctx; ty_ptr; ty_ptr ]
              in
              build_builtin_call_helper llmod id_resolver builder bname decl
                opds' )
      | _ ->
          fail1 "GenLlvm: decl_builtins: Invalid argument types for eq"
            brep.ea_loc )
  | Builtin_concat -> (
      match opds with
      | [
       ( Identifier.Ident (_, { ea_tp = Some (PrimType (Bystrx_typ bw1)); _ })
       as opd1 );
       ( Identifier.Ident (_, { ea_tp = Some (PrimType (Bystrx_typ bw2)); _ })
       as opd2 );
      ] ->
          (* void* _concat_ByStrX ( void* _execptr, int X1, void* bystr1, int X2, void* bystr2 ) *)
          let fname = "_concat_ByStrX" in
          let%bind decl =
            scilla_function_decl llmod fname (void_ptr_type llctx)
              [
                void_ptr_type llctx;
                Llvm.i32_type llctx;
                void_ptr_type llctx;
                Llvm.i32_type llctx;
                void_ptr_type llctx;
              ]
          in
          let x1 = Llvm.const_int (Llvm.i32_type llctx) bw1 in
          let x2 = Llvm.const_int (Llvm.i32_type llctx) bw2 in
          let%bind retty_ll_el =
            genllvm_typ_fst llmod (PrimType (Bystrx_typ (bw1 + bw2)))
          in
          let retty_ll = Llvm.pointer_type retty_ll_el in
          let%bind call =
            build_builtin_call_helper llmod id_resolver builder bname decl
              [
                CALLArg_LLVMVal x1;
                CALLArg_ScillaMemVal opd1;
                CALLArg_LLVMVal x2;
                CALLArg_ScillaMemVal opd2;
              ]
          in
          let retp =
            Llvm.build_pointercast call retty_ll (tempname bname) builder
          in
          pure @@ Llvm.build_load retp (tempname bname) builder
      | [
       Identifier.Ident (_, { ea_tp = Some (PrimType String_typ); _ });
       Identifier.Ident (_, { ea_tp = Some (PrimType String_typ); _ });
      ] ->
          (* String _concat_String ( void* _execptr, String s1, String s2 ) *)
          let fname = "_concat_String" in
          let%bind str_llty = genllvm_typ_fst llmod (PrimType String_typ) in
          let%bind decl =
            scilla_function_decl llmod fname str_llty
              [ void_ptr_type llctx; str_llty; str_llty ]
          in
          let opds' = List.map opds ~f:(fun opd -> CALLArg_ScillaVal opd) in
          build_builtin_call_helper llmod id_resolver builder bname decl opds'
      | _ ->
          fail1 "GenLlvm: decl_builtins: invalid operand types for concat"
            brep.ea_loc )
  | Builtin_to_nat -> (
      (*  # Nat* (void*, i32)
       *  # nat_value _to_nat (execptr, uint32_value)
       *)
      match opds with
      | [
       ( Identifier.Ident (_, { ea_tp = Some (PrimType (Uint_typ Bits32)); _ })
       as opd );
      ] ->
          let%bind nat_ty =
            genllvm_typ_fst llmod (ADT (Identifier.mk_loc_id "Nat", []))
          in
          let%bind uint32_ty =
            genllvm_typ_fst llmod TypeUtilities.PrimTypes.uint32_typ
          in
          let fname = "_to_nat" in
          let%bind decl =
            scilla_function_decl llmod fname nat_ty
              [ void_ptr_type llctx; uint32_ty ]
          in
          build_builtin_call_helper llmod id_resolver builder bname decl
            [ CALLArg_ScillaVal opd ]
      | _ ->
          fail1 "GenLlvm: decl_builtins: to_nat expects Uint32 argument."
            brep.ea_loc )
  | Builtin_to_bystr -> (
      match opds with
      | [
       ( Identifier.Ident (_, { ea_tp = Some (PrimType (Bystrx_typ b)); _ }) as
       opd );
      ] ->
          (* Bystr _to_bystr ( void* _execptr, int X, void* v ) *)
          let fname = "_to_bystr" in
          let%bind retty =
            genllvm_typ_fst llmod (PrimType PrimType.Bystr_typ)
          in
          let%bind decl =
            scilla_function_decl llmod fname retty
              [ void_ptr_type llctx; Llvm.i32_type llctx; void_ptr_type llctx ]
          in
          let i32_b = Llvm.const_int (Llvm.i32_type llctx) b in
          (* Unconditionally pass through memory. *)
          build_builtin_call_helper llmod id_resolver builder bname decl
            [ CALLArg_LLVMVal i32_b; CALLArg_ScillaMemVal opd ]
      | _ ->
          fail1 "GenLlvm: decl_builtins: to_bystr expected ByStrX argument"
            brep.ea_loc )
  | Builtin_sha256hash -> (
      (* ByStr32* sha256hash ( void* _execptr, TyDescr *td, void *v) *)
      let retty = PrimType (PrimType.Bystrx_typ 32) in
      let%bind bystr32_ty = genllvm_typ_fst llmod retty in
      match opds with
      | [ opd ] ->
          let fname = "_sha256hash" in
          let%bind decl =
            let%bind tdty = TypeDescr.srtl_typ_ll llmod in
            scilla_function_decl llmod fname
              (Llvm.pointer_type bystr32_ty)
              [
                void_ptr_type llctx; Llvm.pointer_type tdty; void_ptr_type llctx;
              ]
          in
          let%bind ty = id_typ opd in
          let%bind tydescr = td_resolver ty in
          let%bind call =
            build_builtin_call_helper llmod id_resolver builder bname decl
              [ CALLArg_LLVMVal tydescr; CALLArg_ScillaMemVal opd ]
          in
          pure @@ Llvm.build_load call (tempname bname) builder
      | _ ->
          fail1 "GenLlvm: decl_builtins: sha256hash expects single argument"
            brep.ea_loc )
  | Builtin_put -> (
      match opds with
      | [
       (Identifier.Ident (_, { ea_tp = Some (MapType (kt, vt)); _ }) as m_opd);
       k_opd;
       v_opd;
      ] ->
          (* void* _put ( void* _execptr, void* M : MapTyp, void* K : kt, void* V : vt ) *)
          let fname = "_put" in
          let mty = MapType (kt, vt) in
          let%bind tydesrc_ty = TypeDescr.srtl_typ_ll llmod in
          let%bind decl =
            scilla_function_decl llmod fname (void_ptr_type llctx)
              [
                (* _execptr *)
                void_ptr_type llctx;
                (* type descriptor *)
                Llvm.pointer_type tydesrc_ty;
                (* map *)
                void_ptr_type llctx;
                (* key *)
                void_ptr_type llctx;
                (* val *)
                void_ptr_type llctx;
              ]
          in
          let%bind tydescr = td_resolver mty in
          let%bind call =
            build_builtin_call_helper llmod id_resolver builder bname decl
              [
                CALLArg_LLVMVal tydescr;
                CALLArg_ScillaMemVal m_opd;
                CALLArg_ScillaMemVal k_opd;
                CALLArg_ScillaMemVal v_opd;
              ]
          in
          let%bind mt_ll = genllvm_typ_fst llmod mty in
          pure @@ Llvm.build_pointercast call mt_ll (tempname fname) builder
      | _ ->
          fail1 "GenLlvm: decl_builtins: Incorrect arguments to put" brep.ea_loc
      )
  | Builtin_get -> (
      match opds with
      | [
       (Identifier.Ident (_, { ea_tp = Some (MapType (kt, vt)); _ }) as m_opd);
       k_opd;
      ] ->
          (* void* _get ( void* _execptr, void* M : MapTyp, void* K : kt ) *)
          let fname = "_get" in
          let mty = MapType (kt, vt) in
          let%bind tydesrc_ty = TypeDescr.srtl_typ_ll llmod in
          let%bind decl =
            scilla_function_decl llmod fname (void_ptr_type llctx)
              [
                (* _execptr *)
                void_ptr_type llctx;
                (* type descriptor *)
                Llvm.pointer_type tydesrc_ty;
                (* map *)
                void_ptr_type llctx;
                (* key *)
                void_ptr_type llctx;
              ]
          in
          let%bind tydescr = td_resolver mty in
          let%bind call =
            build_builtin_call_helper llmod id_resolver builder bname decl
              [
                CALLArg_LLVMVal tydescr;
                CALLArg_ScillaMemVal m_opd;
                CALLArg_ScillaMemVal k_opd;
              ]
          in
          let%bind retty_ll =
            genllvm_typ_fst llmod (ADT (Identifier.mk_loc_id "Option", [ vt ]))
          in
          pure @@ Llvm.build_pointercast call retty_ll (tempname fname) builder
      | _ ->
          fail1 "GenLlvm: decl_builtins: Incorrect arguments to get" brep.ea_loc
      )
  | Builtin_contains -> (
      match opds with
      | [
       (Identifier.Ident (_, { ea_tp = Some (MapType (kt, vt)); _ }) as m_opd);
       k_opd;
      ] ->
          (* Bool _contains ( void* _execptr, void* M : MapTyp, void* K : kt ) *)
          let fname = "_contains" in
          let mty = MapType (kt, vt) in
          let%bind retty =
            genllvm_typ_fst llmod (ADT (Identifier.mk_loc_id "Bool", []))
          in
          let%bind tydesrc_ty = TypeDescr.srtl_typ_ll llmod in
          let%bind decl =
            scilla_function_decl llmod fname retty
              [
                (* _execptr *)
                void_ptr_type llctx;
                (* type descriptor *)
                Llvm.pointer_type tydesrc_ty;
                (* map *)
                void_ptr_type llctx;
                (* key *)
                void_ptr_type llctx;
              ]
          in
          let%bind tydescr = td_resolver mty in
          build_builtin_call_helper llmod id_resolver builder bname decl
            [
              CALLArg_LLVMVal tydescr;
              CALLArg_ScillaMemVal m_opd;
              CALLArg_ScillaMemVal k_opd;
            ]
      | _ ->
          fail1 "GenLlvm: decl_builtins: Incorrect arguments to contains"
            brep.ea_loc )
  | Builtin_remove -> (
      match opds with
      | [
       (Identifier.Ident (_, { ea_tp = Some (MapType (kt, vt)); _ }) as m_opd);
       k_opd;
      ] ->
          (* void* _remove ( void* _execptr, void* M : MapTyp, void* K : kt ) *)
          let fname = "_remove" in
          let mty = MapType (kt, vt) in
          let%bind tydesrc_ty = TypeDescr.srtl_typ_ll llmod in
          let%bind decl =
            scilla_function_decl llmod fname (void_ptr_type llctx)
              [
                (* _execptr *)
                void_ptr_type llctx;
                (* type descriptor *)
                Llvm.pointer_type tydesrc_ty;
                (* map *)
                void_ptr_type llctx;
                (* key *)
                void_ptr_type llctx;
              ]
          in
          let%bind tydescr = td_resolver mty in
          let%bind call =
            build_builtin_call_helper llmod id_resolver builder "" decl
              [
                CALLArg_LLVMVal tydescr;
                CALLArg_ScillaMemVal m_opd;
                CALLArg_ScillaMemVal k_opd;
              ]
          in
          let%bind mt_ll = genllvm_typ_fst llmod mty in
          pure @@ Llvm.build_pointercast call mt_ll (tempname fname) builder
      | _ ->
          fail1 "GenLlvm: decl_builtins: Incorrect arguments to remove"
            brep.ea_loc )
  | Builtin_size -> (
      match opds with
      | [ m_opd ] ->
          (* Uint32 _contains ( void* M : MapTyp ) *)
          let fname = "_size" in
          let retty = PrimType (Uint_typ Bits32) in
          let%bind retty_ll = genllvm_typ_fst llmod retty in
          let%bind decl =
            scilla_function_decl llmod fname retty_ll
              [ (* map *) void_ptr_type llctx ]
          in
          build_builtin_call_helper ~execptr_b:false llmod id_resolver builder
            bname decl
            [ CALLArg_ScillaMemVal m_opd ]
      | _ ->
          fail1 "GenLlvm: decl_builtins: Incorrect arguments to size"
            brep.ea_loc )
  | _ ->
      fail1
        (sprintf "GenLlvm: decl_builtins: %s not yet implimented" bname)
        brep.ea_loc

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
  let%bind tydesrc_ty = TypeDescr.srtl_typ_ll llmod in
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
  let%bind tydesrc_ty = TypeDescr.srtl_typ_ll llmod in
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

(* void send (void* execptr, Typ* tydescr, List (Message) *msgs) *)
let decl_send llmod =
  let llctx = Llvm.module_context llmod in
  let%bind tydesrc_ty = TypeDescr.srtl_typ_ll llmod in
  let%bind llty =
    genllvm_typ_fst llmod
      (ADT (Identifier.mk_loc_id "List", [ TypeUtilities.PrimTypes.msg_typ ]))
  in
  scilla_function_decl ~is_internal:false llmod "_send" (Llvm.void_type llctx)
    [ void_ptr_type llctx; Llvm.pointer_type tydesrc_ty; llty ]

(* void event (void* execptr, Typ* tydescr, void* msgobj) *)
let decl_event llmod =
  let llctx = Llvm.module_context llmod in
  let%bind tydesrc_ty = TypeDescr.srtl_typ_ll llmod in
  scilla_function_decl ~is_internal:false llmod "_event" (Llvm.void_type llctx)
    [ void_ptr_type llctx; Llvm.pointer_type tydesrc_ty; void_ptr_type llctx ]

(* void throw (void* execptr, Typ* tydescr, void* msgobj) *)
let decl_throw llmod =
  let llctx = Llvm.module_context llmod in
  let%bind tydesrc_ty = TypeDescr.srtl_typ_ll llmod in
  scilla_function_decl ~is_internal:false llmod "_throw" (Llvm.void_type llctx)
    [ void_ptr_type llctx; Llvm.pointer_type tydesrc_ty; void_ptr_type llctx ]

(* void accept (void* execptr) *)
let decl_accept llmod =
  let llctx = Llvm.module_context llmod in
  scilla_function_decl ~is_internal:false llmod "_accept" (Llvm.void_type llctx)
    [ void_ptr_type llctx ]

(* void* _new_empty_map (void* execptr) *)
let build_new_empty_map llmod builder mt =
  match mt with
  | MapType _ ->
      let%bind mt' = genllvm_typ_fst llmod mt in
      let llctx = Llvm.module_context llmod in
      let fname = "_new_empty_map" in
      let%bind decl =
        scilla_function_decl ~is_internal:false llmod fname
          (void_ptr_type llctx) [ void_ptr_type llctx ]
      in
      let dummy_resolver _ _ =
        fail0 "GenLlvm: build_new_empty_map: Nothing to resolve."
      in
      let%bind call =
        build_builtin_call_helper llmod dummy_resolver builder fname decl []
      in
      pure (Llvm.build_pointercast call mt' (tempname "Emp") builder)
  | _ -> fail0 "GenLlvm: build_new_empty_map: Cannot create non-map values."
