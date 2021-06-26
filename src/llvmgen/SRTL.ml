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
open Scilla_crypto
module PrimType = Type.PrimType
module Literal = Literal.GlobalLiteral
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

(* All purpose utility to call functions in SRTL. "retty" is an extra arg
 * and not taken from the signature of "callee" because some SRTL functions
 * may return different typed values. "retty" is the final expected type. *)
let build_builtin_call_helper ~execptr_b dbg_opt llmod id_resolver builder bname
    callee args retty =
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
          (tempname (bname ^ "_" ^ Identifier.as_string arg))
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
  let call =
    Llvm.build_call callee (Array.of_list (execptr @ args_ll)) callname builder
  in
  let%bind () =
    match dbg_opt with
    | Some (discope, loc) -> DebugInfo.set_inst_loc llctx discope call loc
    | None -> pure ()
  in
  let call_retty_ll = Llvm.type_of call in
  let%bind retty_ll = genllvm_typ_fst llmod retty in
  let%bind boxed_typ = is_boxed_typ retty in
  if boxed_typ then
    (* Ensure that the LLVM type corresponding to retty is a pointer.
     * and that the call also returned a pointer. *)
    let%bind () =
      ensure
        Base.Poly.(
          Llvm.classify_type retty_ll = Llvm.TypeKind.Pointer
          && Llvm.classify_type call_retty_ll = Llvm.TypeKind.Pointer)
        "GenLlvm: build_builtin_call_helper: internal error: Inconsistency in \
         boxed return type."
    in
    pure @@ Llvm.build_pointercast call retty_ll (tempname bname) builder
  else if Base.Poly.(Llvm.classify_type call_retty_ll = Llvm.TypeKind.Pointer)
  then
    (* If the SRTL function returned a pointer, we need to load from it. *)
    let%bind () =
      (* I can't think of any type that is classifed as unboxed but
       * represented with a pointer. If there is one, remove this assert. *)
      ensure
        Base.Poly.(Llvm.classify_type retty_ll <> Llvm.TypeKind.Pointer)
        "GenLlvm: build_builtin_call_helper: internal error: Non-boxed type \
         shouldn't be a pointer"
    in
    let ptr =
      Llvm.build_pointercast call
        (Llvm.pointer_type retty_ll)
        (tempname bname) builder
    in
    pure @@ Llvm.build_load ptr (tempname bname) builder
  else
    (* Unboxed type and the SRTL function returned the value we want. *)
    let%bind () =
      ensure
        (* We check for sizeof of return types to be equal rather than the types
         * themselves because if retty needs to be an LLVM type rather than
         * deriving from Scilla, the caller has no way to express that, so
         * it will just spoof with some compatible (=sizeof) type.
         * Example: build_literal_cost etc. *)
        (Base.Poly.(Llvm.void_type llctx = retty_ll)
        || llsizeof dl retty_ll = llsizeof dl call_retty_ll
           && can_pass_by_val dl retty_ll)
        ("GenLlvm: build_builtin_call_helper: Invalid return of non-boxed \
          type: " ^ pp_typ retty)
    in
    pure call

(* "void print_scilla_val (void *_execptr, Typ*, void* )" *)
let decl_print_scilla_val llmod =
  let llctx = Llvm.module_context llmod in
  let%bind tydesrc_ty = TypeDescr.srtl_typ_ll llmod in
  scilla_function_decl llmod "_print_scilla_val" (Llvm.void_type llctx)
    [ void_ptr_type llctx; Llvm.pointer_type tydesrc_ty; void_ptr_type llctx ]

let get_bool_types llmod =
  let ty =
    ADT (Identifier.mk_loc_id (Identifier.Name.parse_simple_name "Bool"), [])
  in
  let%bind ty_ll = genllvm_typ_fst llmod ty in
  pure (ty, ty_ll)

let get_option_type ty =
  ADT (Identifier.mk_loc_id (Identifier.Name.parse_simple_name "Option"), [ ty ])

let build_builtin_call llmod discope id_resolver td_resolver builder (b, brep)
    opds =
  let llctx = Llvm.module_context llmod in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  let bname = pp_builtin b in
  let build_builtin_call_helper' ?(execptr_b = true) =
    build_builtin_call_helper ~execptr_b
      (Some (discope, brep.ea_loc))
      llmod id_resolver builder bname
  in
  (* For the sake of code generation, Addresses are ByStr20 values. *)
  let is_bystrx_compatible_typ = function
    | PrimType (Bystrx_typ _) | Address _ -> true
    | _ -> false
  in
  (* For a bystrx compatible type, get it's width. *)
  let bystrx_compatible_width = function
    | PrimType (Bystrx_typ b) -> pure b
    | Address _ -> pure 20
    | _ ->
        fail0
          "Internal error: bystrx_compatible_width: Expected bystrx compatible \
           type."
  in
  match b with
  | Builtin_add | Builtin_sub | Builtin_mul | Builtin_div | Builtin_rem -> (
      (* "int(32/64/128) _op_int(32/64/128) ( Int(32/64/128), Int(32/64/128 )" *)
      (* "Int256* _op_int256 ( void* _execptr, Int256*, Int256* )"  *)
      match opds with
      | [ (Identifier.Ident (_, { ea_tp = Some sty; _ }) as opd1); opd2 ] -> (
          let opds' = [ CALLArg_ScillaVal opd1; CALLArg_ScillaVal opd2 ] in
          match sty with
          | PrimType (Int_typ bw as pt) | PrimType (Uint_typ bw as pt) -> (
              let fname = "_" ^ pp_builtin b ^ "_" ^ PrimType.pp_prim_typ pt in
              let%bind ty = genllvm_typ_fst llmod sty in
              match bw with
              | Bits32 | Bits64 | Bits128 ->
                  let%bind () =
                    ensure (can_pass_by_val dl ty)
                      "GenLlvm: decl_add: internal error, cannot pass integer \
                       by value"
                      ~loc:brep.ea_loc
                  in
                  let%bind decl =
                    scilla_function_decl llmod fname ty [ ty; ty ]
                  in
                  build_builtin_call_helper' ~execptr_b:false decl opds' sty
              | Bits256 ->
                  let ty_ptr = Llvm.pointer_type ty in
                  let%bind decl =
                    scilla_function_decl llmod fname ty_ptr
                      [ void_ptr_type llctx; ty_ptr; ty_ptr ]
                  in
                  build_builtin_call_helper' decl opds' sty)
          | _ -> fail1 "GenLlvm: decl_add: expected integer type" brep.ea_loc)
      | _ ->
          fail1 "GenLlvm: decl_builtins: Incorrect arguments for add"
            brep.ea_loc)
  | Builtin_lt -> (
      (* "Bool _lt_int(32/64/128)
            ( void* _execptr, Int(32/64/128), Int(32/64/128 )" *)
      (* "Bool _lt_int256 ( void* _execptr, Int256*, Int256* )"  *)
      match opds with
      | [ (Identifier.Ident (_, { ea_tp = Some sty; _ }) as opd1); opd2 ] -> (
          let%bind retty, retty_ll = get_bool_types llmod in
          let opds' = [ CALLArg_ScillaVal opd1; CALLArg_ScillaVal opd2 ] in
          match sty with
          | PrimType (Int_typ bw as pt) | PrimType (Uint_typ bw as pt) -> (
              let fname = "_lt_" ^ PrimType.pp_prim_typ pt in
              let%bind ty = genllvm_typ_fst llmod sty in
              match bw with
              | Bits32 | Bits64 | Bits128 ->
                  let%bind () =
                    ensure (can_pass_by_val dl ty)
                      "GenLlvm: decl_lt: internal error, cannot pass integer \
                       by value"
                      ~loc:brep.ea_loc
                  in
                  let%bind decl =
                    scilla_function_decl llmod fname retty_ll
                      [ void_ptr_type llctx; ty; ty ]
                  in
                  build_builtin_call_helper' decl opds' retty
              | Bits256 ->
                  let ty_ptr = Llvm.pointer_type ty in
                  let%bind decl =
                    scilla_function_decl llmod fname retty_ll
                      [ void_ptr_type llctx; ty_ptr; ty_ptr ]
                  in
                  build_builtin_call_helper' decl opds' retty)
          | _ -> fail1 "GenLlvm: decl_lt: expected integer type" brep.ea_loc)
      | _ ->
          fail1 "GenLlvm: decl_builtins: Incorrect arguments for lt" brep.ea_loc
      )
  | Builtin_eq -> (
      match opds with
      | Identifier.Ident (_, { ea_tp = Some (PrimType _ as sty); _ }) :: _
      | Identifier.Ident (_, { ea_tp = Some (Address _ as sty); _ }) :: _ ->
          let%bind ty = genllvm_typ_fst llmod sty in
          let%bind retty, retty_ll = get_bool_types llmod in
          if is_bystrx_compatible_typ sty then
            let%bind b = bystrx_compatible_width sty in
            (* Bool _eq_ByStrX ( void* _execptr, i32 X, void*, void* ) *)
            let fname = "_eq_ByStrX" in
            let%bind decl =
              scilla_function_decl llmod fname retty_ll
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
            build_builtin_call_helper' decl
              (CALLArg_LLVMVal i32_b :: opds')
              retty
          else
            (* For all PrimTypes T, except ByStrX:
             *   Bool _eq_T ( void* _execptr, T, T )    when can_pass_by_val
             *   Bool _eq_T ( void* _execptr, T*, T* )  otherwise *)
            let fname = "_eq_" ^ pp_typ sty in
            let opds' = List.map opds ~f:(fun a -> CALLArg_ScillaVal a) in
            let ty_ptr = Llvm.pointer_type ty in
            let%bind decl =
              if can_pass_by_val dl ty then
                scilla_function_decl llmod fname retty_ll
                  [ void_ptr_type llctx; ty; ty ]
              else
                scilla_function_decl llmod fname retty_ll
                  [ void_ptr_type llctx; ty_ptr; ty_ptr ]
            in
            build_builtin_call_helper' decl opds' retty
      | _ ->
          fail1 "GenLlvm: decl_builtins: Invalid argument types for eq"
            brep.ea_loc)
  | Builtin_concat -> (
      match opds with
      | [
       (Identifier.Ident (_, { ea_tp = Some sty1; _ }) as opd1);
       (Identifier.Ident (_, { ea_tp = Some sty2; _ }) as opd2);
      ]
        when is_bystrx_compatible_typ sty1 && is_bystrx_compatible_typ sty2 ->
          let%bind bw1 = bystrx_compatible_width sty1 in
          let%bind bw2 = bystrx_compatible_width sty2 in
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
          let retty = PrimType (Bystrx_typ (bw1 + bw2)) in
          build_builtin_call_helper' decl
            [
              CALLArg_LLVMVal x1;
              CALLArg_ScillaMemVal opd1;
              CALLArg_LLVMVal x2;
              CALLArg_ScillaMemVal opd2;
            ]
            retty
      | [
          Identifier.Ident (_, { ea_tp = Some (PrimType String_typ as tp); _ });
          Identifier.Ident (_, { ea_tp = Some (PrimType String_typ); _ });
        ]
      | [
          Identifier.Ident (_, { ea_tp = Some (PrimType Bystr_typ as tp); _ });
          Identifier.Ident (_, { ea_tp = Some (PrimType Bystr_typ); _ });
        ] ->
          (* String _concat_String ( void* _execptr, String s1, String s2 ) *)
          (* ByStr _concat_ByStr ( void* _execptr, ByStr s1, ByStr s2 ) *)
          let%bind fname =
            match tp with
            | PrimType String_typ -> pure "_concat_String"
            | PrimType Bystr_typ -> pure "_concat_ByStr"
            | _ ->
                fail1 "GenLlvm: decl_builtins: internal error in concat"
                  brep.ea_loc
          in
          let%bind arg_llty = genllvm_typ_fst llmod tp in
          let%bind () =
            ensure ~loc:brep.ea_loc
              (can_pass_by_val dl arg_llty)
              "GenLlvm: decl_builtins: cannot pass variable length (byte) \
               string by value"
          in
          let%bind decl =
            scilla_function_decl llmod fname arg_llty
              [ void_ptr_type llctx; arg_llty; arg_llty ]
          in
          let opds' = List.map opds ~f:(fun opd -> CALLArg_ScillaVal opd) in
          build_builtin_call_helper' decl opds' tp
      | _ ->
          fail1 "GenLlvm: decl_builtins: invalid operand types for concat"
            brep.ea_loc)
  | Builtin_substr -> (
      match opds with
      | [
          Identifier.Ident
            (_, { ea_tp = Some (PrimType (String_typ as ptp)); _ });
          Identifier.Ident (_, { ea_tp = Some (PrimType (Uint_typ Bits32)); _ });
          Identifier.Ident (_, { ea_tp = Some (PrimType (Uint_typ Bits32)); _ });
        ]
      | [
          Identifier.Ident (_, { ea_tp = Some (PrimType (Bystr_typ as ptp)); _ });
          Identifier.Ident (_, { ea_tp = Some (PrimType (Uint_typ Bits32)); _ });
          Identifier.Ident (_, { ea_tp = Some (PrimType (Uint_typ Bits32)); _ });
        ] ->
          (* String _substr_String ( void* _execptr, String, Uint32 pos, Uint32 len ) *)
          (* ByStr _substr_ByStr ( void* _execptr, ByStr, Uint32 pos, Uint32 len ) *)
          let%bind fname =
            match ptp with
            | String_typ -> pure "_substr_String"
            | Bystr_typ -> pure "_substr_ByStr"
            | _ ->
                fail1 "GenLlvm: decl_builtins: internal error in substr"
                  brep.ea_loc
          in
          let%bind arg_llty = genllvm_typ_fst llmod (PrimType ptp) in
          let%bind () =
            ensure ~loc:brep.ea_loc
              (can_pass_by_val dl arg_llty)
              "GenLlvm: decl_builtins: cannot pass variable length (byte) \
               string by value"
          in
          let%bind uint32_ty =
            genllvm_typ_fst llmod TypeUtilities.PrimTypes.uint32_typ
          in
          let%bind decl =
            scilla_function_decl llmod fname arg_llty
              [ void_ptr_type llctx; arg_llty; uint32_ty; uint32_ty ]
          in
          let opds' = List.map opds ~f:(fun opd -> CALLArg_ScillaVal opd) in
          build_builtin_call_helper' decl opds' (PrimType ptp)
      | _ ->
          fail1 "GenLlvm: decl_builtins: Incorrect arguments to substr."
            brep.ea_loc)
  | Builtin_strlen -> (
      match opds with
      | [
          Identifier.Ident
            (_, { ea_tp = Some (PrimType (String_typ as ptp)); _ });
        ]
      | [
          Identifier.Ident (_, { ea_tp = Some (PrimType (Bystr_typ as ptp)); _ });
        ] ->
          (* Uint32 _strlen_String (String) *)
          (* Uint32 _strlen_ByStr (ByStr) *)
          let%bind fname =
            match ptp with
            | String_typ -> pure "_strlen_String"
            | Bystr_typ -> pure "_strlen_ByStr"
            | _ ->
                fail1 "GenLlvm: decl_builtins: internal error in strlen"
                  brep.ea_loc
          in
          let%bind arg_llty = genllvm_typ_fst llmod (PrimType ptp) in
          let%bind () =
            ensure ~loc:brep.ea_loc
              (can_pass_by_val dl arg_llty)
              "GenLlvm: decl_builtins: cannot pass variable length (byte) \
               string by value"
          in
          let uint32_ty = TypeUtilities.PrimTypes.uint32_typ in
          let%bind uint32_ty_ll = genllvm_typ_fst llmod uint32_ty in
          let%bind decl =
            scilla_function_decl llmod fname uint32_ty_ll [ arg_llty ]
          in
          let opds' = List.map opds ~f:(fun opd -> CALLArg_ScillaVal opd) in
          build_builtin_call_helper' ~execptr_b:false decl opds' uint32_ty
      | _ ->
          fail1 "GenLlvm: decl_builtins: Incorrect arguments to strlen."
            brep.ea_loc)
  | Builtin_to_string -> (
      let retty = PrimType String_typ in
      let%bind retty_ll = genllvm_typ_fst llmod retty in
      (* String _to_string ( void* _execptr, TyDescr *td, void *v) *)
      match opds with
      | [ opd ] ->
          let%bind decl =
            let%bind tdty = TypeDescr.srtl_typ_ll llmod in
            scilla_function_decl llmod "_to_string" retty_ll
              [
                void_ptr_type llctx; Llvm.pointer_type tdty; void_ptr_type llctx;
              ]
          in
          let%bind ty = id_typ opd in
          let%bind tydescr = td_resolver ty in
          build_builtin_call_helper' decl
            [ CALLArg_LLVMVal tydescr; CALLArg_ScillaMemVal opd ]
            retty
      | _ ->
          fail1
            "GenLlvm: decl_builtins: to_string expects exactly one argument."
            brep.ea_loc)
  | Builtin_to_ascii -> (
      (* String _to_ascii ( void* _execptr, uint8_t *v, int len) *)
      let retty = PrimType String_typ in
      let%bind retty_ll = genllvm_typ_fst llmod retty in
      let%bind decl =
        scilla_function_decl llmod "_to_ascii" retty_ll
          [
            void_ptr_type llctx;
            Llvm.pointer_type (Llvm.i8_type llctx);
            Llvm.i32_type llctx;
          ]
      in
      match opds with
      | [ (Identifier.Ident (_, { ea_tp = Some sty; _ }) as ptrarg) ]
        when is_bystrx_compatible_typ sty ->
          let%bind x = bystrx_compatible_width sty in
          build_builtin_call_helper' decl
            [
              CALLArg_ScillaMemVal ptrarg;
              CALLArg_LLVMVal (Llvm.const_int (Llvm.i32_type llctx) x);
            ]
            retty
      | [
       (Identifier.Ident (_, { ea_tp = Some (PrimType Bystr_typ); _ }) as sarg);
      ] ->
          let%bind sarg' = id_resolver (Some builder) sarg in
          (* Extract from `String` (see scilla_bytes_ty) 
           * the buffer pointer and length. *)
          let%bind ptrarg =
            build_extractvalue sarg' 0 (tempname bname) builder
          in
          let%bind lenarg =
            build_extractvalue sarg' 1 (tempname bname) builder
          in
          build_builtin_call_helper' decl
            [ CALLArg_LLVMVal ptrarg; CALLArg_LLVMVal lenarg ]
            retty
      | _ ->
          fail1 "GenLlvm: decl_builtins: to_ascii expects exactly one argument."
            brep.ea_loc)
  | Builtin_to_uint32 | Builtin_to_uint64 | Builtin_to_uint128
  | Builtin_to_uint256 | Builtin_to_int32 | Builtin_to_int64 | Builtin_to_int128
  | Builtin_to_int256 -> (
      let open TypeUtilities in
      match opds with
      | [ (Identifier.Ident (_, { ea_tp = Some opdty; _ }) as opd) ]
      (* void* to_(u)int(32/64/128/256) (void* _execptr, TyDescr* tydescr, void* Val) *)
        when is_int_type opdty || is_uint_type opdty || is_string_type opdty ->
          let%bind decl =
            let%bind tdty = TypeDescr.srtl_typ_ll llmod in
            let fname = "_" ^ pp_builtin b in
            scilla_function_decl llmod fname (void_ptr_type llctx)
              [
                void_ptr_type llctx; Llvm.pointer_type tdty; void_ptr_type llctx;
              ]
          in
          let%bind ty = id_typ opd in
          let%bind tydescr = td_resolver ty in
          (* The return type is determined based on the type of this builtin. *)
          let%bind retty = rep_typ brep in
          let%bind () =
            ensure
              (* These builtins return an Option, based on success/fail. *)
              (match retty with
              | ADT (tname, _)
                when String.(Identifier.as_string tname = "Option") ->
                  true
              | _ -> false)
              "GenLlvm: decl_builtins: Expected return type of to_(u)int* to \
               be Option"
          in
          build_builtin_call_helper' decl
            [ CALLArg_LLVMVal tydescr; CALLArg_ScillaMemVal opd ]
            retty
      | [ Identifier.Ident (_, { ea_tp = Some opdty; _ }) ]
        when is_bystrx_compatible_typ opdty ->
          let%bind x = bystrx_compatible_width opdty in
          (* Uint32 _bystrx_to_uint(32/64/128) (void*, void*, ByStrX, X *)
          (* Uint256* _bystrx_to_uint256 (void*, void*, ByStrX, X) *)
          (* _bystrx_to_uint* (_execptr, bystrx_value_p, length_bystrx_value *)
          let%bind fname, retty, ret_llty, isize =
            match b with
            | Builtin_to_uint32 ->
                let rty = TypeUtilities.PrimTypes.uint32_typ in
                let%bind rty_ll = genllvm_typ_fst llmod rty in
                pure ("_bystrx_to_uint32", rty, rty_ll, 32 / 8)
            | Builtin_to_uint64 ->
                let rty = TypeUtilities.PrimTypes.uint64_typ in
                let%bind rty_ll = genllvm_typ_fst llmod rty in
                pure ("_bystrx_to_uint64", rty, rty_ll, 64 / 8)
            | Builtin_to_uint128 ->
                let rty = TypeUtilities.PrimTypes.uint128_typ in
                let%bind rty_ll = genllvm_typ_fst llmod rty in
                pure ("_bystrx_to_uint128", rty, rty_ll, 128 / 8)
            | Builtin_to_uint256 ->
                (* Returns a pointer to Uint256 *)
                let rty = TypeUtilities.PrimTypes.uint256_typ in
                let%bind rty_ll = genllvm_typ_fst llmod rty in
                pure
                  ("_bystrx_to_uint256", rty, Llvm.pointer_type rty_ll, 256 / 8)
            | _ -> fail0 "GenLlvm: decl_builtins: internal error"
          in
          let%bind () =
            ensure ~loc:brep.ea_loc (x <= isize)
              "GenLlvm: decl_builtins: ByStrX longer than target integer"
          in
          let i32_llty = Llvm.i32_type llctx in
          let%bind decl =
            scilla_function_decl llmod fname ret_llty
              [ void_ptr_type llctx; i32_llty; void_ptr_type llctx ]
          in
          let opds' = List.map opds ~f:(fun opd -> CALLArg_ScillaMemVal opd) in
          build_builtin_call_helper' decl
            (CALLArg_LLVMVal (Llvm.const_int i32_llty x) :: opds')
            retty
      | _ -> fail0 "GenLlvm: decl_builtins: Incorrect arguments to to_uint.")
  | Builtin_to_nat -> (
      (*  # Nat* (void*, Uint32)
       *  # nat_value _to_nat (_execptr, uint32_value)
       *)
      match opds with
      | [
       (Identifier.Ident (_, { ea_tp = Some (PrimType (Uint_typ Bits32)); _ })
       as opd);
      ] ->
          let nat_ty =
            ADT
              ( Identifier.mk_loc_id (Identifier.Name.parse_simple_name "Nat"),
                [] )
          in
          let%bind nat_ty_ll = genllvm_typ_fst llmod nat_ty in

          let%bind uint32_ty =
            genllvm_typ_fst llmod TypeUtilities.PrimTypes.uint32_typ
          in
          let fname = "_to_nat" in
          let%bind decl =
            scilla_function_decl llmod fname nat_ty_ll
              [ void_ptr_type llctx; uint32_ty ]
          in
          build_builtin_call_helper' decl [ CALLArg_ScillaVal opd ] nat_ty
      | _ ->
          fail1 "GenLlvm: decl_builtins: to_nat expects Uint32 argument."
            brep.ea_loc)
  | Builtin_to_bystr -> (
      match opds with
      | [ (Identifier.Ident (_, { ea_tp = Some opdty; _ }) as opd) ]
        when is_bystrx_compatible_typ opdty ->
          let%bind b = bystrx_compatible_width opdty in
          (* Bystr _to_bystr ( void* _execptr, int X, void* v ) *)
          let fname = "_to_bystr" in
          let retty = PrimType PrimType.Bystr_typ in
          let%bind retty_ll = genllvm_typ_fst llmod retty in
          let%bind decl =
            scilla_function_decl llmod fname retty_ll
              [ void_ptr_type llctx; Llvm.i32_type llctx; void_ptr_type llctx ]
          in
          let i32_b = Llvm.const_int (Llvm.i32_type llctx) b in
          (* Unconditionally pass through memory. *)
          build_builtin_call_helper' decl
            [ CALLArg_LLVMVal i32_b; CALLArg_ScillaMemVal opd ]
            retty
      | _ ->
          fail1 "GenLlvm: decl_builtins: to_bystr expected ByStrX argument"
            brep.ea_loc)
  | Builtin_to_bystrx bw -> (
      match opds with
      | [
       (Identifier.Ident (_, { ea_tp = Some (PrimType Bystr_typ as argtp); _ })
       as opd);
      ] ->
          (* void* _bystr_to_bystrx ( void* _execptr, int X, ByStr ) *)
          let fname = "_bystr_to_bystrx" in
          let%bind argty = genllvm_typ_fst llmod argtp in
          let%bind () =
            ensure ~loc:brep.ea_loc (can_pass_by_val dl argty)
              "GenLlvm: decl_builtins: cannot pass variable length (byte) \
               string by value"
          in
          let i32ty_ll = Llvm.i32_type llctx in
          let%bind decl =
            scilla_function_decl llmod fname (void_ptr_type llctx)
              [ void_ptr_type llctx; i32ty_ll; argty ]
          in
          (* Returns (Option ByStrX), which is a pointer in the LLVM-IR *)
          let retty = get_option_type (PrimType (PrimType.Bystrx_typ bw)) in
          build_builtin_call_helper' decl
            [
              CALLArg_LLVMVal (Llvm.const_int i32ty_ll bw);
              CALLArg_ScillaVal opd;
            ]
            retty
      | [
       (Identifier.Ident
          (_, { ea_tp = Some (PrimType (Uint_typ iw) as argtp); _ }) as opd);
      ] ->
          (* void* _uint(32/64/128)_to_bystrx ( void* _execptr, Uint(32/64/128) ) *)
          (* void* _uint256_to_bystrx ( void* _execptr, Uint256* ) *)
          let fname =
            "_uint" ^ PrimType.int_bit_width_to_string iw ^ "_to_bystrx"
          in
          let%bind argty =
            let%bind basety = genllvm_typ_fst llmod argtp in
            match iw with
            | Bits32 | Bits64 | Bits128 -> pure basety
            | Bits256 -> pure (Llvm.pointer_type basety)
          in
          let%bind () =
            ensure ~loc:brep.ea_loc (can_pass_by_val dl argty)
              "GenLlvm: decl_builtins: Unable to pass integer by value"
          in
          let%bind decl =
            scilla_function_decl llmod fname (void_ptr_type llctx)
              [ void_ptr_type llctx; argty ]
          in
          (* Returns ByStrX *)
          let retty = PrimType (Bystrx_typ bw) in
          build_builtin_call_helper' decl [ CALLArg_ScillaVal opd ] retty
      | _ ->
          fail1 "GenLlvm: decl_builtins: to_bystrx invalid argument type"
            brep.ea_loc)
  | Builtin_bech32_to_bystr20 -> (
      (*  TName_Option_ByStr20 *_bech32_to_bystr20(void* _execptr, String prefix, String a) *)
      match opds with
      | [
       (Identifier.Ident (_, { ea_tp = Some (PrimType String_typ as sargty); _ })
       as prefix_opd);
       (Identifier.Ident (_, { ea_tp = Some (PrimType String_typ); _ }) as
       addr_opd);
      ] ->
          let fname = "_bech32_to_bystr20" in
          let%bind strty = genllvm_typ_fst llmod sargty in
          let retty =
            get_option_type
              (PrimType (Bystrx_typ Scilla_base.Type.address_length))
          in
          let%bind retty_ll = genllvm_typ_fst llmod retty in
          let%bind decl =
            scilla_function_decl llmod fname retty_ll
              [ void_ptr_type llctx; strty; strty ]
          in
          build_builtin_call_helper' decl
            [ CALLArg_ScillaVal prefix_opd; CALLArg_ScillaVal addr_opd ]
            retty
      | _ ->
          fail1
            "GenLlvm: decl_builtins: bech32_to_bystr20 invalid argument type"
            brep.ea_loc)
  | Builtin_bystr20_to_bech32 -> (
      (*  %TName_Option_String * _bystr20_to_bech32(void* _execptr, String prefix, ByStr20 *a) *)
      match opds with
      | [
       (Identifier.Ident (_, { ea_tp = Some (PrimType String_typ as sargty); _ })
       as prefix_opd);
       (Identifier.Ident
          (_, { ea_tp = Some (PrimType (Bystrx_typ w) as bystr20_typ); _ }) as
       addr_opd);
      ]
        when w = Scilla_base.Type.address_length ->
          let fname = "_bystr20_to_bech32" in
          let%bind strty = genllvm_typ_fst llmod sargty in
          let%bind bystr20_typ_ll = genllvm_typ_fst llmod bystr20_typ in
          let retty = get_option_type (PrimType String_typ) in
          let%bind retty_ll = genllvm_typ_fst llmod retty in
          let%bind decl =
            scilla_function_decl llmod fname retty_ll
              [ void_ptr_type llctx; strty; Llvm.pointer_type bystr20_typ_ll ]
          in
          build_builtin_call_helper' decl
            [ CALLArg_ScillaVal prefix_opd; CALLArg_ScillaVal addr_opd ]
            retty
      | _ ->
          fail1
            "GenLlvm: decl_builtins: bystr20_to_bech32 invalid argument type"
            brep.ea_loc)
  | Builtin_sha256hash | Builtin_keccak256hash | Builtin_ripemd160hash -> (
      (* ByStr(20/32)*
         _sha256hash/_keccak256hash/ripemd160hash
           ( void* _execptr, TyDescr *td, void *v) *)
      let%bind fname, retty =
        match b with
        | Builtin_sha256hash ->
            pure ("_sha256hash", PrimType (PrimType.Bystrx_typ hash_length))
        | Builtin_keccak256hash ->
            pure ("_keccak256hash", PrimType (PrimType.Bystrx_typ hash_length))
        | Builtin_ripemd160hash ->
            pure
              ( "_ripemd160hash",
                PrimType (PrimType.Bystrx_typ Scilla_base.Type.address_length)
              )
        | _ -> fail0 "GenLlvm: decl_builtins: Internal error"
      in
      let%bind bystrx_ty = genllvm_typ_fst llmod retty in
      match opds with
      | [ opd ] ->
          let%bind decl =
            let%bind tdty = TypeDescr.srtl_typ_ll llmod in
            scilla_function_decl llmod fname
              (Llvm.pointer_type bystrx_ty)
              [
                void_ptr_type llctx; Llvm.pointer_type tdty; void_ptr_type llctx;
              ]
          in
          let%bind ty = id_typ opd in
          let%bind tydescr = td_resolver ty in
          build_builtin_call_helper' decl
            [ CALLArg_LLVMVal tydescr; CALLArg_ScillaMemVal opd ]
            retty
      | _ ->
          fail1 "GenLlvm: decl_builtins: hash builtins expect single argument"
            brep.ea_loc)
  | Builtin_schnorr_verify | Builtin_ecdsa_verify -> (
      (* Bool _(schnorr/ecdsa)_verify (void* _execptr, ByStr33* pubkey, ByStr, ByStr64* ) *)
      match opds with
      | [
       (Identifier.Ident
          (_, { ea_tp = Some (PrimType (Bystrx_typ w_pk) as bystr33_typ); _ })
       as pubkey_opd);
       (Identifier.Ident
          (_, { ea_tp = Some (PrimType Bystr_typ as bystr_typ); _ }) as msg_opd);
       (Identifier.Ident
          (_, { ea_tp = Some (PrimType (Bystrx_typ w_sign) as bystr64_typ); _ })
       as sign_opd);
      ]
        when w_pk = Schnorr.pubkey_len && w_sign = Schnorr.signature_len ->
          let%bind () =
            ensure
              (Schnorr.pubkey_len = Secp256k1Wrapper.pubkey_len
              && Schnorr.signature_len = Secp256k1Wrapper.signature_len)
              "Internal error: expected same pubkey and sign lengths for \
               Schnorr and ECDSA"
          in
          let%bind retty, retty_ll = get_bool_types llmod in
          let%bind pubkey_llty = genllvm_typ_fst llmod bystr33_typ in
          let%bind sign_llty = genllvm_typ_fst llmod bystr64_typ in
          let%bind msg_llty = genllvm_typ_fst llmod bystr_typ in
          let%bind decl =
            scilla_function_decl llmod ("_" ^ bname) retty_ll
              [
                void_ptr_type llctx;
                Llvm.pointer_type pubkey_llty;
                msg_llty;
                Llvm.pointer_type sign_llty;
              ]
          in
          build_builtin_call_helper' decl
            [
              CALLArg_ScillaVal pubkey_opd;
              CALLArg_ScillaVal msg_opd;
              CALLArg_ScillaVal sign_opd;
            ]
            retty
      | _ ->
          fail1 "GenLlvm: decl_builtins: Invalid operands to schnorr_verify"
            brep.ea_loc)
  | Builtin_schnorr_get_address -> (
      match opds with
      | [
       (Identifier.Ident
          (_, { ea_tp = Some (PrimType (Bystrx_typ w_pk) as bystr33_typ); _ })
       as pubkey_opd);
      ]
        when w_pk = Schnorr.pubkey_len ->
          (* ByStr20* _schnorr_get_address ( void* _execptr, ByStr33* pubkey ) *)
          let bystr20_ty =
            PrimType (Bystrx_typ Scilla_base.Type.address_length)
          in
          let%bind bystr20_llty = genllvm_typ_fst llmod bystr20_ty in
          let%bind bystr33_llty = genllvm_typ_fst llmod bystr33_typ in
          let%bind decl =
            scilla_function_decl llmod "_schnorr_get_address"
              (Llvm.pointer_type bystr20_llty)
              [ void_ptr_type llctx; Llvm.pointer_type bystr33_llty ]
          in
          build_builtin_call_helper' decl
            [ CALLArg_ScillaVal pubkey_opd ]
            bystr20_ty
      | _ ->
          fail1 "GenLlvm: decl_builtins: Invalid operand to schnorr_get_address"
            brep.ea_loc)
  | Builtin_ecdsa_recover_pk -> (
      match opds with
      | [
       (Identifier.Ident
          (_, { ea_tp = Some (PrimType Bystr_typ as bystr_typ); _ }) as msg_opd);
       (Identifier.Ident
          (_, { ea_tp = Some (PrimType (Bystrx_typ w_sign) as bystr64_typ); _ })
       as sign_opd);
       (Identifier.Ident
          (_, { ea_tp = Some (PrimType (Uint_typ Bits32) as uint32_typ); _ }) as
       recid_opd);
      ]
        when w_sign = Schnorr.signature_len ->
          let%bind sign_llty = genllvm_typ_fst llmod bystr64_typ in
          let%bind msg_llty = genllvm_typ_fst llmod bystr_typ in
          let%bind recid_llty = genllvm_typ_fst llmod uint32_typ in
          (* ByStr65* _ecdsa_recover_pk ( void* _execptr, ByStr Msg, ByStr64* sign, Uint32 recid ) *)
          let ret_ty =
            PrimType (Bystrx_typ Secp256k1Wrapper.uncompressed_pubkey_len)
          in
          let%bind ret_llty = genllvm_typ_fst llmod ret_ty in
          let%bind decl =
            scilla_function_decl llmod "_ecdsa_recover_pk"
              (Llvm.pointer_type ret_llty)
              [
                void_ptr_type llctx;
                msg_llty;
                Llvm.pointer_type sign_llty;
                recid_llty;
              ]
          in
          build_builtin_call_helper' decl
            [
              CALLArg_ScillaVal msg_opd;
              CALLArg_ScillaVal sign_opd;
              CALLArg_ScillaVal recid_opd;
            ]
            ret_ty
      | _ ->
          fail1 "GenLlvm: decl_builtins: Invalid operand to schnorr_get_address"
            brep.ea_loc)
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
          build_builtin_call_helper' decl
            [
              CALLArg_LLVMVal tydescr;
              CALLArg_ScillaMemVal m_opd;
              CALLArg_ScillaMemVal k_opd;
              CALLArg_ScillaMemVal v_opd;
            ]
            mty
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
          let retty = get_option_type vt in
          let%bind tydescr = td_resolver mty in
          build_builtin_call_helper' decl
            [
              CALLArg_LLVMVal tydescr;
              CALLArg_ScillaMemVal m_opd;
              CALLArg_ScillaMemVal k_opd;
            ]
            retty
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
          let%bind retty, retty_ll = get_bool_types llmod in
          let%bind tydesrc_ty = TypeDescr.srtl_typ_ll llmod in
          let%bind decl =
            scilla_function_decl llmod fname retty_ll
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
          build_builtin_call_helper' decl
            [
              CALLArg_LLVMVal tydescr;
              CALLArg_ScillaMemVal m_opd;
              CALLArg_ScillaMemVal k_opd;
            ]
            retty
      | _ ->
          fail1 "GenLlvm: decl_builtins: Incorrect arguments to contains"
            brep.ea_loc)
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
          build_builtin_call_helper' decl
            [
              CALLArg_LLVMVal tydescr;
              CALLArg_ScillaMemVal m_opd;
              CALLArg_ScillaMemVal k_opd;
            ]
            mty
      | _ ->
          fail1 "GenLlvm: decl_builtins: Incorrect arguments to remove"
            brep.ea_loc)
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
          build_builtin_call_helper' ~execptr_b:false decl
            [ CALLArg_ScillaMemVal m_opd ]
            retty
      | _ ->
          fail1 "GenLlvm: decl_builtins: Incorrect arguments to size"
            brep.ea_loc)
  | Builtin_blt -> (
      (* Bool res = _lt_BNum ( void* _execptr, BNum opd1, BNum opd2 ) *)
      (* where BNum is represented by void* *)
      match opds with
      | [
       (Identifier.Ident (_, { ea_tp = Some (PrimType Bnum_typ); _ }) as opd1);
       (Identifier.Ident (_, { ea_tp = Some (PrimType Bnum_typ); _ }) as opd2);
      ] ->
          let fname = "_lt_BNum" in
          let%bind retty, retty_ll = get_bool_types llmod in
          let%bind bnty_ll = genllvm_typ_fst llmod (PrimType Bnum_typ) in
          let%bind decl =
            scilla_function_decl llmod fname retty_ll
              (* _execptr, opd1 and opd2 *)
              [ void_ptr_type llctx; bnty_ll; bnty_ll ]
          in
          build_builtin_call_helper' decl
            [ CALLArg_ScillaVal opd1; CALLArg_ScillaVal opd2 ]
            retty
      | _ ->
          fail1 "GenLlvm: decl_builtins: Incorrect arguments to blt" brep.ea_loc
      )
  | Builtin_badd -> (
      (* Add an unsigned integer (described by tydescr) to a BNum value. *)
      (* BNum _badd (void* _execptr, BNum bval, TyDescr* tydescr, void *ui_val) *)
      (*   where BNum = ( void* ) *)
      match opds with
      | [
       (Identifier.Ident (_, { ea_tp = Some (PrimType Bnum_typ); _ }) as opd1);
       (Identifier.Ident (_, { ea_tp = Some (PrimType (Uint_typ _)); _ }) as
       opd2);
      ] ->
          let%bind decl =
            let%bind tdty = TypeDescr.srtl_typ_ll llmod in
            let fname = "_badd" in
            scilla_function_decl llmod fname (void_ptr_type llctx)
              [
                void_ptr_type llctx;
                void_ptr_type llctx;
                Llvm.pointer_type tdty;
                void_ptr_type llctx;
              ]
          in
          let%bind ty = id_typ opd2 in
          let%bind tydescr = td_resolver ty in
          build_builtin_call_helper' decl
            [
              CALLArg_ScillaVal opd1;
              CALLArg_LLVMVal tydescr;
              CALLArg_ScillaMemVal opd2;
            ]
            (PrimType Bnum_typ)
      | _ ->
          fail1 "GenLlvm: decl_builtins: Incorrect arguments to badd."
            brep.ea_loc)
  | Builtin_bsub -> (
      (* Subtract two block number to give Int256. *)
      (* Int256* _bsub (void* _execptr, BNum bval1, BNum bval2) *)
      (*   where BNum = ( void* ) *)
      match opds with
      | [
       (Identifier.Ident (_, { ea_tp = Some (PrimType Bnum_typ); _ }) as opd1);
       (Identifier.Ident (_, { ea_tp = Some (PrimType Bnum_typ); _ }) as opd2);
      ] ->
          let retty = PrimType (Int_typ Bits256) in
          let%bind decl =
            let fname = "_bsub" in
            let%bind retty_ll = genllvm_typ_fst llmod retty in
            let%bind argty_ll = genllvm_typ_fst llmod (PrimType Bnum_typ) in
            let%bind () =
              ensure
                Base.Poly.(argty_ll = void_ptr_type llctx)
                "GenLlvm: decl_builtins: BNum must be boxed"
            in
            scilla_function_decl llmod fname
              (Llvm.pointer_type retty_ll)
              [ void_ptr_type llctx; argty_ll; argty_ll ]
          in
          build_builtin_call_helper' decl
            [ CALLArg_ScillaVal opd1; CALLArg_ScillaVal opd2 ]
            retty
      | _ ->
          fail1 "GenLlvm: decl_builtins: Incorrect arguments to bsub."
            brep.ea_loc)
  | Builtin_strrev | Builtin_to_list | Builtin_pow | Builtin_isqrt
  | Builtin_alt_bn128_G1_add | Builtin_alt_bn128_G1_mul
  | Builtin_alt_bn128_pairing_product ->
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

(* Same as decl_fetch_field, but with an additional ByStr20 parameter.comp_name.
 *   # void* ( void*, const *uint8_t[20], const char *, Typ*, i32, i8*, i32 )
 *   # fetched_val ( execptr address field_name field_tydescr num_indices indices fetchval )
 *)
let decl_fetch_remote_field llmod =
  let llctx = Llvm.module_context llmod in
  let%bind tydesrc_ty = TypeDescr.srtl_typ_ll llmod in
  let%bind address_ty = genllvm_typ_fst llmod (Address None) in
  scilla_function_decl ~is_internal:false llmod "_fetch_remote_field"
    (void_ptr_type llctx)
    [
      void_ptr_type llctx;
      Llvm.pointer_type address_ty;
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

(* void *_read_blockchain(void* _execptr, String VName) *)
let decl_read_blockchain llmod =
  let llctx = Llvm.module_context llmod in
  let%bind bnum_string_ty = scilla_bytes_ty llmod "BCVName" in
  let fname = "_read_blockchain" in
  let%bind decl =
    scilla_function_decl ~is_internal:false llmod fname (void_ptr_type llctx)
      [ void_ptr_type llctx; bnum_string_ty ]
  in
  pure (decl, bnum_string_ty)

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
      (ADT
         ( Identifier.mk_loc_id (Identifier.Name.parse_simple_name "List"),
           [ TypeUtilities.PrimTypes.msg_typ ] ))
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
      let llctx = Llvm.module_context llmod in
      let fname = "_new_empty_map" in
      let%bind decl =
        scilla_function_decl ~is_internal:false llmod fname
          (void_ptr_type llctx) [ void_ptr_type llctx ]
      in
      let dummy_resolver _ _ =
        fail0 "GenLlvm: build_new_empty_map: Nothing to resolve."
      in
      build_builtin_call_helper ~execptr_b:true None llmod dummy_resolver
        builder fname decl [] mt
  | _ -> fail0 "GenLlvm: build_new_empty_map: Cannot create non-map values."

(* void* _new_bnum (void* execptr, String Val) *)
let build_new_bnum llmod builder strval =
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in
  let llctx = Llvm.module_context llmod in
  let bnty = PrimType Bnum_typ in
  let%bind bnty_ll = genllvm_typ_fst llmod bnty in
  let%bind bnum_string_ty = scilla_bytes_ty llmod "BNumString" in
  let fname = "_new_bnum" in
  let%bind decl =
    scilla_function_decl ~is_internal:false llmod fname bnty_ll
      [ void_ptr_type llctx; bnum_string_ty ]
  in
  let dummy_resolver _ _ =
    fail0 "GenLlvm: build_new_empty_map: Nothing to resolve."
  in
  let%bind arg =
    define_string_value llmod bnum_string_ty ~name:(tempname "BNumLit") ~strval
  in
  let%bind () =
    ensure
      (can_pass_by_val dl bnum_string_ty)
      "GenLlvm: build_new_bnum: Internal error: Cannot pass string by value"
  in
  build_builtin_call_helper ~execptr_b:true None llmod dummy_resolver builder
    fname decl [ CALLArg_LLVMVal arg ] bnty

let build_literal_cost builder td_resolver id_resolver llmod v =
  let fname = "_literal_cost" in
  (* Computes the size of a value, equal to literal_cost in Scilla_base. *)
  (* uint64_t (Typ* typdescr, void* V *)
  let decl_literal_cost llmod =
    let llctx = Llvm.module_context llmod in
    let%bind tydesrc_ty = TypeDescr.srtl_typ_ll llmod in
    scilla_function_decl ~is_internal:false llmod fname (Llvm.i64_type llctx)
      [ Llvm.pointer_type tydesrc_ty; void_ptr_type llctx ]
  in
  (* Note: The return type isn't the Scilla Uint64, but an llvm i64.
   * We use this one here to just cheat build_builtin_call_helper to
   * not take any action on the return value of the SRTL function. *)
  let retty = PrimType (Uint_typ Bits64) in
  let%bind decl = decl_literal_cost llmod in
  match v with
  | Identifier.Ident (_, { ea_tp = Some sty; _ }) as vopd ->
      (* TODO: For integer and ByStrX types, return statically. *)
      let%bind tydescr = td_resolver sty in
      build_builtin_call_helper ~execptr_b:false None llmod id_resolver builder
        fname decl
        [ CALLArg_LLVMVal tydescr; CALLArg_ScillaMemVal vopd ]
        retty
  | _ -> fail0 "GenLlvm: build_literal_cost: Invalid argument"

let build_lengthof builder td_resolver id_resolver llmod v =
  let fname = "_lengthof" in
  (* Compute the length of a Scilla lists and maps. *)
  (* uint64_t (Typ* typdescr, void* V *)
  let decl_lengthof llmod =
    let llctx = Llvm.module_context llmod in
    let%bind tydesrc_ty = TypeDescr.srtl_typ_ll llmod in
    scilla_function_decl ~is_internal:false llmod fname (Llvm.i64_type llctx)
      [ Llvm.pointer_type tydesrc_ty; void_ptr_type llctx ]
  in
  let%bind decl = decl_lengthof llmod in
  (* Note: The return type isn't the Scilla Uint64, but an llvm i64.
   * We use this one here to just cheat build_builtin_call_helper to
   * not take any action on the return value of the SRTL function. *)
  let retty = PrimType (Uint_typ Bits64) in
  match v with
  | Identifier.Ident (_, { ea_tp = Some sty; _ }) as vopd ->
      let%bind tydescr = td_resolver sty in
      build_builtin_call_helper ~execptr_b:false None llmod id_resolver builder
        fname decl
        [ CALLArg_LLVMVal tydescr; CALLArg_ScillaMemVal vopd ]
        retty
  | _ -> fail0 "GenLlvm: build_lengthof: Invalid argument"

let build_mapsortcost builder id_resolver llmod v =
  let fname = "_mapsortcost" in
  (* Compute the cost of (nested) sorting a Scilla map. *)
  (* uint64_t (void* V *)
  let decl_mapsortcost llmod =
    let llctx = Llvm.module_context llmod in
    scilla_function_decl ~is_internal:false llmod "_mapsortcost"
      (Llvm.i64_type llctx) [ void_ptr_type llctx ]
  in
  (* Note: The return type isn't the Scilla Uint64, but an llvm i64.
   * We use this one here to just cheat build_builtin_call_helper to
   * not take any action on the return value of the SRTL function. *)
  let retty = PrimType (Uint_typ Bits64) in
  let%bind decl = decl_mapsortcost llmod in
  build_builtin_call_helper ~execptr_b:false None llmod id_resolver builder
    fname decl [ CALLArg_ScillaMemVal v ] retty

(* void _out_of_gas (void) *)
let decl_out_of_gas llmod =
  let void_ty = Llvm.void_type (Llvm.module_context llmod) in
  scilla_function_decl ~is_internal:false llmod "_out_of_gas" void_ty []

(* Generate contract and transition parameter descriptors.
 * An option to cmodule is taken to enable generating empty
 * parameter descriptors for pure expressions. *)
let gen_param_descrs cmod_opt llmod (tdr : TypeDescr.typ_descr) =
  let open ClosuredSyntax.CloCnvSyntax in
  let open TypeLLConv in
  let llctx = Llvm.module_context llmod in
  (*
      // Parameter descriptor.
      struct ParamDescr {
        String m_PName;
        Typ *m_PTy;
      };
      // Transition descriptor.
      struct TransDescr {
        String m_TName;
        int32_t m_NParams;
        ParamDescr *m_Params;
      };
  *)
  let%bind tydescr_string_ty = scilla_bytes_ty llmod "ParamDescrString" in
  let%bind typ_ll_ty = TypeDescr.srtl_typ_ll llmod in
  let%bind param_descr_ty =
    named_struct_type llmod (tempname "ParamDescr")
      (* m_PName and m_PTy *)
      [| tydescr_string_ty; Llvm.pointer_type typ_ll_ty |]
  in
  let%bind trans_descr_ty =
    named_struct_type llmod (tempname "TransDescr")
      (* m_TName, m_NParams and m_Params *)
      [|
        tydescr_string_ty; Llvm.i32_type llctx; Llvm.pointer_type param_descr_ty;
      |]
  in
  let i32_ty = Llvm.i32_type llctx in

  (* Let's get the contract parameters descriptors up first. *)
  let%bind cparams'', cparams_len =
    match cmod_opt with
    | None -> pure ([||], 0)
    | Some cmod ->
        let%bind cparams' =
          mapM cmod.contr.cparams ~f:(fun (name, ty) ->
              let name' = Identifier.as_string name in
              let%bind pname =
                define_string_value llmod tydescr_string_ty
                  ~name:(tempname ("pname_" ^ name'))
                  ~strval:name'
              in
              let%bind td = TypeDescr.resolve_typdescr tdr ty in
              (* m_PName and m_PTy *)
              pure @@ Llvm.const_named_struct param_descr_ty [| pname; td |])
        in
        pure @@ (Array.of_list cparams', List.length cparams')
  in
  let _cparams_descr =
    define_global "_contract_parameters"
      (Llvm.const_array param_descr_ty cparams'')
      llmod ~const:true ~unnamed:false
  in
  let _cparams_descr_length =
    define_global "_contract_parameters_length"
      (Llvm.const_int i32_ty cparams_len)
      llmod ~const:true ~unnamed:false
  in

  (* And now, transition parameters. *)
  let%bind tparams'', tparams_len =
    match cmod_opt with
    | None -> pure ([||], 0)
    | Some cmod ->
        let tparams =
          List.filter_map cmod.contr.ccomps ~f:(fun c ->
              match c.comp_type with
              | CompTrans -> Some (c.comp_name, c.comp_params)
              | CompProc -> None)
        in
        let%bind tparams' =
          mapM tparams ~f:(fun (tname, tparams) ->
              let tname' = Identifier.as_string tname in
              let%bind params =
                mapM tparams ~f:(fun (name, ty) ->
                    let name' = Identifier.as_string name in
                    let%bind pname =
                      define_string_value llmod tydescr_string_ty
                        ~name:(tempname ("tpname_" ^ name'))
                        ~strval:name'
                    in
                    let%bind td = TypeDescr.resolve_typdescr tdr ty in
                    pure
                    @@ Llvm.const_named_struct param_descr_ty [| pname; td |])
              in
              let params' =
                Llvm.const_array param_descr_ty (Array.of_list params)
              in
              let params_global =
                Llvm.const_pointercast
                  (define_global
                     (tempname ("tparams_" ^ tname'))
                     params' llmod ~const:true ~unnamed:true)
                  (Llvm.pointer_type param_descr_ty)
              in
              let%bind tname_cval =
                define_string_value llmod tydescr_string_ty
                  ~name:(tempname ("tname_" ^ tname'))
                  ~strval:tname'
              in
              pure
              @@ Llvm.const_named_struct trans_descr_ty
                   [|
                     (* m_TName *)
                     tname_cval;
                     (* m_NParams *)
                     Llvm.const_int i32_ty (List.length tparams);
                     (* m_Params *)
                     params_global;
                   |])
        in
        pure (Array.of_list tparams', List.length tparams')
  in
  let _tparams_descr =
    define_global "_transition_parameters"
      (Llvm.const_array trans_descr_ty tparams'')
      llmod ~const:true ~unnamed:false
  in
  let _tparams_descr_length =
    define_global "_transition_parameters_length"
      (Llvm.const_int i32_ty tparams_len)
      llmod ~const:true ~unnamed:false
  in

  pure ()
