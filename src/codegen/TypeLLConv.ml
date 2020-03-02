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
open Syntax
open MonadUtil
open UncurriedSyntax.Uncurried_Syntax
open ClosuredSyntax.CloCnvSyntax
open Datatypes
open CodegenUtils

let named_struct_type ?(is_packed = false) ?(is_opaque = false) llmod name tyarr
    =
  let ctx = Llvm.module_context llmod in
  match Llvm.type_by_name llmod name with
  | Some ty ->
      (* If ty is an opaque type, we fill its body now. *)
      Base.Poly.(
        if
          Llvm.classify_type ty <> Llvm.TypeKind.Struct
          || (not (Llvm.is_opaque ty))
             && (not is_opaque)
             && Llvm.struct_element_types ty <> tyarr
        then
          fail0
            (sprintf
               "GenLlvm: named_struct_type: internal error. Type %s already \
                exists but does not match requested struct type."
               name)
        else (
          if Llvm.is_opaque ty then Llvm.struct_set_body ty tyarr is_packed;
          pure ty ))
  | None ->
      let t = Llvm.named_struct_type ctx name in
      if not is_opaque then Llvm.struct_set_body t tyarr is_packed;
      pure t

(* Create a StructType "type { i8*, i32 }".
  * This type can represent Scilla String and ByStr values.
  * Note: We cannot use LLVM's Array type to represent bytes because
  *       that requires the length to be known at compile time. *)
let scilla_bytes_ty llmod ty_name =
  let ctx = Llvm.module_context llmod in
  let charp_ty = Llvm.pointer_type (Llvm.i8_type ctx) in
  let len_ty = Llvm.i32_type ctx in
  named_struct_type llmod ty_name [| charp_ty; len_ty |]

(* Given an ADT name or one of it's constructors' and the instantiation types,
  * concatenate them to create a name for the instantiated type. *)
let type_instantiated_adt_name prefix name ts =
  match ts with
  | [] -> pure name
  | _ ->
      let%bind ts' =
        mapM ts ~f:(fun t ->
            if TypeUtilities.is_ground_type t then
              pure
                (String.map (pp_typ t) ~f:(fun c ->
                     if Char.(c = ' ') then '_' else c))
            else fail0 "GenLlvm: unexpected polymorphic ADT")
      in
      pure @@ prefix ^ name ^ "_" ^ String.concat ~sep:"_" ts'

let genllvm_typ llmod sty =
  let ctx = Llvm.module_context llmod in
  let i8_type = Llvm.i8_type ctx in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in

  let rec go ~inprocess sty =
    match sty with
    | PrimType pty ->
        let%bind llty =
          match pty with
          (* Build integer types, by wrapping LLMV's i* type in structs with names. *)
          | Int_typ bw | Uint_typ bw ->
              let bwi =
                match bw with
                | Bits32 -> 32
                | Bits64 -> 64
                | Bits128 -> 128
                | Bits256 -> 256
              in
              named_struct_type llmod (pp_prim_typ pty)
                [| Llvm.integer_type ctx bwi |]
          (* An instantiation of scilla_bytes_ty for Scilla String. *)
          | String_typ -> scilla_bytes_ty llmod "String"
          (* An instantiation of scilla_bytes_ty for Scilla Bystr. *)
          | Bystr_typ -> scilla_bytes_ty llmod "Bystr"
          (* ByStrX represented as an LLVM array of length X. *)
          | Bystrx_typ bytes -> pure @@ Llvm.array_type i8_type bytes
          | Msg_typ | Event_typ | Exception_typ | Bnum_typ ->
              fail0 "GenLlvm: genllvm_prim_typ: unimplemented"
        in
        pure (llty, [])
    | ADT (tname, ts) ->
        let%bind name_ll = type_instantiated_adt_name "TName_" tname ts in
        (* If this type is already being translated, return an opaque type. *)
        if List.exists inprocess ~f:TypeUtilities.([%equal: typ] sty) then
          let%bind tdecl =
            named_struct_type ~is_opaque:true llmod name_ll [||]
          in
          pure (Llvm.pointer_type tdecl, [])
        else
          let%bind adt = Datatypes.DataTypeDictionary.lookup_name tname in
          (* Let's get / create the types for each constructed ADTValue. *)
          let%bind cnames_ctrs_ty_ll =
            mapM adt.tconstr ~f:(fun ct ->
                let%bind arg_types =
                  TypeUtilities.constr_pattern_arg_types sty ct.cname
                in
                let%bind arg_types_ll =
                  mapM arg_types ~f:(fun t ->
                      (* Ensure that we mark sty as "in process" before making the recursive call. *)
                      let%bind llty, _ = go ~inprocess:(sty :: inprocess) t in
                      pure llty)
                in
                (* In addition to the member literal types, we add a tag at the beginning. *)
                let tagged_arg_types_ll =
                  Array.of_list @@ (i8_type :: arg_types_ll)
                in
                (* Come up with a name by suffixing the constructor name with the instantiated types. *)
                let%bind cname_ll =
                  type_instantiated_adt_name "CName_" ct.cname ts
                in
                let%bind ctr_ty_ll =
                  named_struct_type ~is_packed:true llmod cname_ll
                    tagged_arg_types_ll
                in
                (* We now have an llvm struct type to represent an object of this constructed type. *)
                pure (ct.cname, Llvm.pointer_type ctr_ty_ll))
          in
          let _, ctrs_ty_ll = List.unzip cnames_ctrs_ty_ll in
          (* We "union" the types of each constructed object type with a struct type that has a tag
             * at the start, and a list of pointers to each constructed object. The latter is only
             * to be able to verify that the constructor types and the main type are all related.
             * The tag is the only real element that will ever be accessed *)
          let%bind ty_ll =
            named_struct_type llmod name_ll
              (Array.of_list (i8_type :: ctrs_ty_ll))
          in
          (* The final type will be a pointer to this struct. *)
          pure (Llvm.pointer_type ty_ll, cnames_ctrs_ty_ll)
    | FunType (argts, rett) ->
        (* We don't know the type of the environment with just the "typ" of a function.
         * We make do with using a "void*" for it instead. *)
        let envty = void_ptr_type ctx in
        let%bind argts_ll =
          mapM argts ~f:(fun argt ->
              let%bind argt_ll, _ = go ~inprocess:(sty :: inprocess) argt in
              if can_pass_by_val dl argt_ll then pure argt_ll
              else pure @@ Llvm.pointer_type argt_ll)
        in
        let%bind rett_ll, _ = go ~inprocess:(sty :: inprocess) rett in
        let funty =
          if can_pass_by_val dl rett_ll then
            (* if return is by value, then "retval (envpointer, args ...)" *)
            Llvm.function_type rett_ll (Array.of_list (envty :: argts_ll))
          else
            let argts_final = envty :: Llvm.pointer_type rett_ll :: argts_ll in
            (* If return is not by value, then 1. env pointer, 2. ret value pointer, 3. args *)
            Llvm.function_type (Llvm.void_type ctx) (Array.of_list argts_final)
        in
        (* Functions are represented with closures, so return the closure type. *)
        pure
          ( Llvm.struct_type ctx [| Llvm.pointer_type funty; void_ptr_type ctx |],
            [] )
    | MapType _ -> fail0 "GenLlvm: genllvm_typ: MapType not supported yet"
    | PolyFun _ | TypeVar _ | Unit ->
        fail0 "GenLlvm: genllvm_typ: unsupported type"
  in
  go ~inprocess:[] sty

let genllvm_typ_fst llmod sty =
  let%bind sty', _ = genllvm_typ llmod sty in
  pure sty'

let rep_typ rep =
  match rep.ea_tp with
  | Some ty -> pure ty
  | None -> fail1 (sprintf "GenLlvm: rep_typ: not type annotated.") rep.ea_loc

let id_typ id = rep_typ (get_rep id)

let id_typ_ll llmod id =
  let%bind ty = id_typ id in
  let%bind llty, _ = genllvm_typ llmod ty in
  pure llty

let get_ctr_struct adt_llty_map cname =
  match List.Assoc.find adt_llty_map ~equal:String.( = ) cname with
  | Some ptr_llcty -> (
      (* We have a pointer type to the constructor's LLVM type. *)
      let%bind ctr_struct = ptr_element_type ptr_llcty in
      let%bind adt, _ = DataTypeDictionary.lookup_constructor cname in
      match
        List.findi adt.tconstr ~f:(fun _ cn -> String.(cname = cn.cname))
      with
      | Some (tag, _) -> pure (ctr_struct, tag)
      | None ->
          fail0
            (sprintf
               "GenLlvm: get_ctr_struct: internal error: constructor %s for \
                adt %s not found"
               cname adt.tname) )
  | None ->
      fail0
        (sprintf
           "GenLlvm get_constr_type: LLVM type for ADT constructor %s not built"
           cname)

module TypeDescr = struct
  type typ_descr = (typ, Llvm.llvalue) Caml.Hashtbl.t

  (* Track instantiations of ADTs, Maps and ByStrX *)
  type specl_dict = {
    adtspecl : (string * typ list list) list;
    mapspecl : (typ * typ) list;
    bystrspecl : int list;
  }

  let empty_specl_dict = { adtspecl = []; mapspecl = []; bystrspecl = [] }

  (* For debugging. *)
  let sprint_specl_dict specls =
    "ADTs:\n"
    ^ String.concat ~sep:"\n"
        (List.map specls.adtspecl ~f:(fun (tname, specls) ->
             sprintf "%s:\n  " tname
             ^ String.concat ~sep:"\n  "
                 (List.map specls ~f:(fun tlist ->
                      String.concat ~sep:" " (List.map tlist ~f:pp_typ)))))
    ^ "\nMaps:\n  "
    ^ String.concat ~sep:"\n  "
        (List.map specls.mapspecl ~f:(fun (kt, vt) -> pp_typ (MapType (kt, vt))))
    ^ "\nByStrX: "
    ^ String.concat ~sep:" "
        (List.map specls.bystrspecl ~f:(fun i ->
             pp_typ (PrimType (Bystrx_typ i))))

  (* Update "specls" by adding (if not already present) ADT, Map or ByStrX type "ty". *)
  let update_specl_dict (specls : specl_dict) ty =
    (* We only care of storable types. *)
    if not (TypeUtilities.is_storable_type ty) then specls
    else
      match ty with
      | ADT (tname, tlist) -> (
          let non_this, this_and_rest =
            List.split_while specls.adtspecl ~f:(fun (tname', _) ->
                String.(tname <> tname'))
          in
          match this_and_rest with
          | (_, this_specls) :: rest ->
              if
                List.mem this_specls tlist ~equal:TypeUtilities.type_equiv_list
                (* This specialization already exists. *)
              then specls (* Add this specialization. *)
              else
                {
                  specls with
                  adtspecl = (tname, tlist :: this_specls) :: (non_this @ rest);
                }
          | [] ->
              { specls with adtspecl = (tname, [ tlist ]) :: specls.adtspecl } )
      | MapType (kt, vt) ->
          if
            List.exists specls.mapspecl ~f:(fun (kt', vt') ->
                TypeUtilities.([%equal: typ] kt kt')
                && TypeUtilities.([%equal: typ] vt vt'))
          then specls
          else { specls with mapspecl = (kt, vt) :: specls.mapspecl }
      | PrimType (Bystrx_typ x) ->
          if List.mem specls.bystrspecl x ~equal:( = ) then specls
          else { specls with bystrspecl = x :: specls.bystrspecl }
      | _ -> specls

  let resolve_typdescr tdescr t =
    match Caml.Hashtbl.find_opt tdescr t with
    | Some v -> pure v
    | None ->
        fail0
          (sprintf "GenLlvm: TypeDescr: internal error: couldn't resolve %s."
             (pp_typ t))

  let tydescrty_typ_name = "_TyDescrTy_Typ"

  let srtl_typ_ll llmod =
    let llctx = Llvm.module_context llmod in
    let i32_ty = Llvm.integer_type llctx 32 in
    named_struct_type llmod tydescrty_typ_name
      [| i32_ty (* tag *); void_ptr_type llctx (* union *) |]

  (* Generate type descriptors for SRTL. The working horse of this module. *)
  let generate_typedescr llmod specls =
    let _ =
      DebugMessage.plog
        (sprintf "\nSpecialized types:\n%s\n\n" (sprint_specl_dict specls))
    in
    let llctx = Llvm.module_context llmod in
    let i32_ty = Llvm.integer_type llctx 32 in
    (* Quick convert integer to LLVM const int32 *)
    let qi i = Llvm.const_int i32_ty i in
    (* Creating double pointers types. *)
    let ptr_ptr_ty llty = Llvm.pointer_type (Llvm.pointer_type llty) in

    (* 1. Let's first define the enum values used in SRTL. *)
    (* enum ScillaTypes::PrimTyp::BitWidth in SRTL. *)
    let rec enum_bitwidth = function
      | Bits32 -> 0
      | Bits64 -> enum_bitwidth Bits32 + 1
      | Bits128 -> enum_bitwidth Bits64 + 1
      | Bits256 -> enum_bitwidth Bits128 + 1
    in
    (* enum ScillaTypes::PrimTyp::Prims in SRTL. *)
    let rec enum_prims = function
      | Int_typ _ -> 0
      | Uint_typ _ -> enum_prims (Int_typ Bits32) + 1
      | String_typ -> enum_prims (Uint_typ Bits32) + 1
      | Bnum_typ -> enum_prims String_typ + 1
      | Msg_typ -> enum_prims Bnum_typ + 1
      | Event_typ -> enum_prims Msg_typ + 1
      | Exception_typ -> enum_prims Event_typ + 1
      | Bystr_typ -> enum_prims Exception_typ + 1
      | Bystrx_typ _ -> enum_prims Bystr_typ + 1
    in
    (* enum ScillaTypes::Typ::Typs *)
    let enum_typ = function
      | PrimType _ -> pure 0
      | ADT _ -> pure 1
      | MapType _ -> pure 2
      | _ ->
          fail0 "GenLlvm: TypeDescr: enum_typ: internal error: unsupported type"
    in

    let tdescr : typ_descr = Caml.Hashtbl.create 10 in

    (* 2. Generate code for primitive types. *)
    (* A PrimTyp struct is defined as:
        struct PrimTyp {
          Prims pt; // Tag for the union below
          union {
            BitWidth m_intBW; // bit-width of Int*, Uint*
            uint32_t m_bystX; // Length of ByStrX
          };
        };
       A Typ struct is defined as:
        struct Typ {
          Typs m_t; // Tag for the union below
          union {
            PrimTyp *m_primt;
            // Typ can only be specialized.
            ADTDesc::Specl *m_spladt;
            // key type, value type.
            MapTyp *m_mapt;
          };
        };
    *)
    (* The union in PrimTyp is represented as an i32 LLVM value. *)
    let%bind tydescr_prim_ty =
      named_struct_type llmod
        (tempname "TyDescrTy_PrimTyp")
        [| i32_ty (* tag *); i32_ty (* union *) |]
    in
    let%bind tydescr_ty = srtl_typ_ll llmod in
    (* Function to wrap a PrimTyp struct with a Typ struct. *)
    let wrap_primty gname pt primptr =
      let primptr' = Llvm.const_bitcast primptr (void_ptr_type llctx) in
      let%bind ptenum = enum_typ pt in
      pure
      @@ Llvm.define_global gname
           (Llvm.const_named_struct tydescr_ty [| qi ptenum; primptr' |])
           llmod
    in

    (* Int32 *)
    let primtydescr_int32 =
      Llvm.define_global
        (tempname "TyDescr_Int32_Prim")
        (Llvm.const_named_struct tydescr_prim_ty
           [| qi (enum_prims (Int_typ Bits32)); qi (enum_bitwidth Bits32) |])
        llmod
    in
    let ty_int32 = PrimType (Int_typ Bits32) in
    let%bind tydescr_int32 =
      wrap_primty (tempname "TyDescr_Int32") ty_int32 primtydescr_int32
    in
    Caml.Hashtbl.add tdescr ty_int32 tydescr_int32;
    (* Uint32 *)
    let primtydescr_uint32 =
      Llvm.define_global
        (tempname "TyDescr_Uint32_Prim")
        (Llvm.const_named_struct tydescr_prim_ty
           [| qi (enum_prims (Uint_typ Bits32)); qi (enum_bitwidth Bits32) |])
        llmod
    in
    let ty_uint32 = PrimType (Uint_typ Bits32) in
    let%bind tydescr_uint32 =
      wrap_primty (tempname "TyDescr_Uint32") ty_uint32 primtydescr_uint32
    in
    Caml.Hashtbl.add tdescr ty_uint32 tydescr_uint32;
    (* Int64 *)
    let primtydescr_int64 =
      Llvm.define_global
        (tempname "TyDescr_Int64_Prim")
        (Llvm.const_named_struct tydescr_prim_ty
           [| qi (enum_prims (Int_typ Bits64)); qi (enum_bitwidth Bits64) |])
        llmod
    in
    let ty_int64 = PrimType (Int_typ Bits64) in
    let%bind tydescr_int64 =
      wrap_primty (tempname "TyDescr_Int64") ty_int64 primtydescr_int64
    in
    Caml.Hashtbl.add tdescr ty_int64 tydescr_int64;
    (* Uint64 *)
    let primtydescr_uint64 =
      Llvm.define_global
        (tempname "TyDescr_Uint64_Prim")
        (Llvm.const_named_struct tydescr_prim_ty
           [| qi (enum_prims (Uint_typ Bits64)); qi (enum_bitwidth Bits64) |])
        llmod
    in
    let ty_uint64 = PrimType (Uint_typ Bits64) in
    let%bind tydescr_uint64 =
      wrap_primty (tempname "TyDescr_Uint64") ty_uint64 primtydescr_uint64
    in
    Caml.Hashtbl.add tdescr ty_uint64 tydescr_uint64;
    (* Int128 *)
    let primtydescr_int128 =
      Llvm.define_global
        (tempname "TyDescr_Int128_Prim")
        (Llvm.const_named_struct tydescr_prim_ty
           [| qi (enum_prims (Int_typ Bits128)); qi (enum_bitwidth Bits128) |])
        llmod
    in
    let ty_int128 = PrimType (Int_typ Bits128) in
    let%bind tydescr_int128 =
      wrap_primty (tempname "TyDescr_Int128") ty_int128 primtydescr_int128
    in
    Caml.Hashtbl.add tdescr ty_int128 tydescr_int128;
    (* Uint128 *)
    let primtydescr_uint128 =
      Llvm.define_global
        (tempname "TyDescr_Uint128_Prim")
        (Llvm.const_named_struct tydescr_prim_ty
           [| qi (enum_prims (Uint_typ Bits128)); qi (enum_bitwidth Bits128) |])
        llmod
    in
    let ty_uint128 = PrimType (Uint_typ Bits128) in
    let%bind tydescr_uint128 =
      wrap_primty (tempname "TyDescr_Uint128") ty_uint128 primtydescr_uint128
    in
    Caml.Hashtbl.add tdescr ty_uint128 tydescr_uint128;
    (* Int256 *)
    let primtydescr_int256 =
      Llvm.define_global
        (tempname "TyDescr_Int256_Prim")
        (Llvm.const_named_struct tydescr_prim_ty
           [| qi (enum_prims (Int_typ Bits256)); qi (enum_bitwidth Bits256) |])
        llmod
    in
    let ty_int256 = PrimType (Int_typ Bits256) in
    let%bind tydescr_int256 =
      wrap_primty (tempname "TyDescr_Int256") ty_int256 primtydescr_int256
    in
    Caml.Hashtbl.add tdescr ty_int256 tydescr_int256;
    (* Uint256 *)
    let primtydescr_uint256 =
      Llvm.define_global
        (tempname "TyDescr_Uint256_Prim")
        (Llvm.const_named_struct tydescr_prim_ty
           [| qi (enum_prims (Uint_typ Bits256)); qi (enum_bitwidth Bits256) |])
        llmod
    in
    let ty_uint256 = PrimType (Uint_typ Bits256) in
    let%bind tydescr_uint256 =
      wrap_primty (tempname "TyDescr_Uint256") ty_uint256 primtydescr_uint256
    in
    Caml.Hashtbl.add tdescr ty_uint256 tydescr_uint256;
    (* String *)
    let primtydescr_string =
      Llvm.define_global
        (tempname "TyDescr_String_Prim")
        (Llvm.const_named_struct tydescr_prim_ty
           [| qi (enum_prims String_typ); qi 0 |])
        llmod
    in
    let ty_string = PrimType String_typ in
    let%bind tydescr_string =
      wrap_primty (tempname "TyDescr_String") ty_string primtydescr_string
    in
    Caml.Hashtbl.add tdescr ty_string tydescr_string;
    (* Bystr *)
    let primtydescr_bystr =
      Llvm.define_global
        (tempname "TyDescr_Bystr_Prim")
        (Llvm.const_named_struct tydescr_prim_ty
           [| qi (enum_prims Bystr_typ); qi 0 |])
        llmod
    in
    let ty_bystr = PrimType Bystr_typ in
    let%bind tydescr_bystr =
      wrap_primty (tempname "TyDescr_Bystr") ty_bystr primtydescr_bystr
    in
    Caml.Hashtbl.add tdescr ty_bystr tydescr_bystr;
    (* BystrX *)
    let%bind _ =
      iterM specls.bystrspecl ~f:(fun x ->
          let primtydescr_bystrx =
            Llvm.define_global
              (tempname (sprintf "TyDescr_Bystr%d_Prim" x))
              (Llvm.const_named_struct tydescr_prim_ty
                 [| qi (enum_prims (Bystrx_typ x)); qi x |])
              llmod
          in
          let ty_bystrx = PrimType (Bystrx_typ x) in
          let%bind tydescr_bystrx =
            wrap_primty
              (tempname (sprintf "TyDescr_Bystr%d" x))
              ty_bystrx primtydescr_bystrx
          in
          Caml.Hashtbl.add tdescr ty_bystrx tydescr_bystrx;
          pure ())
    in

    (* 3. Declare type descriptors for ADTs and Maps. *)
    (*
      struct String {
        uint8_t *m_buffer;
        uint32_t m_length;
      }
      // Describe a constructor.
      struct Constr {
        // Constructor name.
        String m_cName;
        // Number of arguments to this constructor.
        uint32_t m_numArgs;
        // The type of each argument of this constructor.
        Typ **m_args;
      };
      // Describe an ADT specialization.
      struct Specl {
        // Number of type arguments to the ADT.
        uint32_t m_numTArgs;
        // Types used to instantiate the ADT.
        // Needed to serialize the ADT with full type information.
        Typ **m_TArgs;
        // The constructors for this specialization. The number of
        // constructors is same for all specializations, and hence
        // defined outside in ADTTyp.
        Constr **m_constrs;
        // Pointer to the parent ADTTyp. Necessary when only a Specl is known.
        ADTTyp *m_parent;
      };
      struct ADTTyp {
        // The ADT name
        String m_tName;
        // Number of constructors
        uint32_t m_numConstrs;
        // Number of type specializations
        uint32_t m_numSpecls;
        // An array of all specializations.
        Specl **m_specls;
      };
    *)
    let%bind tydescr_string_ty = scilla_bytes_ty llmod "TyDescrString" in
    (* Declare an opaque type for struct Specl. *)
    let%bind tydescr_specl_ty =
      named_struct_type ~is_opaque:true llmod
        (tempname "TyDescrTy_ADTTyp_Specl")
        [||]
    in
    (* Define type for struct ADTTyp *)
    let%bind tydescr_adt_ty =
      named_struct_type llmod
        (tempname "TyDescrTy_ADTTyp")
        [|
          tydescr_string_ty;
          (* m_tName *)
          i32_ty;
          (* m_numConstrs *)
          i32_ty;
          (* m_numSpecls *)
          ptr_ptr_ty tydescr_specl_ty (* m_specls *);
        |]
    in
    (* Define a struct for struct Constr *)
    let%bind tydescr_constr_ty =
      named_struct_type llmod
        (tempname "TyDescrTy_ADTTyp_Constr")
        [|
          tydescr_string_ty;
          (* m_cName *)
          i32_ty;
          (* m_numArgs *)
          ptr_ptr_ty tydescr_ty (* Typ** m_args *);
        |]
    in
    (* Now fill the body for struct Specl. *)
    Llvm.struct_set_body tydescr_specl_ty
      [|
        i32_ty (* m_numTArgs *);
        ptr_ptr_ty tydescr_ty;
        (* Typ** m_TArgs *)
        ptr_ptr_ty tydescr_constr_ty;
        (* Constr** m_constrs *)
        Llvm.pointer_type tydescr_adt_ty
        (* ADTType* m_parent *);
      |]
      false;
    (* Declare type descriptors for all ADTs. *)
    let%bind _ =
      iterM specls.adtspecl ~f:(fun (tname, specls) ->
          iterM specls ~f:(fun specl ->
              let ty_adt = ADT (tname, specl) in
              let%bind tname' = type_instantiated_adt_name "" tname specl in
              let tydescr_adt =
                declare_global ~unnamed:true ~const:true tydescr_ty
                  (tempname ("TyDescr_ADT_" ^ tname'))
                  llmod
              in
              Caml.Hashtbl.add tdescr ty_adt tydescr_adt;
              pure ()))
    in
    (* Define a descriptor for MapTyp *)
    let%bind tydescr_map_ty =
      named_struct_type ~is_opaque:true llmod (tempname "TyDescr_MapTyp") [||]
    in
    Llvm.struct_set_body tydescr_map_ty
      [|
        Llvm.pointer_type tydescr_ty;
        (* Typ* m_keyTyp *)
        Llvm.pointer_type tydescr_ty (* Typ* m_valTyp *);
      |]
      false;
    (* Declare type descriptors for all Maps. *)
    let%bind _ =
      iterM specls.mapspecl ~f:(fun (kt, vt) ->
          let ty_map = MapType (kt, vt) in
          let tydescr_map =
            declare_global ~unnamed:true ~const:true tydescr_ty
              (tempname "TyDescr_Map") llmod
          in
          Caml.Hashtbl.add tdescr ty_map tydescr_map;
          pure ())
    in

    let define_adtname name =
      let chars =
        define_global ~unnamed:true ~const:true
          (tempname ("TyDescr_ADT_" ^ name))
          (Llvm.const_string llctx name)
          llmod
      in
      build_scilla_bytes llctx tydescr_string_ty chars
    in
    let tempname_adt tname specl struct_name =
      let%bind s = type_instantiated_adt_name "" tname specl in
      pure @@ tempname ("TyDescr_" ^ s ^ "_" ^ struct_name)
    in

    (* 4. Fill up the type descriptors for each ADT. *)
    let%bind _ =
      iterM specls.adtspecl ~f:(fun (tname, specls) ->
          let%bind adt = DataTypeDictionary.lookup_name tname in
          let%bind tydescr_adt_decl =
            let%bind tvname = tempname_adt tname [] "ADTTyp" in
            pure
              (declare_global ~unnamed:true ~const:true tydescr_adt_ty tvname
                 llmod)
          in
          let%bind tydescr_specls_specls =
            mapM specls ~f:(fun specl ->
                let ty_adt = ADT (tname, specl) in
                let%bind tydescr_constrs =
                  mapM adt.tconstr ~f:(fun c ->
                      let%bind argts =
                        TypeUtilities.constr_pattern_arg_types ty_adt c.cname
                      in
                      let%bind argts_ll =
                        mapM argts ~f:(fun t -> resolve_typdescr tdescr t)
                      in
                      let%bind argts_ll_array =
                        let%bind tvname =
                          tempname_adt
                            (tname ^ "_" ^ c.cname)
                            specl "Constr_m_args"
                        in
                        pure
                        @@ define_global ~unnamed:true ~const:true tvname
                             (Llvm.const_array
                                (Llvm.pointer_type tydescr_ty)
                                (Array.of_list argts_ll))
                             llmod
                      in
                      let num_args = List.length argts in
                      let%bind cname_val = define_adtname c.cname in
                      let tydescr_constr =
                        Llvm.const_named_struct tydescr_constr_ty
                          [|
                            cname_val;
                            qi num_args;
                            Llvm.const_bitcast argts_ll_array
                              (ptr_ptr_ty tydescr_ty);
                          |]
                      in
                      let%bind constr_gname =
                        tempname_adt
                          (tname ^ "_" ^ c.cname)
                          specl "ADTTyp_Constr"
                      in
                      pure
                      @@ define_global ~unnamed:true ~const:true constr_gname
                           tydescr_constr llmod)
                in
                (* We now have all the constructors for this specialization.
                 * Create the Specl descriptor. *)
                let%bind tydescr_constrs_array =
                  let%bind tvname =
                    tempname_adt tname specl "ADTTyp_Specl_m_constrs"
                  in
                  pure
                  @@ define_global ~unnamed:true ~const:true tvname
                       (Llvm.const_array
                          (Llvm.pointer_type tydescr_constr_ty)
                          (Array.of_list tydescr_constrs))
                       llmod
                in
                let num_targs = List.length specl in
                let%bind tydescr_targs_ll =
                  mapM specl ~f:(fun t -> resolve_typdescr tdescr t)
                in
                let%bind tydescr_targs_array =
                  let%bind tvname =
                    tempname_adt tname specl "ADTTyp_Specl_m_TArgs"
                  in
                  pure
                  @@ define_global ~unnamed:true ~const:true tvname
                       (Llvm.const_array
                          (Llvm.pointer_type tydescr_ty)
                          (Array.of_list tydescr_targs_ll))
                       llmod
                in
                let tydescr_specl =
                  Llvm.const_named_struct tydescr_specl_ty
                    [|
                      qi num_targs;
                      Llvm.const_bitcast tydescr_targs_array
                        (ptr_ptr_ty tydescr_ty);
                      Llvm.const_bitcast tydescr_constrs_array
                        (ptr_ptr_ty tydescr_constr_ty);
                      tydescr_adt_decl;
                    |]
                in
                let%bind tydescr_specl_ptr =
                  let%bind tvname = tempname_adt tname specl "ADTTyp_Specl" in
                  pure
                    (define_global ~unnamed:true ~const:true tvname
                       tydescr_specl llmod)
                in
                pure (tydescr_specl_ptr, specl))
          in
          let tydescr_specl_ptrs, _ = List.unzip tydescr_specls_specls in
          (* We have all specializations for this ADT. Create the ADTTyp struct. *)
          let%bind tydescr_specls_array =
            let%bind tvname = tempname_adt tname [] "ADTTyp_m_specls" in
            pure
            @@ define_global ~unnamed:true ~const:true tvname
                 (Llvm.const_array
                    (Llvm.pointer_type tydescr_specl_ty)
                    (Array.of_list tydescr_specl_ptrs))
                 llmod
          in
          let num_constrs = List.length adt.tconstr in
          let num_specls = List.length tydescr_specl_ptrs in
          let%bind tname_val = define_adtname tname in
          let tydescr_adt =
            Llvm.const_named_struct tydescr_adt_ty
              [|
                tname_val;
                qi num_constrs;
                qi num_specls;
                Llvm.const_bitcast tydescr_specls_array
                  (ptr_ptr_ty tydescr_specl_ty);
              |]
          in
          (* We only declared a global for the ADTTyp earlier, initialize it now. *)
          Llvm.set_initializer tydescr_adt tydescr_adt_decl;
          (* Initialize the type declaration for each specialization. *)
          iterM tydescr_specls_specls ~f:(fun (tydescr_specl_ptr, specl) ->
              let tydescr_specl_ptr' =
                Llvm.const_bitcast tydescr_specl_ptr (void_ptr_type llctx)
              in
              let ty_adt = ADT (tname, specl) in
              let%bind tydescr_ty_decl = resolve_typdescr tdescr ty_adt in
              (* Wrap tydescr_adt_ptr in struct Typ. *)
              let%bind adtenum = enum_typ ty_adt in
              Llvm.set_initializer
                (Llvm.const_named_struct tydescr_ty
                   [| qi adtenum; tydescr_specl_ptr' |])
                tydescr_ty_decl;
              pure ()))
    in

    (* 4. Fill up the type descriptors for each MapType. *)
    let%bind _ =
      iterM specls.mapspecl ~f:(fun (kt, vt) ->
          let ty_map = MapType (kt, vt) in
          let%bind tydescr_ty_decl = resolve_typdescr tdescr ty_map in
          let%bind kt_ll = resolve_typdescr tdescr kt in
          let%bind vt_ll = resolve_typdescr tdescr vt in
          let tydescr_map_ptr =
            define_global ~unnamed:true ~const:true
              (tempname "TyDescr_MapTyp")
              (Llvm.const_named_struct tydescr_map_ty [| kt_ll; vt_ll |])
              llmod
          in
          let tydescr_map_ptr' =
            Llvm.const_bitcast tydescr_map_ptr (void_ptr_type llctx)
          in
          let%bind mapenum = enum_typ ty_map in
          Llvm.set_initializer
            (Llvm.const_named_struct tydescr_ty
               [| qi mapenum; tydescr_map_ptr' |])
            tydescr_ty_decl;
          pure ())
    in

    (* Finally return our mapping for clients to resolve later. *)
    pure tdescr

  (* Given a type, call update_specl_dict for it and all its constituent types. *)
  let gather_specls_ty specls ty =
    let rec go inscope specls ty =
      (* If we're already processing ty, do not go further. *)
      if List.mem inscope ty ~equal:TypeUtilities.([%equal: typ]) then specls
      else
        match ty with
        | PrimType (Bystrx_typ _) -> update_specl_dict specls ty
        | PrimType _ | Unit | TypeVar _ -> specls
        | MapType (kt, vt) ->
            let specls_this = update_specl_dict specls ty in
            let specls' = go (ty :: inscope) specls_this kt in
            go (ty :: inscope) specls' vt
        | FunType (argts, rett) ->
            List.fold ~init:specls (rett :: argts) ~f:(go (ty :: inscope))
        | ADT (_, argts) ->
            let specls' = update_specl_dict specls ty in
            List.fold ~init:specls' argts ~f:(go (ty :: inscope))
        | PolyFun (_, t) -> go (ty :: inscope) specls t
    in
    go [] specls ty

  let rec gather_specls_stmts specls stmts =
    (* We mostly gather from bindings (definitions, arguments etc). *)
    foldM stmts ~init:specls ~f:(fun specls (stmt, _) ->
        match stmt with
        | Bind (x, _)
        | LoadEnv (x, _, _)
        | ReadFromBC (x, _)
        | LocalDecl x
        | LibVarDecl x ->
            let%bind t = id_typ x in
            pure (gather_specls_ty specls t)
        | MatchStmt (_, clauses, jopt) ->
            let%bind specls_jopt =
              match jopt with
              | Some (_, j) -> gather_specls_stmts specls j
              | None -> pure specls
            in
            foldM clauses ~init:specls_jopt ~f:(fun specls (pat, body) ->
                let%bind specls_bounds =
                  foldM (get_spattern_bounds pat) ~init:specls
                    ~f:(fun specls v ->
                      let%bind t = id_typ v in
                      pure (gather_specls_ty specls t))
                in
                gather_specls_stmts specls_bounds body)
        | JumpStmt _ | AcceptPayment | SendMsgs _ | CreateEvnt _
        (* Fields are gathered separately. *)
        | MapUpdate _ | MapGet _ | Load _ | Store _ | CallProc _ | Throw _
        | Ret _ | StoreEnv _ | AllocCloEnv _ ->
            pure specls)

  (* Gather all ADT specializations in a closure. *)
  let gather_specls_clo specls clo =
    let ts = !(clo.thisfun).fretty :: snd (List.unzip !(clo.thisfun).fargs) in
    let specls' = List.fold ts ~init:specls ~f:gather_specls_ty in
    gather_specls_stmts specls' !(clo.thisfun).fbody

  let generate_type_descr_cmod llmod topclos cmod =
    (* Build a list of all ADT specializations in topclos+cmod. *)
    let%bind specls_clos =
      foldM topclos ~init:empty_specl_dict ~f:(fun specls clo ->
          gather_specls_clo specls clo)
    in
    (* Library statements *)
    let%bind specls_libs = gather_specls_stmts specls_clos cmod.lib_stmts in
    (* Contract parameters *)
    let specls_params =
      List.fold cmod.contr.cparams ~init:specls_libs ~f:(fun specls (_, pt) ->
          gather_specls_ty specls pt)
    in
    (* Fields *)
    let%bind specls_fields =
      foldM cmod.contr.cfields ~init:specls_params
        ~f:(fun specls (_, ft, finit) ->
          let specls_ft = gather_specls_ty specls ft in
          gather_specls_stmts specls_ft finit)
    in
    (* Procedures and transitions. *)
    let%bind specls_comps =
      foldM cmod.contr.ccomps ~init:specls_fields ~f:(fun specls c ->
          let specls_comp_params =
            List.fold c.comp_params ~init:specls ~f:(fun specls (_, pt) ->
                gather_specls_ty specls pt)
          in
          gather_specls_stmts specls_comp_params c.comp_body)
    in
    generate_typedescr llmod specls_comps

  let generate_type_descr_stmts_wrapper llmod topclos stmts =
    (* Build a list of all ADT specializations in topclos+stmts. *)
    let%bind specls_clos =
      foldM topclos ~init:empty_specl_dict ~f:(fun specls clo ->
          gather_specls_clo specls clo)
    in
    let%bind specls_stmts = gather_specls_stmts specls_clos stmts in
    generate_typedescr llmod specls_stmts

  let build_tydescr_table llmod ~global_array_name ~global_array_length_name
      tdescr =
    let ctx = Llvm.module_context llmod in
    match Llvm.type_by_name llmod tydescrty_typ_name with
    | None ->
        fail0
          (sprintf
             "GenLlvm: TyDescr: Type %s to desribe types not found in module."
             tydescrty_typ_name)
    | Some llty ->
        (* Build a constant array of llty. *)
        let tdescrs = Caml.Array.of_seq (Caml.Hashtbl.to_seq_values tdescr) in
        let tdescr_table = Llvm.const_array llty tdescrs in
        let tdescr_global_array =
          define_global global_array_name tdescr_table llmod ~const:true
            ~unnamed:false
        in
        let tdescr_global_array_length =
          define_global global_array_length_name
            (Llvm.const_int (Llvm.i32_type ctx) (Caml.Hashtbl.length tdescr))
            llmod ~const:true ~unnamed:false
        in
        pure (tdescr_global_array, tdescr_global_array_length)
end
