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

open Core
open Result.Let_syntax
open Syntax
open MonadUtil
open UncurriedSyntax.Uncurried_Syntax
open ClosuredSyntax.CloCnvSyntax
open Datatypes

(* Create a named struct with types from tyarr. *)
let named_struct_type ?(is_packed=false) llmod name tyarr =
  let ctx = Llvm.module_context llmod in
  match Llvm.type_by_name llmod name with
  | Some ty ->
    (* If ty is an opaque type, we fill its body now. *)
    if Llvm.classify_type ty <> Llvm.TypeKind.Struct
    then fail0 (sprintf 
      "GenLlvm: named_struct_type: internal error. Type %s already exists but is not struct." name)
    else (
      if Llvm.is_opaque ty then Llvm.struct_set_body ty tyarr is_packed;
      pure ty
    )
  | None ->
    let t = Llvm.named_struct_type ctx name in
    let _ = Llvm.struct_set_body t tyarr is_packed in
    pure t

let void_ptr_type ctx = Llvm.pointer_type (Llvm.void_type ctx)

(*
 * To avoid ABI complexities, we allow passing by value only
 * when the object size is not larger than two eight-bytes.
 * Otherwise, it needs to be passed in memory (via a pointer).
 * See https://stackoverflow.com/a/42413484/2128804
 *)
let can_pass_by_val dl ty =
  not
    (Llvm.type_is_sized ty &&
      (Int64.compare (Llvm_target.DataLayout.size_in_bits ty dl) (Int64.of_int 128)) > 0
    )


(* Translate Scilla types to LLVM types.
 * In case of ADTs, the LLVM types for each constructor is returned
 * as the second component of the result. In all other cases, the
 * second component of the result is an empty list. *)
let genllvm_typ llmod sty =

  let ctx = Llvm.module_context llmod in
  let i8_type = Llvm.i8_type ctx in
  let dl = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod) in

  (* Create a StructType "type { i8*, i32 }".
   * This type can represent Scilla String and ByStr values.
   * Note: We cannot use LLVM's Array type to represent bytes because
   *       that requires the length to be known at compile time. *)
  let scilla_bytes_ty ty_name =
    let ctx = Llvm.module_context llmod in
    let charp_ty = Llvm.pointer_type i8_type in
    let len_ty = Llvm.i32_type ctx in
    named_struct_type llmod ty_name [|charp_ty;len_ty|]
  in

  (* Given an ADT name or one of it's constructors' and the instantiation types,
   * concatenate them to create a name for the instantiated type. *)
  let type_instantiated_adt_name name ts =
    match ts with
    | [] -> pure name
    | _ ->
      let%bind ts' = mapM ts ~f:(fun t ->
        if TypeUtilities.is_ground_type t
        then pure (pp_typ t)
        else fail0 "GenLlvm: unexpected polymorphic ADT"
      ) in
      pure @@ name ^ "_" ^ (String.concat ~sep:"_" ts')
  in

  let rec go ~inprocess sty =
    match sty with
    | PrimType pty ->
      let%bind llty = (match pty with
        (* Build integer types, by wrapping LLMV's i* type in structs with names. *)
        | Int_typ bw | Uint_typ bw ->
          let bwi = match bw with | Bits32 -> 32 | Bits64 -> 64 | Bits128 -> 128 | Bits256 -> 256 in
          named_struct_type llmod (pp_prim_typ pty) [|Llvm.integer_type ctx bwi|]
        (* An instantiation of scilla_bytes_ty for Scilla String. *)
        | String_typ -> scilla_bytes_ty "String"
        (* An instantiation of scilla_bytes_ty for Scilla Bystr. *)
        | Bystr_typ -> scilla_bytes_ty "Bystr"
        (* ByStrX represented as an LLVM array of length X. *)
        | Bystrx_typ bytes -> pure @@ Llvm.array_type i8_type bytes
        | Msg_typ | Event_typ | Exception_typ | Bnum_typ -> fail0 "GenLlvm: genllvm_prim_typ: unimplemented"
        ) in
      pure (llty, [])
    | ADT (tname, ts) ->
      let%bind name_ll = type_instantiated_adt_name tname ts in
      (* If this type is already being translated, return an opaque type. *)
      if List.exists inprocess ~f:(TypeUtilities.type_equiv sty)
      then pure ((Llvm.named_struct_type ctx name_ll |> Llvm.pointer_type), []) else

      let%bind adt = Datatypes.DataTypeDictionary.lookup_name tname in
      (* Let's get / create the types for each constructed ADTValue. *)
      let%bind cnames_ctrs_ty_ll = mapM adt.tconstr ~f:(fun ct ->
        let%bind arg_types = TypeUtilities.constr_pattern_arg_types sty ct.cname in
        let%bind arg_types_ll = mapM arg_types ~f:(fun t ->
          (* Ensure that we mark sty as "in process" before making the recursive call. *)
          let%bind (llty, _) = go ~inprocess:(sty :: inprocess) t in
          pure llty
        ) in
        (* In addition to the member literal types, we add a tag at the beginning. *)
        let tagged_arg_types_ll = Array.of_list @@ i8_type :: arg_types_ll in
        (* Come up with a name by suffixing the constructor name with the instantiated types. *)
        let%bind cname_ll = type_instantiated_adt_name ct.cname ts in
        let%bind ctr_ty_ll = named_struct_type ~is_packed:true llmod cname_ll tagged_arg_types_ll in
        (* We now have an llvm struct type to represent an object of this constructed type. *)
        pure (ct.cname, Llvm.pointer_type ctr_ty_ll)
      ) in
      let (_, ctrs_ty_ll) = List.unzip cnames_ctrs_ty_ll in
      (* We "union" the types of each constructed object type with a struct type that has a tag
      * at the start, and a list of pointers to each constructed object. The latter is only
      * to be able to verify that the constructor types and the main type are all related.
      * The tag is the only real element that will ever be accessed *)
      let%bind ty_ll = named_struct_type llmod name_ll (Array.of_list (i8_type :: ctrs_ty_ll)) in
      (* The final type will be a pointer to this struct. *)
      pure ((Llvm.pointer_type ty_ll), cnames_ctrs_ty_ll)
    | FunType (argts, rett) ->
      (* We don't know the type of the environment with just the "typ" of a function.
       * We make do with using a "void*" for it instead. *)
      let envty = void_ptr_type ctx in
      let%bind argts_ll = mapM argts ~f:(fun argt ->
        let%bind (argt_ll, _) = go ~inprocess:(sty :: inprocess) argt in
        if can_pass_by_val dl argt_ll then pure argt_ll else pure @@ Llvm.pointer_type argt_ll
      ) in
      let%bind (rett_ll, _) = go ~inprocess:(sty :: inprocess) rett in
      let funty = 
        if can_pass_by_val dl rett_ll
        then
        (* if return is by value, then "retval (envpointer, args ...)" *)
          Llvm.function_type rett_ll (Array.of_list (envty :: argts_ll))
        else
          let argts_final = envty :: (Llvm.pointer_type rett_ll) :: argts_ll in
          (* If return is not by value, then 1. env pointer, 2. ret value pointer, 3. args *)
          Llvm.function_type (Llvm.void_type ctx) (Array.of_list argts_final)
      in
      (* Functions are represented with closures, so return the closure type. *)
      pure (Llvm.struct_type ctx [|Llvm.pointer_type funty;void_ptr_type ctx|], [])
    | MapType _ -> fail0 "GenLlvm: genllvm_typ: MapType not supported yet"
    | PolyFun _ | TypeVar _ | Unit -> fail0 "GenLlvm: genllvm_typ: unsupported type"
  in
  go ~inprocess:[] sty

(* Returns only the first component of genllvm_typ. *)
let genllvm_typ_fst llmod sty =
  let%bind (sty', _) = genllvm_typ llmod sty in
  pure sty'

let rep_typ rep =
  match rep.ea_tp with
  | Some ty -> pure ty
  | None -> fail1 (sprintf "GenLlvm: rep_typ: not type annotated.")
            rep.ea_loc

let id_typ id = rep_typ (get_rep id)

let id_typ_ll llmod id =
  let%bind ty = id_typ id in
  let%bind (llty, _) = genllvm_typ llmod ty in
  pure llty

let ptr_element_type ptr_llty =
  match Llvm.classify_type ptr_llty with
  | Llvm.TypeKind.Pointer -> pure @@ Llvm.element_type ptr_llty
  | _ -> fail0 "GenLlvm: internal error: expected pointer type"

let struct_element_types sty =
  match Llvm.classify_type sty with
  | Llvm.TypeKind.Struct -> pure (Llvm.struct_element_types sty)
  | _ -> fail0 "GenLlvm: internal error: expected struct type"


(* Get the LLVM struct that holds an ADT's constructed object. Get its tag too.
 * Typically used on the output of genllvm_typ for ADT type. *)
let get_ctr_struct adt_llty_map cname =
  match List.Assoc.find adt_llty_map ~equal:(=) cname with
  | Some ptr_llcty -> (* We have a pointer type to the constructor's LLVM type. *)
    let%bind ctr_struct = ptr_element_type ptr_llcty in
    let%bind (adt, _) = DataTypeDictionary.lookup_constructor cname in
    (match List.findi adt.tconstr ~f:(fun _ cn -> cname = cn.cname) with
    | Some (tag, _) -> pure (ctr_struct, tag)
    | None -> fail0 (sprintf "GenLlvm: get_ctr_struct: internal error: constructor %s for adt %s not found" 
                      cname (adt.tname))
    )
  | None -> fail0 (sprintf "GenLlvm get_constr_type: LLVM type for ADT constructor %s not built" cname)

(* Builds type descriptors corresponding to ScillaTypes in SRTL. *)
module TypeDescr = struct

  (* Track instantiations of ADTs. *)
  type adt_specl_dict = (string * (typ list) list) list

  (* For debugging. *)
  let sprint_adt_specl_dict adt_specls =
    String.concat ~sep:"\n" (
      List.map adt_specls ~f:(fun (tname, specls) ->
        (sprintf "%s:\n  " tname) ^
        String.concat ~sep:"\n  " (
          List.map specls ~f:(fun tlist ->
            String.concat ~sep:" " (List.map tlist ~f:pp_typ)
          )
        )
      )
    )

  (* Update "adt_specls" by adding (if not already present) ADT type "ty". *)
  let update_adt_specl_dict (adt_specls : adt_specl_dict) ty =
    (* We only care of storable types. *)
    if not (TypeUtilities.is_storable_type ty) then adt_specls else
    match ty with
    | ADT (tname, tlist) ->
      let (non_this, this_and_rest) = List.split_while adt_specls ~f:(fun (tname', _) -> tname <> tname') in
      (match this_and_rest with
      | (_, this_specls) :: rest ->
        if List.mem this_specls tlist ~equal:TypeUtilities.type_equiv_list
        then adt_specls (* This specialization already exists. *)
        else (tname, tlist :: this_specls) :: (non_this @ rest) (* Add this specialization. *)
      | [] -> (tname, [tlist]) :: adt_specls
      )
    | _ -> adt_specls

  (* Generate type descriptors for SRTL. The working horse of this module. *)
  let generate_typedescr _llmod adt_specls =
    let _ = printf "\nType specialized ADTS:\n%s\n\n" (sprint_adt_specl_dict adt_specls) in
    pure ()

  (* Given a type, call update_adt_specl_dict for it and all its constituent types. *)
  let gather_adt_specls_ty adt_specls ty =
    let rec go inscope adt_specls ty =
      (* If we're already processing ty, do not go further. *)
      if List.mem inscope ty ~equal:TypeUtilities.type_equiv then adt_specls else
      match ty with
      | PrimType _ | Unit | TypeVar _ -> adt_specls
      | MapType (kt, vt) ->
        let adt_specls' = go (ty :: inscope) adt_specls kt in
        go (ty :: inscope) adt_specls' vt
      | FunType (argts, rett) ->
        List.fold ~init:adt_specls (rett::argts) ~f:(go (ty::inscope))
      | ADT (_, argts) ->
        let adt_specls' = update_adt_specl_dict adt_specls ty in
        List.fold ~init:adt_specls' argts ~f:(go (ty::inscope))
      | PolyFun (_, t) -> go (ty :: inscope) adt_specls t
    in
    go [] adt_specls ty

  let rec gather_adt_specls_stmts adt_specls stmts =
    (* We mostly gather from bindings (definitions, arguments etc). *)
    foldM stmts ~init:adt_specls ~f:(fun adt_specls (stmt, _) ->
      match stmt with
      | Bind (x, _) | LoadEnv (x, _, _) | ReadFromBC (x, _) | LocalDecl x ->
        let%bind t = id_typ x in
        pure (gather_adt_specls_ty adt_specls t)
      | MatchStmt (_, clauses, jopt) ->
        let%bind adt_specls_jopt =
          (match jopt with
          | Some (_, j) -> gather_adt_specls_stmts adt_specls j
          | None -> pure adt_specls
          )
        in
        foldM clauses ~init:adt_specls_jopt ~f:(fun adt_specls (pat, body) ->
          let%bind adt_specls_bounds =
            foldM (get_spattern_bounds pat) ~init:adt_specls ~f:(fun adt_specls v ->
              let%bind t = id_typ v in
              pure (gather_adt_specls_ty adt_specls t)
          ) in
          gather_adt_specls_stmts adt_specls_bounds body
        )
      | JumpStmt _ | AcceptPayment | SendMsgs _ | CreateEvnt _ 
      (* Fields are gathered separately. *)
      | MapUpdate _ | MapGet _ | Load _ | Store _
      | CallProc _ | Throw _ | Ret _ | StoreEnv _ | AllocCloEnv _ -> pure adt_specls
    )

  (* Gather all ADT specializations in a closure. *)
  let gather_adt_specls_clo adt_specls clo =
    let ts = !(clo.thisfun).fretty :: (snd (List.unzip !(clo.thisfun).fargs)) in
    let adt_specls' = List.fold ts~init:adt_specls ~f:gather_adt_specls_ty in
    gather_adt_specls_stmts adt_specls' !(clo.thisfun).fbody

  (* Generate type descriptors in a contract module. *)
  (* TODO: See if monomorphize can do this and update DataTypeDictionary. *)
  let generate_type_descr_cmod llmod topclos cmod =
    (* Build a list of all ADT specializations in topclos+cmod. *)
    let%bind adt_specls_clos =
      foldM topclos ~init:[] ~f:(fun adt_specls clo -> gather_adt_specls_clo adt_specls clo)
    in
    (* Library statements *)
    let%bind adt_specls_libs = gather_adt_specls_stmts adt_specls_clos cmod.lib_stmts in
    (* Contract parameters *)
    let adt_specls_params =
      List.fold cmod.contr.cparams ~init:adt_specls_libs 
        ~f:(fun adt_specls (_, pt) -> gather_adt_specls_ty adt_specls pt)
    in
    (* Fields *)
    let%bind adt_specls_fields = foldM cmod.contr.cfields ~init:adt_specls_params
    ~f:(fun adt_specls (_, ft, finit) ->
      let adt_specls_ft = gather_adt_specls_ty adt_specls ft in
      gather_adt_specls_stmts adt_specls_ft finit
    ) in
    (* Procedures and transitions. *)
    let%bind adt_specls_comps = foldM cmod.contr.ccomps ~init:adt_specls_fields
    ~f:(fun adt_specls c ->
        let adt_specls_comp_params =
          List.fold c.comp_params ~init:adt_specls
          ~f:(fun adt_specls (_, pt) -> gather_adt_specls_ty adt_specls pt)
        in
        gather_adt_specls_stmts adt_specls_comp_params c.comp_body
    ) in
    generate_typedescr llmod adt_specls_comps

  (* Generate type descriptors for a standalone sequence of statements. *)
  let generate_type_descr_stmts_wrapper llmod topclos stmts =
    (* Build a list of all ADT specializations in topclos+stmts. *)
    let%bind adt_specls_clos =
      foldM topclos ~init:[] ~f:(fun adt_specls clo -> gather_adt_specls_clo adt_specls clo)
    in
    let%bind adt_specls_stmts = gather_adt_specls_stmts adt_specls_clos stmts in
    generate_typedescr llmod adt_specls_stmts

end
