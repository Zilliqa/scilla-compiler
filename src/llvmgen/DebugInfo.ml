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

(* All functions in this file are NOPs if generate_debuginfo is not enabled.
 * i.e., when generate_debuginfo is not enabled,
 *   - Functions that return an llmetadata value return
 *     Llvm_debuginfo.llmetadata_null().
 *   - Functions that return unit will not have any side effects.
 *)

open Core_kernel
open Scilla_base
open MonadUtil
module Literal = Literal.GlobalLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open UncurriedSyntax
open ClosuredSyntax

type scilla_dibuilder = DIEnabled of Llvm_debuginfo.lldibuilder | DIDisabled

let generate_debuginfo = ref false

let create_dibuilder llmod =
  if !generate_debuginfo then DIEnabled (Llvm_debuginfo.dibuilder llmod)
  else DIDisabled

let finalize_dibuilder = function
  | DIEnabled dibuilder -> Llvm_debuginfo.dibuild_finalize dibuilder
  | DIDisabled -> ()

(* Generate debuginfo common to all programs. *)
let gen_common dibuilder llmod filename =
  match dibuilder with
  | DIEnabled dibuilder ->
      let ctx = Llvm.module_context llmod in
      let di_version_key = "Debug Info Version" in
      let ver =
        Llvm.value_as_metadata
        @@ Llvm.const_int (Llvm.i32_type ctx)
             (Llvm_debuginfo.debug_metadata_version ())
      in
      let () =
        Llvm.add_module_flag llmod Llvm.ModuleFlagBehavior.Warning
          di_version_key ver
      in
      let file_di =
        Llvm_debuginfo.dibuild_create_file dibuilder
          ~filename:(Filename.basename filename)
          ~directory:(Filename.dirname filename)
      in
      let cu_di =
        Llvm_debuginfo.dibuild_create_compile_unit dibuilder
          Llvm_debuginfo.DWARFSourceLanguageKind.C89 ~file_ref:file_di
          ~producer:"Scilla Compiler" ~is_optimized:false ~flags:""
          ~runtime_ver:0 ~split_name:""
          Llvm_debuginfo.DWARFEmissionKind.LineTablesOnly ~dwoid:0
          ~di_inlining:false ~di_profiling:false ~sys_root:"" ~sdk:""
      in
      let _ =
        Llvm_debuginfo.dibuild_create_module dibuilder ~parent_ref:cu_di
          ~name:(Llvm.get_module_identifier llmod)
          ~config_macros:"" ~include_path:"" ~sys_root:""
      in
      ()
  | DIDisabled -> ()

let gen_fun_loc dibuilder ?(is_local_to_unit = true) name (loc : ErrorUtils.loc)
    fllval =
  match dibuilder with
  | DIEnabled dibuilder ->
      let void_dty =
        Llvm_debuginfo.dibuild_create_unspecified_type dibuilder ~name:"void"
      in
      let flags = Llvm_debuginfo.diflags_get Llvm_debuginfo.DIFlag.Zero in
      let file =
        Llvm_debuginfo.dibuild_create_file dibuilder
          ~filename:(Filename.basename loc.fname)
          ~directory:(Filename.dirname loc.fname)
      in
      let ty =
        Llvm_debuginfo.dibuild_create_subroutine_type dibuilder ~file
          ~param_types:[| void_dty |] flags
      in
      let sp =
        Llvm_debuginfo.dibuild_create_function dibuilder ~scope:file ~name
          ~linkage_name:name ~file ~line_no:loc.lnum ~ty ~is_local_to_unit
          ~is_definition:true ~scope_line:loc.lnum ~flags ~is_optimized:false
      in
      let () = Llvm_debuginfo.set_subprogram fllval sp in
      sp
  | DIDisabled -> Llvm_debuginfo.llmetadata_null ()

let gen_fun dibuilder ?(is_local_to_unit = true)
    (fid : Uncurried_Syntax.eannot Identifier.t) fllval =
  let name, loc =
    (Identifier.as_error_string fid, (Identifier.get_rep fid).ea_loc)
  in
  gen_fun_loc dibuilder ~is_local_to_unit name loc fllval

let set_inst_loc llctx scope llinst (loc : ErrorUtils.loc) =
  match Llvm.classify_value llinst with
  | Llvm.ValueKind.Instruction _ ->
      (if !generate_debuginfo then
       let md =
         Llvm_debuginfo.dibuild_create_debug_location llctx ~line:loc.lnum
           ~column:loc.cnum ~scope
       in
       Llvm_debuginfo.instr_set_debug_loc llinst (Some md));
      pure ()
  | _ ->
      fail1
        ~kind:"DebugInfo: set_inst_loc can only be called on LLVM instructions"
        ?inst:None loc

let create_sub_scope dibuilder scope (loc : ErrorUtils.loc) =
  match dibuilder with
  | DIEnabled dibuilder -> (
      match Llvm_debuginfo.di_scope_get_file ~scope with
      | Some file ->
          pure
          @@ Llvm_debuginfo.dibuild_create_lexical_block dibuilder ~scope ~file
               ~line:loc.lnum ~column:loc.cnum
      | None ->
          fail1
            ~kind:
              "DebugInfo: create_sub_scope: Unable to determine file of parent \
               scope"
            ?inst:None loc)
  | DIDisabled -> pure @@ Llvm_debuginfo.llmetadata_null ()
