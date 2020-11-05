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
module Literal = Literal.FlattenedLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open UncurriedSyntax
open ClosuredSyntax

let generate_debug_info = true

(* Generate debuginfo common to all programs. *)
let gen_common dibuilder llmod filename =
  if generate_debug_info then
    let ctx = Llvm.module_context llmod in
    let di_version_key = "Debug Info Version" in
    let ver =
      Llvm.value_as_metadata
      @@ Llvm.const_int (Llvm.i32_type ctx)
           (Llvm_debuginfo.debug_metadata_version ())
    in
    let () =
      Llvm.add_module_flag llmod Llvm.ModuleFlagBehaviour.Warning di_version_key
        ver
    in
    let file_di =
      Llvm_debuginfo.dibuild_create_file dibuilder
        ~filename:(Filename.basename filename)
        ~directory:(Filename.dirname filename)
    in
    let cu_di =
      Llvm_debuginfo.dibuild_create_compile_unit dibuilder
        Llvm_debuginfo.DWARFSourceLanguageKind.C89 ~file_ref:file_di
        ~producer:"Scilla Compiler" ~is_optimized:false ~flags:"" ~runtime_ver:0
        ~split_name:"" Llvm_debuginfo.DWARFEmissionKind.LineTablesOnly ~dwoid:0
        ~di_inlining:false ~di_profiling:false
    in
    let _ =
      Llvm_debuginfo.dibuild_create_module dibuilder ~parent_ref:cu_di
        ~name:"scilla_expr" ~config_macros:"" ~include_path:"" ~sys_root:""
    in
    file_di
  else Llvm_debuginfo.llmetadata_null ()

let gen_fun dibuilder file ?(is_local_to_unit = true)
    (fid : Uncurried_Syntax.eannot Identifier.t) fllval =
  let void_dty =
    Llvm_debuginfo.dibuild_create_unspecified_type dibuilder ~name:"void"
  in
  let flags = Llvm_debuginfo.diflags_get Llvm_debuginfo.DIFlag.Zero in
  let ty =
    Llvm_debuginfo.dibuild_create_subroutine_type dibuilder ~file
      ~param_types:[| void_dty |] flags
  in
  let name, loc = (Identifier.get_id fid, (Identifier.get_rep fid).ea_loc) in
  let sp =
    Llvm_debuginfo.dibuild_create_function dibuilder ~scope:file ~name
      ~linkage_name:name ~file ~line_no:loc.lnum ~ty ~is_local_to_unit
      ~is_definition:true ~scope_line:loc.lnum ~flags ~is_optimized:false
  in
  let () = Llvm_debuginfo.set_subprogram fllval sp in
  sp

let set_inst_loc llctx scope llinst (loc : ErrorUtils.loc) =
  let md =
    Llvm_debuginfo.dibuild_create_debug_location llctx ~line:loc.lnum
      ~column:loc.cnum ~scope
  in
  Llvm_debuginfo.instruction_set_debug_loc llinst md
