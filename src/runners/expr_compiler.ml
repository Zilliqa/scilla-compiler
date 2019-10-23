open Core
open Printf
open Syntax
open ParserUtil
open RunnerUtil
open DebugMessage
open Result.Let_syntax
open PatternChecker
open PrettyPrinters
open RecursionPrinciples

module ParsedSyntax = ParserUtil.ParsedSyntax
module PSRep = ParserRep
module PERep = ParserRep
  
module TC = TypeChecker.ScillaTypechecker (PSRep) (PERep)
module TCSRep = TC.OutputSRep
module TCERep = TC.OutputERep

module PM_Checker = ScillaPatternchecker (TCSRep) (TCERep)

module AnnExpl = AnnotationExplicitizer.ScillaCG_AnnotationExplicitizer (TCSRep) (TCERep)
module DCE = DCE.ScillaCG_Dce
module Mmph = Monomorphize.ScillaCG_Mmph
module FlatPat = FlattenPatterns.ScillaCG_FlattenPat
module ScopingRename = ScopingRename.ScillaCG_ScopingRename
module CloCnv = ClosureConversion.ScillaCG_CloCnv


(* Check that the expression parses *)
let check_parsing filename = 
    match FrontEndParser.parse_file ScillaParser.Incremental.exp_term filename with
    | Error e -> fatal_error e
    | Ok e ->
        plog @@ sprintf
          "\n[Parsing]:\nExpression in [%s] is successfully parsed.\n" filename;
        e

(* Type check the expression with external libraries *)
let check_typing e elibs gas_limit =
  let checker =
    let open TC in
    let open TC.TypeEnv in
    let rec_lib = { ParsedSyntax.lname = asId "rec_lib" ;
                    ParsedSyntax.lentries = recursion_principles } in
    let%bind ((_typed_rec_libs, tenv0), gas_rem) = type_library TEnv.mk rec_lib gas_limit in
    (* Step 1: Type check external libraries *)
    let%bind (_, tenv1, gas_rem) = type_libraries elibs tenv0 gas_rem in
    type_expr tenv1 e gas_rem
  in
  match checker with
  | Error (e, remaining_gas) -> fatal_error_gas e remaining_gas
  (* TODO: Convey remaining_gas in the final output. *)
  | Ok (e', _remaining_gas) -> e'

let check_patterns e =
  match PM_Checker.pm_check_expr e with
  | Error e -> fatal_error e
  | Ok e' -> e'

let transform_explicitize_annots e =
  match AnnExpl.explicitize_expr_wrapper e with
  | Error e -> fatal_error e
  | Ok e' -> e'

let transform_dce e =
  DCE.expr_dce_wrapper e

let transform_monomorphize e =
  match Mmph.monomorphize_expr_wrapper e with
  | Error e -> fatal_error e
  | Ok e' -> e'

let transform_flatpat e =
  match FlatPat.flatpat_expr_wrapper e with
  | Error e -> fatal_error e
  | Ok e' -> e'

let transform_scoping_rename e =
  ScopingRename.scoping_rename_expr_wrapper e

let transform_clocnv e =
  match CloCnv.clocnv_expr_wrapper e with
  | Error e -> fatal_error e
  | Ok e' -> e'

let () =
    let cli = parse_cli () in
    let open GlobalConfig in
    StdlibTracker.add_stdlib_dirs cli.stdlib_dirs;
    set_debug_level Debug_None;
    let filename = cli.input_file in
    let gas_limit = cli.gas_limit in
    let e = check_parsing filename in
    (* Get list of stdlib dirs. *)
    let lib_dirs = StdlibTracker.get_stdlib_dirs() in
    if lib_dirs = [] then stdlib_not_found_err ();
    (* Import all libs. *)
    let std_lib = import_all_libs lib_dirs  in
    let typed_e =  check_typing e std_lib gas_limit in
    let _ = check_patterns typed_e in
    let ea_e = transform_explicitize_annots typed_e in
    let dce_e = transform_dce ea_e in
    let monomorphized_e = transform_monomorphize dce_e in
    let sr_e = transform_scoping_rename monomorphized_e in
    let flatpat_e = transform_flatpat sr_e in
    let clocnv_e = transform_clocnv flatpat_e in
    (* Print the closure converted AST. *)
    Printf.printf "Closure converted AST:\n%s\n" (ClosuredSyntax.CloCnvSyntax.pp_stmts_wrapper clocnv_e)
