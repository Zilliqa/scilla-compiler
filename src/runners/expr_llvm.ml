open Core
open Printf
open Scilla_base
module Literal = Literal.FlattenedLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open ParserUtil
open RunnerUtil
open DebugMessage
open Result.Let_syntax
open PatternChecker
open PrettyPrinters
open RecursionPrinciples
open ErrorUtils
open MonadUtil
module Parser = ScillaParser.Make (ParserSyntax)
module PSRep = ParserRep
module PERep = ParserRep
module TC = TypeChecker.ScillaTypechecker (PSRep) (PERep)
module TCSRep = TC.OutputSRep
module TCERep = TC.OutputERep
module PM_Checker = ScillaPatternchecker (TCSRep) (TCERep)
module SG = Gas.ScillaGas (TCSRep) (TCERep)

module AnnExpl =
  AnnotationExplicitizer.ScillaCG_AnnotationExplicitizer (TCSRep) (TCERep)

module DCE = DCE.ScillaCG_Dce
module Mmph = Monomorphize.ScillaCG_Mmph
module FlatPat = FlattenPatterns.ScillaCG_FlattenPat
module ScopingRename = ScopingRename.ScillaCG_ScopingRename
module Uncurry = Uncurry.ScillaCG_Uncurry
module CloCnv = ClosureConversion.ScillaCG_CloCnv

(* Check that the expression parses *)
let check_parsing filename =
  match FrontEndParser.parse_file Parser.Incremental.exp_term filename with
  | Error e -> fatal_error e
  | Ok e ->
      plog
      @@ sprintf "\n[Parsing]:\nExpression in [%s] is successfully parsed.\n"
           filename;
      e

(* Type check the expression with external libraries *)
let check_typing e elibs gas_limit =
  let checker =
    let open TC in
    let open TC.TypeEnv in
    let rec_lib =
      {
        ParserSyntax.lname = Identifier.mk_loc_id "rec_lib";
        ParserSyntax.lentries = recursion_principles;
      }
    in
    let tenv0 = TEnv.mk () in
    let%bind typed_rlibs, gas_rem = type_library tenv0 rec_lib gas_limit in
    (* Step 1: Type check external libraries *)
    let%bind typed_elibs, gas_rem = type_libraries elibs tenv0 gas_rem in
    let%bind typed_expr, gas_rem = type_expr e tenv0 init_gas_kont gas_rem in
    Ok ((typed_rlibs, typed_elibs, typed_expr), gas_rem)
  in
  match checker with
  | Error ((_, e), remaining_gas) -> fatal_error_gas e remaining_gas
  (* TODO: Convey remaining_gas in the final output. *)
  | Ok (e', _remaining_gas) -> e'

let check_patterns rlibs elibs e =
  let checker =
    let%bind pm_checked_rlibs = PM_Checker.pm_check_library rlibs in
    let%bind pm_checked_elibs = mapM elibs ~f:PM_Checker.pm_check_libtree in
    let%bind pm_checked_e = PM_Checker.pm_check_expr e in
    pure (pm_checked_rlibs, pm_checked_elibs, pm_checked_e)
  in
  match checker with Error e -> fatal_error e | Ok e' -> e'

let gas_charge rlibs elibs e =
  (SG.lib_cost rlibs, List.map ~f:SG.libtree_cost elibs, SG.expr_static_cost e)

let transform_explicitize_annots rlibs elibs e =
  match AnnExpl.explicitize_expr_wrapper rlibs elibs e with
  | Error e -> fatal_error e
  | Ok e' -> e'

let transform_dce rlibs elibs e = DCE.expr_dce_wrapper rlibs elibs e

let transform_monomorphize rlibs elibs e =
  match Mmph.monomorphize_expr_wrapper rlibs elibs e with
  | Error e -> fatal_error e
  | Ok e' -> e'

let transform_flatpat rlibs elibs e =
  match FlatPat.flatpat_expr_wrapper rlibs elibs e with
  | Error e -> fatal_error e
  | Ok e' -> e'

let transform_scoping_rename rlibs elibs e =
  ScopingRename.scoping_rename_expr_wrapper rlibs elibs e

let transform_uncurry rlibs elibs e =
  match Uncurry.uncurry_expr_wrapper rlibs elibs e with
  | Error e -> fatal_error e
  | Ok e' -> e'

let transform_clocnv rlibs elibs e =
  match CloCnv.clocnv_expr_wrapper rlibs elibs e with
  | Error e -> fatal_error e
  | Ok e' -> e'

let transform_genllvm stmts =
  match GenLlvm.genllvm_stmt_list_wrapper stmts with
  | Error e ->
      (* fatal_error e *)
      perr (scilla_error_to_sstring e)
  | Ok llmod ->
      let _ = Printf.printf "%s" llmod in
      ()

let run () =
  GlobalConfig.reset ();
  ErrorUtils.reset_warnings ();
  Datatypes.DataTypeDictionary.reinit ();
  let cli = parse_cli None ~exe_name:(Sys.get_argv ()).(0) in
  let open GlobalConfig in
  StdlibTracker.add_stdlib_dirs cli.stdlib_dirs;
  set_debug_level Debug_None;
  let filename = cli.input_file in
  let gas_limit = cli.gas_limit in
  let e = check_parsing filename in
  (* Get list of stdlib dirs. *)
  let lib_dirs = StdlibTracker.get_stdlib_dirs () in
  if List.is_empty lib_dirs then stdlib_not_found_err ();
  (* Import all libs. *)
  let std_lib = import_all_libs lib_dirs in
  let typed_rlibs, typed_elibs, typed_e = check_typing e std_lib gas_limit in
  let _ = check_patterns typed_rlibs typed_elibs typed_e in
  let gas_rlibs, gas_elibs, gas_e =
    gas_charge typed_rlibs typed_elibs typed_e
  in
  let ea_rlibs, ea_elibs, ea_e =
    transform_explicitize_annots gas_rlibs gas_elibs gas_e
  in
  let dce_rlibs, dce_elibs, dce_e = transform_dce ea_rlibs ea_elibs ea_e in
  let sr_rlibs, sr_elibs, sr_e =
    transform_scoping_rename dce_rlibs dce_elibs dce_e
  in
  let flatpat_rlibs, flatpat_elibs, flatpat_e =
    transform_flatpat sr_rlibs sr_elibs sr_e
  in
  let uncurried_rlibs, uncurried_elibs, uncurried_e =
    transform_uncurry flatpat_rlibs flatpat_elibs flatpat_e
  in
  let monomorphized_rlibs, monomorphized_elibs, monomorphized_e =
    transform_monomorphize uncurried_rlibs uncurried_elibs uncurried_e
  in
  let clocnv_e =
    transform_clocnv monomorphized_rlibs monomorphized_elibs monomorphized_e
  in
  (* Log the closure converted AST. *)
  plog
    (Printf.sprintf "Closure converted AST:\n%s\n"
       (ClosuredSyntax.CloCnvSyntax.pp_stmts_wrapper clocnv_e));
  transform_genllvm clocnv_e

let () = try run () with FatalError msg -> exit_with_error msg
