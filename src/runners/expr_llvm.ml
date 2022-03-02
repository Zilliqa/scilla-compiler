open Core
open Printf
open Scilla_base
open Literal
open ParserUtil
open RunnerUtil
open DebugMessage
open Result.Let_syntax
open PatternChecker
open PrettyPrinters
open RecursionPrinciples
open ErrorUtils
open MonadUtil
open TypeInfo
open ExprLlvmUtils


let run_analysis_expr file gas_limit stdlib_dirs = 
  let open GlobalConfig in
  StdlibTracker.add_stdlib_dirs stdlib_dirs;
  let e = check_parsing file in
  (* Get list of stdlib dirs. *)
  let lib_dirs = StdlibTracker.get_stdlib_dirs () in
  if List.is_empty lib_dirs then stdlib_not_found_err ();
  (* Import all libs. *)
  let std_lib = import_all_libs lib_dirs in
  let de = disambiguate e std_lib in
  let rrlibs, relibs, re = check_recursion de std_lib in
  let (typed_rlibs, typed_elibs, typed_e), gas_remaining =
    check_typing re relibs rrlibs gas_limit
  in
  let _ = check_patterns typed_rlibs typed_elibs typed_e in
  let (gas_rlibs, gas_elibs, gas_e), gas_remaining =
    gas_charge gas_remaining typed_rlibs typed_elibs typed_e
  in
  let (evallib_rlibs, evallib_elibs, evallibs_e), _gas_remaining =
    transform_evallibs gas_remaining gas_rlibs gas_elibs gas_e
  in
  let ea_rlibs, ea_elibs, ea_e =
    transform_explicitize_annots evallib_rlibs evallib_elibs evallibs_e
  in
  let dce_rlibs, dce_elibs, dce_e = transform_dce ea_rlibs ea_elibs ea_e in
  let sr_rlibs, sr_elibs, sr_e =
    transform_scoping_rename dce_rlibs dce_elibs dce_e
  in
  let flatpat_rlibs, flatpat_elibs, flatpat_e =
    transform_flatpat sr_rlibs sr_elibs sr_e
  in
  let uncurried_rlibs, uncurried_elibs, ((_, e_annot) as uncurried_e) =
    transform_uncurry flatpat_rlibs flatpat_elibs flatpat_e
  in
  let monomorphized_rlibs, monomorphized_elibs, monomorphized_e, _ =
    transform_monomorphize uncurried_rlibs uncurried_elibs uncurried_e
  in
  let clocnv_libs, clocnv_e =
    transform_clocnv monomorphized_rlibs monomorphized_elibs monomorphized_e
  in
  clocnv_libs, clocnv_e, e_annot

let run () =
  GlobalConfig.reset ();
  ErrorUtils.reset_warnings ();
  Datatypes.DataTypeDictionary.reinit ();
  let cli = Cli.parse_cli None ~exe_name:(Sys.get_argv ()).(0) in
  let open GlobalConfig in
  DebugInfo.generate_debuginfo := cli.debuginfo;

  (**** TEMP WORK AROUND FOR SCILLA-CHICK ***)
  let e = check_parsing cli.input_file in
  let e_annot = check_parsing_eval cli.input_file in 
  (* print_string (String.concat ~sep:"; " cli.stdlib_dirs); *)
  let _ = run_check_analysis e e_annot cli.gas_limit cli.stdlib_dirs in
  ()
  (**** TEMP WORK AROUND FOR SCILLA-CHICK ***)
  

  (* let clocnv_libs, clocnv_e, e_annot = run_analysis_expr cli.input_file cli.gas_limit cli.stdlib_dirs in 
  (* Log the closure converted AST. *)
  pvlog (fun () ->
      Printf.sprintf "Closure converted AST:\n%s\n"
        (ClosuredSyntax.CloCnvSyntax.pp_stmts_wrapper clocnv_e));
  transform_genllvm cli.input_file cli.output_file clocnv_libs clocnv_e e_annot *)

let () = try run () with FatalError msg -> exit_with_error msg
