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
module PSRep = ParserRep
module PERep = ParserRep

(* Stdlib are implicitly imported, so we need to use local names in the parser *)
module FEParser = FrontEndParser.ScillaFrontEndParser (LocalLiteral)
module Parser = FEParser.Parser
module Syn = FEParser.FESyntax
module Dis = Disambiguate.ScillaDisambiguation (PSRep) (PERep)
module GlobalSyntax = Dis.PostDisSyntax
module RC = Recursion.ScillaRecursion (PSRep) (PERep)
module RCSRep = RC.OutputSRep
module RCERep = RC.OutputERep
module TC = TypeChecker.ScillaTypechecker (RCSRep) (RCERep)
module TCSRep = TC.OutputSRep
module TCERep = TC.OutputERep
module PM_Checker = ScillaPatternchecker (TCSRep) (TCERep)
module TI = ScillaTypeInfo (TCSRep) (TCERep)
module SG = Gas.ScillaGas (TCSRep) (TCERep)
module EL = EvalLib.ScillaCG_EvalLib (TCSRep) (TCERep)

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
  match FEParser.parse_file Parser.Incremental.exp_term filename with
  | Error e -> fatal_error e
  | Ok e ->
      plog
      @@ sprintf "\n[Parsing]:\nExpression in [%s] is successfully parsed.\n"
           filename;
      e

let disambiguate e (std_lib : GlobalSyntax.libtree list) =
  match
    let open Dis in
    let open GlobalSyntax in
    let%bind imp_var_dict, imp_typ_dict, imp_ctr_dict =
      foldM std_lib ~init:([], [], []) ~f:(fun acc_dicts lt ->
          let ({ libn; _ } : libtree) = lt in
          let lib_address = SIdentifier.as_string libn.lname in
          amend_imported_ns_dict libn lib_address None acc_dicts
            (SIdentifier.get_rep libn.lname))
    in
    let imp_dicts =
      {
        var_dict = imp_var_dict;
        typ_dict = imp_typ_dict;
        ctr_dict = imp_ctr_dict;
      }
    in
    match disambiguate_exp imp_dicts e with
    | Error _ -> fail0 ~kind:"Failed to disambiguate\n" ?inst:None
    | Ok e ->
        plog
        @@ sprintf
             "\n[Disambiguation]:\nExpression successfully disambiguated.\n";
        pure e
  with
  | Error e -> fatal_error e
  | Ok e -> e

let check_recursion e elibs =
  match
    let%bind rrlibs, relibs =
      match RC.recursion_rprins_elibs recursion_principles elibs None with
      | Error s -> fail s
      | Ok (rlibs, elibs, _, emsgs) ->
          if List.is_empty emsgs then pure (rlibs, elibs) else fail emsgs
    in
    let%bind re = RC.recursion_exp e in
    pure (rrlibs, relibs, re)
  with
  | Error e -> fatal_error e
  | Ok e -> e

(* Type check the expression with external libraries *)
let check_typing e elibs rlibs gas_limit =
  let checker =
    let open TC in
    let open TC.TypeEnv in
    let rec_lib =
      {
        RC.lname = TCIdentifier.mk_loc_id (TCName.parse_simple_name "rec_lib");
        RC.lentries = rlibs;
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
  | Ok (e', remaining_gas) -> (e', remaining_gas)

let check_patterns rlibs elibs e =
  let checker =
    let%bind pm_checked_rlibs = PM_Checker.pm_check_library rlibs in
    let%bind pm_checked_elibs = mapM elibs ~f:PM_Checker.pm_check_libtree in
    let%bind pm_checked_e = PM_Checker.pm_check_expr e in
    pure (pm_checked_rlibs, pm_checked_elibs, pm_checked_e)
  in
  match checker with Error e -> fatal_error e | Ok e' -> e'

let gas_charge remaining_gas rlibs elibs e =
  let checker =
    let wrap_error_with_gas gas res =
      match res with Ok r -> Ok r | Error e -> Error (e, gas)
    in
    let%bind gas_rlibs =
      wrap_error_with_gas remaining_gas @@ SG.lib_cost rlibs
    in
    let%bind gas_elibs =
      wrap_error_with_gas remaining_gas @@ mapM ~f:SG.libtree_cost elibs
    in
    let%bind gas_e =
      wrap_error_with_gas remaining_gas @@ SG.expr_static_cost e
    in
    pure (gas_rlibs, gas_elibs, gas_e)
  in
  match checker with
  | Error (e, g) -> fatal_error_gas e g
  | Ok e' -> (e', remaining_gas)

let transform_evallibs remaining_gas rlibs elibs e =
  match EL.eval_libs_wrapper rlibs elibs remaining_gas with
  | Error e -> fatal_error e
  | Ok ((rlibs', elibs'), remaining_gas') ->
      ((rlibs', elibs', e), remaining_gas')

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

let transform_genllvm (cli : Cli.compiler_cli) lib_stmts e_stmts expr_annot =
  match
    GenLlvm.genllvm_stmt_list_wrapper cli.input_file lib_stmts e_stmts
      expr_annot
  with
  | Error e ->
      (* fatal_error e *)
      perr (scilla_error_to_sstring e)
  | Ok llmod -> (
      match cli.output_file with
      | Some output_file ->
          if not (Llvm_bitwriter.write_bitcode_file llmod output_file) then
            fatal_error
              (mk_error0 ~kind:"Error writing LLVM bitcode to file"
                 ~inst:output_file)
      | None ->
          let _ = Printf.printf "%s" (Llvm.string_of_llmodule llmod) in
          ())

let run () =
  GlobalConfig.reset ();
  ErrorUtils.reset_warnings ();
  Datatypes.DataTypeDictionary.reinit ();
  let cli = Cli.parse_cli None ~exe_name:(Sys.get_argv ()).(0) in
  let open GlobalConfig in
  StdlibTracker.add_stdlib_dirs cli.stdlib_dirs;
  DebugInfo.generate_debuginfo := cli.debuginfo;
  set_debug_level Debug_None;
  let filename = cli.input_file in
  let gas_limit = cli.gas_limit in
  let e = check_parsing filename in
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
  let monomorphized_rlibs, monomorphized_elibs, monomorphized_e =
    transform_monomorphize uncurried_rlibs uncurried_elibs uncurried_e
  in
  let clocnv_libs, clocnv_e =
    transform_clocnv monomorphized_rlibs monomorphized_elibs monomorphized_e
  in
  (* Log the closure converted AST. *)
  pvlog (fun () ->
      Printf.sprintf "Closure converted AST:\n%s\n"
        (ClosuredSyntax.CloCnvSyntax.pp_stmts_wrapper clocnv_e));
  transform_genllvm cli clocnv_libs clocnv_e e_annot

let () = try run () with FatalError msg -> exit_with_error msg
