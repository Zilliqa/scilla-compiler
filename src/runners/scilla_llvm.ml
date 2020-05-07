open Scilla_base
module Literal = Literal.FlattenedLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open ParserUtil
open Core
open ErrorUtils
open PrettyPrinters
open DebugMessage
open MonadUtil
open Result.Let_syntax
open RunnerUtil
open PatternChecker
open EventInfo
open RecursionPrinciples
module Parser = ScillaParser.Make (ParserSyntax)
module PSRep = ParserRep
module PERep = ParserRep
module Rec = Recursion.ScillaRecursion (PSRep) (PERep)
module RecSRep = Rec.OutputSRep
module RecERep = Rec.OutputERep
module TC = TypeChecker.ScillaTypechecker (RecSRep) (RecERep)
module TCSRep = TC.OutputSRep
module TCERep = TC.OutputERep
module PMC = ScillaPatternchecker (TCSRep) (TCERep)
module PMCSRep = PMC.SPR
module PMCERep = PMC.EPR
module EI = ScillaEventInfo (PMCSRep) (PMCERep)
module Mmph = Monomorphize.ScillaCG_Mmph

module AnnExpl =
  AnnotationExplicitizer.ScillaCG_AnnotationExplicitizer (TCSRep) (TCERep)

module CloCnv = ClosureConversion.ScillaCG_CloCnv
module FlatPat = FlattenPatterns.ScillaCG_FlattenPat
module ScopingRename = ScopingRename.ScillaCG_ScopingRename
module Uncurry = Uncurry.ScillaCG_Uncurry

let check_version vernum =
  let mver, _, _ = Syntax.scilla_version in
  if vernum <> mver then
    let emsg =
      sprintf "Scilla version mismatch. Expected %d vs Contract %d\n" mver
        vernum
    in
    fatal_error (mk_error0 emsg)

(* Check that the module parses *)
let check_parsing ctr syn =
  let cmod = FrontEndParser.parse_file syn ctr in
  if Result.is_ok cmod then
    plog @@ sprintf "\n[Parsing]:\n module [%s] is successfully parsed.\n" ctr;
  cmod

(* Type check the contract with external libraries *)
let check_recursion cmod elibs =
  let open Rec in
  let res = recursion_module cmod recursion_principles elibs in
  if Result.is_ok res then
    plog
    @@ sprintf "\n[Recursion Check]:\n module [%s] is successfully checked.\n"
         (Identifier.get_id cmod.contr.cname);
  res

let wrap_error_with_gas gas res =
  match res with Ok r -> Ok r | Error e -> Error (e, gas)

(* Type check the contract with external libraries *)
let check_typing cmod rprin elibs gas =
  let open TC in
  let res = type_module cmod rprin elibs gas in
  let _ =
    match res with
    | Ok (_, remaining_gas) ->
        plog
        @@ sprintf "\n[Type Check]:\n module [%s] is successfully checked.\n"
             (Identifier.get_id cmod.contr.cname);
        let open Stdint.Uint64 in
        plog
        @@ sprintf "Gas remaining after typechecking: %s units.\n"
             (to_string remaining_gas)
    | _ -> ()
  in
  res

let check_patterns e rlibs elibs =
  let res = PMC.pm_check_module e rlibs elibs in
  if Result.is_ok res then
    plog
    @@ sprintf "\n[Pattern Check]:\n module [%s] is successfully checked.\n"
         (Identifier.get_id e.contr.cname);
  res

let compile_cmodule cli =
  let initial_gas = cli.gas_limit in
  let%bind (cmod : ParserSyntax.cmodule) =
    wrap_error_with_gas initial_gas
    @@ check_parsing cli.input_file Parser.Incremental.cmodule
  in
  check_version cmod.smver;
  (* Import whatever libs we want. *)
  let elibs = import_libs cmod.elibs cli.init_file in
  let%bind recursion_cmod, recursion_rec_principles, recursion_elibs =
    wrap_error_with_gas initial_gas @@ check_recursion cmod elibs
  in
  let%bind (typed_cmod, _, typed_elibs, typed_rlibs), remaining_gas =
    check_typing recursion_cmod recursion_rec_principles recursion_elibs
      initial_gas
  in
  let%bind pm_checked_cmod, _, _ =
    wrap_error_with_gas remaining_gas
    @@ check_patterns typed_cmod typed_rlibs typed_elibs
  in
  let%bind event_info =
    wrap_error_with_gas remaining_gas @@ EI.event_info pm_checked_cmod
  in
  let%bind ea_cmod, ea_rlibs, ea_elibs =
    wrap_error_with_gas remaining_gas
    @@ AnnExpl.explicitize_module typed_cmod typed_rlibs typed_elibs
  in
  let dce_cmod, dce_rlibs, dce_elibs =
    DCE.ScillaCG_Dce.cmod_dce ea_cmod ea_rlibs ea_elibs
  in
  let sr_cmod, sr_rlibs, sr_elibs =
    ScopingRename.scoping_rename_module dce_cmod dce_rlibs dce_elibs
  in
  let%bind flatpat_cmod, flatpat_rlibs, flatpat_elibs =
    wrap_error_with_gas remaining_gas
    @@ FlatPat.flatpat_in_module sr_cmod sr_rlibs sr_elibs
  in
  let%bind uncurried_cmod, uncurried_rlibs, uncurried_elibs =
    wrap_error_with_gas remaining_gas
    @@ Uncurry.uncurry_in_module flatpat_cmod flatpat_rlibs flatpat_elibs
  in
  let%bind monomorphic_cmod, monomorphic_rlibs, monomorphic_elibs =
    wrap_error_with_gas remaining_gas
    @@ Mmph.monomorphize_module uncurried_cmod uncurried_rlibs uncurried_elibs
  in
  let%bind clocnv_module =
    wrap_error_with_gas remaining_gas
    @@ CloCnv.clocnv_module monomorphic_cmod monomorphic_rlibs monomorphic_elibs
  in
  (* Print the closure converted module. *)
  plog
    (Printf.sprintf "Closure converted module:\n%s\n\n"
       (ClosuredSyntax.CloCnvSyntax.pp_cmod clocnv_module));
  let%bind llmod_str =
    wrap_error_with_gas remaining_gas @@ GenLlvm.genllvm_module clocnv_module
  in
  pure (cmod, llmod_str, event_info, remaining_gas)

let run () =
  GlobalConfig.reset ();
  ErrorUtils.reset_warnings ();
  Datatypes.DataTypeDictionary.reinit ();
  let cli = parse_cli None ~exe_name:Sys.argv.(0) in
  let open GlobalConfig in
  StdlibTracker.add_stdlib_dirs cli.stdlib_dirs;
  let file_extn = FilePath.get_extension cli.input_file in
  (* Get list of stdlib dirs. *)
  let lib_dirs = StdlibTracker.get_stdlib_dirs () in
  if lib_dirs = [] then stdlib_not_found_err ();

  (* Testsuite runs this executable with cwd=tests and ends
      up complaining about missing _build directory for logger.
      So disable the logger. *)
  set_debug_level Debug_None;

  if file_extn <> StdlibTracker.file_extn_contract then
    fatal_error (mk_error0 (sprintf "Unknown file extension %s\n" file_extn))
  else
    (* Check contract modules. *)
    match compile_cmodule cli with
    | Ok (cmod, llmod_str, event_info, g) ->
        let output =
          if cli.p_contract_info then
            [
              ( "contract_info",
                JSON.ContractInfo.get_json cmod.smver cmod.contr event_info );
            ]
          else []
        in
        let output =
          (* This part only has warnings and gas_remaining, which we output as JSON
             * if either `-jsonerrors` OR if there is other JSON output. *)
          if GlobalConfig.use_json_errors () || not (List.is_empty output) then
            output
            @ [
                ("warnings", scilla_warning_to_json (get_warnings ()));
                ("gas_remaining", `String (Stdint.Uint64.to_string g));
                ("llvm_ir", `String llmod_str);
              ]
          else output
        in
        (* We print as a JSON if `-jsonerrors` OR if there is some JSON data to display. *)
        if GlobalConfig.use_json_errors () || not (List.is_empty output) then
          let j = `Assoc output in
          sprintf "%s\n" (Yojson.Basic.pretty_to_string j)
        else
          scilla_warning_to_sstring (get_warnings ())
          ^ "\n; gas_remaining: " ^ Stdint.Uint64.to_string g ^ "\n" ^ llmod_str
    | Error (err, remaining_gas) -> fatal_error_gas err remaining_gas

let () = try pout @@ run () with FatalError msg -> exit_with_error msg