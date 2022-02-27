open Scilla_base
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
open Literal
open SanityChecker
open ScillaLlvmUtils

let compile_cmodule (cli : Cli.compiler_cli) =
  let initial_gas = Stdint.Uint64.mul Gas.scale_factor cli.gas_limit in
  let%bind (cmod : ParserSyntax.cmodule) =
    wrap_error_with_gas initial_gas
    @@ check_parsing cli.input_file Parser.Incremental.cmodule
  in
  check_version cmod.smver;
  let this_address_opt, init_address_map =
    Option.value_map cli.init_file ~f:get_init_this_address_and_extlibs
      ~default:(None, [])
  in
  let this_address =
    Option.value this_address_opt
      ~default:(FilePath.chop_extension (FilePath.basename cli.input_file))
  in
  let elibs = import_libs cmod.elibs init_address_map in
  let%bind dis_cmod =
    wrap_error_with_gas initial_gas
    @@ disambiguate_cmod cmod elibs init_address_map this_address
  in
  (* Import whatever libs we want. *)
  let%bind recursion_cmod, recursion_rec_principles, recursion_elibs =
    wrap_error_with_gas initial_gas @@ check_recursion dis_cmod elibs
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
  let%bind gas_cmod, gas_rlibs, gas_elibs =
    check_gas_charge remaining_gas typed_cmod typed_rlibs typed_elibs
  in
  let%bind (peval_rlibs, peval_elibs, peval_cmod), remaining_gas =
    wrap_error_with_gas remaining_gas
    @@ EL.eval_mod_libs gas_rlibs gas_elibs gas_cmod remaining_gas
  in
  let%bind ea_cmod, ea_rlibs, ea_elibs =
    wrap_error_with_gas remaining_gas
    @@ AnnExpl.explicitize_module peval_cmod peval_rlibs peval_elibs
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
  let%bind monomorphic_cmod, monomorphic_rlibs, monomorphic_elibs, _ =
    wrap_error_with_gas remaining_gas
    @@ Mmph.monomorphize_module uncurried_cmod uncurried_rlibs uncurried_elibs
  in
  let%bind clocnv_module =
    wrap_error_with_gas remaining_gas
    @@ CloCnv.clocnv_module monomorphic_cmod monomorphic_rlibs monomorphic_elibs
  in
  pvlog (fun () ->
      Printf.sprintf "Closure converted module:\n%s\n\n"
        (ClosuredSyntax.CloCnvSyntax.pp_cmod clocnv_module));
  let%bind llmod =
    wrap_error_with_gas remaining_gas
    @@ GenLlvm.genllvm_module cli.input_file clocnv_module
  in
  let remaining_gas' = Gas.finalize_remaining_gas cli.gas_limit remaining_gas in
  pure (dis_cmod, llmod, event_info, remaining_gas')

let run args_list ~exe_name =
  GlobalConfig.reset ();
  ErrorUtils.reset_warnings ();
  Datatypes.DataTypeDictionary.reinit ();
  reset_compiler ();
  let cli = Cli.parse_cli args_list ~exe_name in
  let open GlobalConfig in
  StdlibTracker.add_stdlib_dirs cli.stdlib_dirs;
  DebugInfo.generate_debuginfo := cli.debuginfo;
  let file_extn = FilePath.get_extension cli.input_file in
  (* Get list of stdlib dirs. *)
  let lib_dirs = StdlibTracker.get_stdlib_dirs () in
  if List.is_empty lib_dirs then stdlib_not_found_err ();

  (* Testsuite runs this executable with cwd=tests and ends
      up complaining about missing _build directory for logger.
      So disable the logger. *)
  set_debug_level Debug_None;

  if String.(file_extn = StdlibTracker.file_extn_library) then
    let cli' =
      {
        input_file = cli.input_file;
        stdlib_dirs = cli.stdlib_dirs;
        gas_limit = cli.gas_limit;
        gua_flag = false;
        init_file = cli.init_file;
        cf_flag = false;
        cf_token_fields = [];
        p_contract_info = cli.contract_info;
        p_type_info = false;
        disable_analy_warn = true;
      }
    in
    Checker.check_lmodule cli'
  else if String.(file_extn <> StdlibTracker.file_extn_contract) then
    fatal_error (mk_error0 ~kind:"Unknown file extension" ~inst:file_extn)
  else
    (* Check contract modules. *)
    match compile_cmodule cli with
    | Ok (cmod, llmod, event_info, g) ->
        let llmod_str =
          match cli.output_file with
          | Some output_file ->
              if not (Llvm_bitwriter.write_bitcode_file llmod output_file) then
                fatal_error_gas_scale Gas.scale_factor
                  (mk_error0 ~kind:"Error writing LLVM bitcode to file"
                     ~inst:output_file)
                  g;
              ""
          | None -> Llvm.string_of_llmodule llmod
        in
        let output =
          if cli.contract_info then
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
            [
              ("warnings", scilla_warning_to_json (get_warnings ()));
              ("gas_remaining", `String (Stdint.Uint64.to_string g));
              ("llvm_ir", `String llmod_str);
            ]
            @ output
          else output
        in
        (* We print as a JSON if `-jsonerrors` OR if there is some JSON data to display. *)
        if GlobalConfig.use_json_errors () || not (List.is_empty output) then
          let j = `Assoc output in
          sprintf "%s\n" (Yojson.Basic.pretty_to_string j)
          (* "" *)
        else
          scilla_warning_to_sstring (get_warnings ())
          ^ "\n; gas_remaining: " ^ Stdint.Uint64.to_string g ^ "\n" ^ llmod_str
          (* "" *)
    | Error (err, remaining_gas) ->
        fatal_error_gas_scale Gas.scale_factor err remaining_gas
