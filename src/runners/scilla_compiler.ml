open Syntax
open Core
open ErrorUtils
open PrettyPrinters
open ParserUtil
open DebugMessage
open MonadUtil
open Result.Let_syntax
open RunnerUtil
open RecursionPrinciples

module ParsedSyntax = ParserUtil.ParsedSyntax
module PSRep = ParserRep
module PERep = ParserRep

module Rec = Recursion.ScillaRecursion (PSRep) (PERep)
module RecSRep = Rec.OutputSRep
module RecERep = Rec.OutputERep

module TC = TypeChecker.ScillaTypechecker (RecSRep) (RecERep)
module TCSRep = TC.OutputSRep
module TCERep = TC.OutputERep

module Mmph = Monomorphize.ScillaCG_Mmph
module AnnExpl = AnnotationExplicitizer.ScillaCG_AnnotationExplicitizer (TCSRep) (TCERep)
module CloCnv =  ClosureConversion.ScillaCG_CloCnv

(* Check that the module parses *)
let check_parsing ctr syn = 
  let cmod = FrontEndParser.parse_file syn ctr in
  if Result.is_ok cmod then
    plog @@ sprintf "\n[Parsing]:\n module [%s] is successfully parsed.\n" ctr;
  cmod

(* Type check the contract with external libraries *)
let check_recursion cmod elibs  =
  let open Rec in
  let res = recursion_module cmod recursion_principles elibs in
  if Result.is_ok res then
    plog @@ sprintf "\n[Recursion Check]:\n module [%s] is successfully checked.\n" (get_id cmod.contr.cname);
  res

(* Type check the contract with external libraries *)
let check_typing cmod rprin elibs  =
let open TC in
let res = type_module cmod rprin elibs in
if Result.is_ok res then
  plog @@ sprintf "\n[Type Check]:\n module [%s] is successfully checked.\n" (get_id cmod.contr.cname);
res

let compile_cmodule cli =
  let%bind (cmod : ParsedSyntax.cmodule) = check_parsing cli.input_file ScillaParser.cmodule  in
  (* Import whatever libs we want. *)
  let elibs = import_libs cmod.elibs cli.init_file in
  let%bind (recursion_cmod, recursion_rec_principles, recursion_elibs) = check_recursion cmod elibs in
  let%bind (typed_cmod, _, typed_elibs, typed_rlibs) = check_typing recursion_cmod recursion_rec_principles recursion_elibs in
  let%bind (ea_cmod, ea_rlibs, ea_elibs) = AnnExpl.explicitize_module typed_cmod typed_rlibs typed_elibs in
  let%bind (monomorphic_cmod, monomorphic_rlibs, monomorphic_elibs) =
    Mmph.monomorphize_module ea_cmod ea_rlibs ea_elibs in
  let%bind clocnv_module = CloCnv.clocnv_module monomorphic_cmod monomorphic_rlibs monomorphic_elibs in
  (* Print the closure converted module. *)
  Printf.printf "Closure converted module:\n%s\n" (ClosuredSyntax.CloCnvSyntax.pp_cmod clocnv_module);
  pure ()

let () =
  let cli = parse_cli () in
  let open GlobalConfig in

  StdlibTracker.add_stdlib_dirs cli.stdlib_dirs;
  let file_extn = FilePath.get_extension cli.input_file in
  (* Get list of stdlib dirs. *)
  let lib_dirs = StdlibTracker.get_stdlib_dirs() in
  if lib_dirs = [] then stdlib_not_found_err ();

  (* Testsuite runs this executable with cwd=tests and ends
      up complaining about missing _build directory for logger.
      So disable the logger. *)
  set_debug_level Debug_None;

  if file_extn <> StdlibTracker.file_extn_contract
  then
    fatal_error (mk_error0(sprintf "Unknown file extension %s\n" file_extn))
  else
    (* Check contract modules. *)
    match compile_cmodule cli with
    | Ok _ -> ()
    | Error err -> fatal_error err
