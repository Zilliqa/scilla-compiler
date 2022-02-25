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

(* Modules use local names, which are then disambiguated *)
module FEParser = FrontEndParser.ScillaFrontEndParser (LocalLiteral)
module Parser = FEParser.Parser
module ParserSyntax = FEParser.FESyntax
module PSRep = ParserRep
module PERep = ParserRep
module Dis = Disambiguate.ScillaDisambiguation (PSRep) (PERep)
module Rec = Recursion.ScillaRecursion (PSRep) (PERep)
module RecSRep = Rec.OutputSRep
module RecERep = Rec.OutputERep
module TC = TypeChecker.ScillaTypechecker (RecSRep) (RecERep)
module TCSRep = TC.OutputSRep
module TCERep = TC.OutputERep
module PMC = ScillaPatternchecker (TCSRep) (TCERep)
module PMCSRep = PMC.SPR
module PMCERep = PMC.EPR
module SC = ScillaSanityChecker (TCSRep) (TCERep)
module EI = ScillaEventInfo (PMCSRep) (PMCERep)
module SG = Gas.ScillaGas (TCSRep) (TCERep)
module EL = EvalLib.ScillaCG_EvalLib (TCSRep) (TCERep)

module AnnExpl =
  AnnotationExplicitizer.ScillaCG_AnnotationExplicitizer (TCSRep) (TCERep)

module Mmph = Monomorphize.ScillaCG_Mmph
module CloCnv = ClosureConversion.ScillaCG_CloCnv
module FlatPat = FlattenPatterns.ScillaCG_FlattenPat
module ScopingRename = ScopingRename.ScillaCG_ScopingRename
module Uncurry = Uncurry.ScillaCG_Uncurry

let reset_compiler () =
  UncurriedSyntax.Uncurried_Syntax.Datatypes.DataTypeDictionary.reset ();
  LoweringUtils.reset_global_newnamer ()

let check_version vernum =
  let mver, _, _ = Syntax.scilla_version in
  if vernum <> mver then
    fatal_error
      (mk_error0 ~kind:"Scilla version mismatch"
         ~inst:(sprintf "Expected %d vs Contract %d\n" mver vernum))

(* Check that the module parses *)
let check_parsing ctr syn =
  let cmod = FEParser.parse_file syn ctr in
  if Result.is_ok cmod then
    plog @@ sprintf "\n[Parsing]:\n module [%s] is successfully parsed.\n" ctr;
  cmod

(* Change local names to global names *)
let disambiguate_lmod lmod elibs names_and_addresses this_address =
  let open Dis in
  let res = disambiguate_lmodule lmod elibs names_and_addresses this_address in
  if Result.is_ok res then
    plog
    @@ sprintf "\n[Disambiguation]:\n lmodule [%s] is successfully checked.\n"
         (PreDisIdentifier.as_error_string lmod.libs.lname);
  res

(* Change local names to global names *)
let disambiguate_cmod cmod elibs names_and_addresses this_address =
  let open Dis in
  let res = disambiguate_cmodule cmod elibs names_and_addresses this_address in
  if Result.is_ok res then
    plog
    @@ sprintf "\n[Disambiguation]:\n cmodule [%s] is successfully checked.\n"
         (PreDisIdentifier.as_error_string cmod.contr.cname);
  res

(* Type check the contract with external libraries *)
let check_recursion cmod elibs =
  let open Rec in
  let res = recursion_module cmod recursion_principles elibs in
  if Result.is_ok res then
    plog
    @@ sprintf "\n[Recursion Check]:\n module [%s] is successfully checked.\n"
         (RecIdentifier.as_string cmod.contr.cname);
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
             (TCIdentifier.as_string cmod.contr.cname);
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
         (PMC.PCIdentifier.as_string e.contr.cname);
  res

let check_gas_charge remaining_gas cmod rlibs elibs =
  let%bind gas_cmod = wrap_error_with_gas remaining_gas @@ SG.cmod_cost cmod in
  let%bind gas_rlibs =
    wrap_error_with_gas remaining_gas @@ mapM ~f:SG.lib_entry_cost rlibs
  in
  let%bind gas_elibs =
    wrap_error_with_gas remaining_gas @@ mapM ~f:SG.libtree_cost elibs
  in
  pure (gas_cmod, gas_rlibs, gas_elibs)

let check_eval_libs remaining_gas cmod rlibs elibs =
  let%bind eval_libscmod =
    wrap_error_with_gas remaining_gas @@ SG.cmod_cost cmod
  in
  let%bind eval_libsrlibs =
    wrap_error_with_gas remaining_gas @@ mapM ~f:SG.lib_entry_cost rlibs
  in
  let%bind eval_libselibs =
    wrap_error_with_gas remaining_gas @@ mapM ~f:SG.libtree_cost elibs
  in
  pure (eval_libscmod, eval_libsrlibs, eval_libselibs)