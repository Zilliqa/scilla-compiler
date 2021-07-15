(*
  This file is part of scilla.

  Copyright (c) 2018 - present Zilliqa Research Pvt. Ltd.
  
  scilla is free software: you can redistribute it and/or modify it under the
  terms of the GNU General Public License as published by the Free Software
  Foundation, either version 3 of the License, or (at your option) any later
  version.
 
  scilla is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
  A PARTICULAR PURPOSE.  See the GNU General Public License for more details.
 
  You should have received a copy of the GNU General Public License along with
  scilla.  If not, see <http://www.gnu.org/licenses/>.
*)

open OUnit2
open Utils

let contrlist =
  [
    "crowdfunding.scilla";
    "match_assign.scilla";
    "match_assign2.scilla";
    "match_assign3.scilla";
    "name_clash1.scilla";
    "name_clash2.scilla";
    "pm-empty.scilla";
    "pm1.scilla";
    "pm2.scilla";
    "pm3.scilla";
    "pm4.scilla";
    "pm5.scilla";
    "pm6.scilla";
    "pm7.scilla";
    "helloWorld.scilla";
    "simple-map.scilla";
    "ud-registry.scilla";
    "ud-proxy.scilla";
    "send.scilla";
    "event.scilla";
    "throw.scilla";
    "accept.scilla";
    "map_corners_test.scilla";
    "MmphTest.scilla";
    "simple-iterate.scilla";
    "map_misc.scilla";
    "uncurry1.scilla";
    "uncurry2.scilla";
    "uncurry3.scilla";
    "uncurry4.scilla";
  ]

module TestM = struct
  let gold_path dir f = [ dir; "codegen"; "contr"; "gold"; f ^ ".gold" ]

  let test_path f = [ "codegen"; "contr"; f ]

  let runner = "scilla-llvm"

  let ignore_predef_args = false

  let json_errors = false

  let gas_limit = Stdint.Uint64.of_int 4002000

  let custom_args = []

  let additional_libdirs = []

  let tests = contrlist

  let exit_code : Unix.process_status = WEXITED 0

  let provide_init_arg = false

  let diff_filter = diff_filter
end

module TestM_DI = struct
  include TestM

  let gold_path dir f = [ dir; "codegen"; "contr"; "dgold"; f ^ ".gold" ]

  let custom_args = [ "-debuginfo"; "true" ]
end

module Tests = Scilla_test.Util.DiffBasedTests (TestM)
module Tests_DI = Scilla_test.Util.DiffBasedTests (TestM_DI)

let contrs_with_init =
  [ "remote_state_reads.scilla"; "remote_state_reads_2.scilla" ]

module TestM_With_Init = struct
  include TestM

  let tests = contrs_with_init

  let provide_init_arg = true
end

module Tests_With_Init = Scilla_test.Util.DiffBasedTests (TestM_With_Init)

module TestM_With_Init_DI = struct
  include TestM_With_Init

  let gold_path dir f = [ dir; "codegen"; "contr"; "dgold"; f ^ ".gold" ]

  let custom_args = [ "-debuginfo"; "true" ]
end

module Tests_With_Init_DI = Scilla_test.Util.DiffBasedTests (TestM_With_Init_DI)

module All = struct
  let tests env =
    "codegen_contr"
    >::: [
           Tests.tests env;
           Tests_DI.tests env;
           Tests_With_Init.tests env;
           Tests_With_Init_DI.tests env;
         ]
end
