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

let explist = [
  "exponential-growth.scilexp";
  "fun-type-inst.scilexp";
  "multi-type-inst.scilexp";
  "dce1.scilexp";
  "typ-inst.scilexp";
  "tfun-val.scilexp";
  "tname_clash.scilexp";
  "simple_ho.scilexp";
  "simple-fun.scilexp";
  "adt-fun.scilexp";
  "uint256-fun.scilexp";
  "nested-fun.scilexp";
  "pm1.scilexp";
  "pm2.scilexp";
  "pm3.scilexp";
  "pm4.scilexp";
  "pm5.scilexp";
  "pm6.scilexp";
  "pm7.scilexp";
  "name_clash.scilexp";
  "name_clash1.scilexp";
  "name_clash2.scilexp";
  "name_clash3.scilexp";
  "lit-int32.scilexp";
  "lit-string.scilexp";
  "lit-nil.scilexp";
  "lit-bystr3.scilexp";
  "lit-i256-4.scilexp";
  "lit-i256-min.scilexp";
  "lit-i256-max.scilexp";
  "lit-ui256-4.scilexp";
  "lit-ui256-max.scilexp";
  "lit-pair-list-int.scilexp";
  "map1.scilexp";
]

module Tests = TestUtil.DiffBasedTests(
  struct
    let gold_path dir f = [dir; "codegen"; "expr"; "gold"; f ^ ".gold" ]
    let test_path f = ["codegen"; "expr"; f]
    let runner = "expr-compiler"
    let ignore_predef_args = false
    let gas_limit = Stdint.Uint64.of_int 4002000
    let custom_args = []
    let additional_libdirs = []
    let tests = explist
    let exit_code : Unix.process_status = WEXITED 0

  end)

let all_tests = Tests.all_tests
