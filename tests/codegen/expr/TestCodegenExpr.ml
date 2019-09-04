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
  "exponential-growth.scilla";
  "fun-type-inst.scilla";
  "multi-type-inst.scilla";
  "dce1.scilexp";
  "typ-inst.scilexp";
  "tfun-val.scilexp";
  "tname_clash.scilexp";
  "simple_ho.scilexp";
]

module Tests = TestUtil.DiffBasedTests(
  struct
    let gold_path dir f = [dir; "codegen"; "expr"; "gold"; f ^ ".gold" ]
    let test_path f = ["codegen"; "expr"; f]
    let runner = "expr-compiler"
    let gas_limit = Stdint.Uint64.of_int 4002000
    let custom_args = []
    let additional_libdirs = []
    let tests = explist
    let exit_code : Unix.process_status = WEXITED 0

  end)
