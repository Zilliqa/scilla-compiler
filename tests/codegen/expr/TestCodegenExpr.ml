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

let explist =
  [
    "exponential-growth.scilexp";
    "fun-type-inst.scilexp";
    "multi-type-inst.scilexp";
    "dce1.scilexp";
    "fib.scilexp";
    "ackermann.scilexp";
    "typ-inst.scilexp";
    "typ1-inst.scilexp";
    "typ2-inst.scilexp";
    "typ3-inst.scilexp";
    "tfun-val.scilexp";
    "nonprenex.scilexp";
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
    "lit-int32-1.scilexp";
    "lit-string.scilexp";
    "lit-nil.scilexp";
    "lit-bystr3.scilexp";
    "lit-i256-4.scilexp";
    "lit-i256-min.scilexp";
    "lit-i256-max.scilexp";
    "lit-ui256-4.scilexp";
    "lit-ui256-max.scilexp";
    "lit-pair-list-int.scilexp";
    "lit-nat_zero.scilexp";
    "lit-nat_two.scilexp";
    "map1.scilexp";
    "builtin_add_int256.scilexp";
    "builtin_add_int32.scilexp";
    "builtin_add_uint256.scilexp";
    "builtin_add_uint32.scilexp";
    "builtin_to_nat.scilexp";
    "match_assign.scilexp";
  ]

module Tests = Scilla_test.Util.DiffBasedTests (struct
  let gold_path dir f = [ dir; "codegen"; "expr"; "gold"; f ^ ".gold" ]

  let test_path f = [ "codegen"; "expr"; f ]

  let runner = "expr-llvm"

  let ignore_predef_args = false

  let json_errors = false

  let gas_limit = Stdint.Uint64.of_int 4002000

  let custom_args = []

  let additional_libdirs = []

  let tests = explist

  let exit_code : Unix.process_status = WEXITED 0

  let provide_init_arg = false
end)

module All = struct
  let tests env = "codegen_expr" >::: [ Tests.tests env ]
end
