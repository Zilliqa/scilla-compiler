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

open Scilla_test.Util
open Core

let llvm_version () =
  let open Build_info.V1 in
  let rec find_llvm = function
    | l :: lr ->
        if String.equal "llvm" @@ Statically_linked_library.name l then
          match Statically_linked_library.version l with
          | None -> None
          | Some v -> Version.to_string v |> Option.some
        else find_llvm lr
    | [] -> None
  in
  Statically_linked_libraries.to_list ()
  |> find_llvm
  |> Option.value ~default:"n/a"

let () =
  let tests = [ TestCodegenExpr.Common.tests; TestCodegenContr.Common.tests ] in
  (* Tests for DebugInfo should be used with LLVM 13.0.0.
     Newer versions of LLVM generate the different debug metadata because of
     the changes introduced in:
     https://reviews.llvm.org/rG47b239eb5a17065d13c317600c46e56ffe2d6c75*)
  let tests =
    if String.equal "13.0.0" @@ llvm_version () then
      tests @ [ TestCodegenExpr.DI.tests; TestCodegenContr.DI.tests ]
    else tests
  in
  run_tests tests
