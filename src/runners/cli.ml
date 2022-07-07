(*
  This file is part of scilla.

  Copyright (c) 2021 - present Zilliqa Research Pvt. Ltd.

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

open Core
open Scilla_base
open PrettyPrinters

type compiler_cli = {
  input_file : string;
  output_file : string option;
  init_file : string option;
  stdlib_dirs : string list;
  gas_limit : Stdint.uint64;
  debuginfo : bool;
  json_errors : bool;
  contract_info : bool;
}

let parse_cli args ~exe_name =
  let r_stdlib_dir = ref [] in
  let r_gas_limit = ref None in
  let r_input_file = ref "" in
  let r_output_file = ref None in
  let r_init_file = ref None in
  let b_debuginfo = ref false in
  let b_json_errors = ref false in
  let b_contract_info = ref false in

  let speclist =
    [
      ( "-version",
        Arg.Unit
          (fun () ->
            DebugMessage.pout
              (sprintf "Scilla version: %s\n"
                 PrettyPrinters.scilla_version_string);
            if true then exit 0;
            (* if "true" to avoid warning on exit 0 *)
            ()),
        "Print Scilla version and exit" );
      ( "-o",
        Arg.String (fun x -> r_output_file := Some x),
        "Path to output LLVM bitcode json (textual LLVM-IR is printed on \
         stdout otherwise)" );
      ( "-init",
        Arg.String (fun x -> r_init_file := Some x),
        "Path to initialization json" );
      ( "-libdir",
        Arg.String
          (fun s -> r_stdlib_dir := !r_stdlib_dir @ FilePath.path_of_string s),
        "Path(s) to libraries separated with ':' (';' on windows)" );
      ( "-gaslimit",
        Arg.String
          (fun i ->
            let g = try Some (Stdint.Uint64.of_string i) with _ -> None in
            r_gas_limit := g),
        "Gas limit" );
      ( "-debuginfo",
        Arg.Bool (fun b -> b_debuginfo := b),
        "Generate debug metadata for debugging with GDB" );
      ( "-jsonerrors",
        Arg.Unit (fun () -> b_json_errors := true),
        "Print errors in JSON format" );
      ( "-contractinfo",
        Arg.Unit (fun () -> b_contract_info := true),
        "Print contract info" );
    ]
  in

  let mandatory_usage =
    "Usage:\n" ^ exe_name
    ^ " -gaslimit <limit> -libdir /path/to/stdlib input.scilla\n"
  in
  let optional_usage =
    String.concat ~sep:"\n "
      (List.map ~f:(fun (flag, _, desc) -> flag ^ " " ^ desc) speclist)
  in
  let usage = mandatory_usage ^ "\n  " ^ optional_usage ^ "\n" in

  (* Only one input file allowed, so the last anonymous argument will be *it*. *)
  let anon_handler s = r_input_file := s in
  let () =
    match args with
    | None -> Arg.parse speclist anon_handler mandatory_usage
    | Some argv -> (
        try
          Arg.parse_argv ~current:(ref 0)
            (List.to_array @@ (exe_name :: argv))
            speclist anon_handler mandatory_usage
        with Arg.Bad msg -> fatal_error_noformat (Printf.sprintf "%s\n" msg))
  in
  if String.is_empty !r_input_file then fatal_error_noformat usage;
  let gas_limit =
    match !r_gas_limit with Some g -> g | None -> fatal_error_noformat usage
  in
  GlobalConfig.set_use_json_errors !b_json_errors;
  {
    input_file = !r_input_file;
    output_file = !r_output_file;
    init_file = !r_init_file;
    stdlib_dirs = !r_stdlib_dir;
    gas_limit;
    debuginfo = !b_debuginfo;
    json_errors = !b_json_errors;
    contract_info = !b_contract_info;
  }
