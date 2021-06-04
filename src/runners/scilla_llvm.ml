open Core
open Scilla_base
open DebugMessage
open ErrorUtils

let () =
  try pout @@ Scilla_llvm_common.run None ~exe_name:(Sys.get_argv ()).(0)
  with FatalError msg -> exit_with_error msg
