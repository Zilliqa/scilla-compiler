open Core
open Scilla_server_lib
open Scilla_eval
open Idl
open IPCUtil
module IDL = Server.IDL

type args_t = string list [@@deriving rpcty, show]
(** A type alias representing a list of arguments to
    be provided to scilla-compiler *)

module API (R : RPC) = struct
  open R

  let description =
    Interface.
      {
        name = "API";
        namespace = None;
        description =
          [
            "This is a functor used to generate clients and servers that \
             follow the JSON RPC protocol";
          ];
        version = (1, 0, 0);
      }

  let implementation = implement description

  let compiler_argv =
    Param.mk ~name:"argv"
      ~description:[ "scilla-llvm execution parameters" ]
      args_t

  let compiler_return = Param.mk Rpc.Types.string
  let compiler_error = RPCError.err

  let compiler =
    (* Change the name to "compile" once the client supports it. *)
    declare "check"
      [
        "Parse Scilla contract, perform a number of static checks including \
         typechecking and generate LLVM-IR";
      ]
      (compiler_argv @-> returning compiler_return compiler_error)
end

module ServerAPI = API (IDL.GenServer ())

let cmd =
  let server_impl () =
    ServerAPI.compiler
    @@ Server.mk_handler (Scilla_llvm_common.run ~exe_name:"scilla-llvm");
    ServerAPI.implementation
  in
  Command.basic ~summary:"Scilla server"
    Command.Let_syntax.(
      let%map_open sock_path =
        flag "-socket"
          (optional_with_default Server.sock_path string)
          ~doc:"SOCKET Address for communication with the server"
      and num_pending =
        flag "-num-pending"
          (optional_with_default Server.num_pending int)
          ~doc:"NUM_PENDING Maximum number of pending requests"
      in
      fun () ->
        Server.start ~server_implementation:server_impl ~sock_path ~num_pending)

let () = Command_unix.run cmd
