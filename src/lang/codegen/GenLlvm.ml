(*
  This file is part of scilla.

  Copyright (c) 2019 - present Zilliqa Research Pvt. Ltd.
  
  scilla is free software: you can redistribute it and/or modify it under the
  terms of the GNU General Public License as published by the Free Software
  Foundation, either version 3 of the License, or (at your option) any later
  version.
 
  scilla is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
  A PARTICULAR PURPOSE.  See the GNU General Public License for more details.
 
  You should have received a copy of the GNU General Public License along with
*)

(* This file takes care of translating the closure converted AST into LLVM-IR. *)

open MonadUtil
open Syntax
open ClosuredSyntax

let genllvm_module (cmod : CloCnvSyntax.cmodule) =
  let llcontext = Llvm.create_context () in
  let llmod = Llvm.create_module llcontext (get_id cmod.contr.cname) in
  pure (Llvm.string_of_llmodule llmod)
