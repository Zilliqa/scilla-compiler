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

open Syntax

(* Create a closure for creating new variable names.
 * The closure maintains a state for incremental numbering. 
 * Do not use this directly as it will provide a namer with
 * count beginning from 0 (potential name clashes if used as such
 * from different passes. Use it only if you're sure of providing
 * a uniqe base name. Otherwise use the global_newnamer next. *)
val newname_creator : unit -> string -> 'a -> 'a ident

(* A newnamer that keeps a global counter and assures unique
 * names throughout the compiler pipeline. *)
val global_newnamer : string -> 'a -> 'a ident
