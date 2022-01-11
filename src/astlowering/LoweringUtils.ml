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

open Core_kernel
open Scilla_base
open MonadUtil
module Literal = Literal.GlobalLiteral
module Type = Literal.LType
module Identifier = Literal.LType.TIdentifier
open UncurriedSyntax.Uncurried_Syntax

let newname_prefix_char = "$"

let newname_creator () =
  let name_counter = ref 0 in
  fun base rep ->
    (* system generated names will begin with "$" for uniqueness. *)
    let n = newname_prefix_char ^ base ^ "_" ^ Int.to_string !name_counter in
    name_counter := !name_counter + 1;
    Identifier.mk_id (Identifier.Name.parse_simple_name n) rep

let global_name_counter = ref 0

let global_newnamer
    (* Cannot just call newname_creator() because of OCaml's weak type limitation. *)
      base rep =
  (* system generated names will begin with "$" for uniqueness. *)
  let n =
    newname_prefix_char ^ base ^ "_" ^ Int.to_string !global_name_counter
  in
  global_name_counter := !global_name_counter + 1;
  Identifier.mk_id (Identifier.Name.parse_simple_name n) rep

let reset_global_newnamer () = global_name_counter := 0

let tempname base =
  Identifier.as_string
    (global_newnamer base ExplicitAnnotationSyntax.empty_annot)

let rep_typ rep =
  match rep.ea_tp with
  | Some ty -> pure ty
  | None ->
      fail1 ~kind:"GenLlvm: rep_typ: not type annotated." ?inst:None rep.ea_loc

let id_typ id = rep_typ (Identifier.get_rep id)
