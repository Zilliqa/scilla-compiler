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

(* Scilla AST without parametric polymorphism. *)
module MmphSyntax (SR : Rep) (ER : Rep) = struct
  (* Syntax reference: http://gallium.inria.fr/blog/overriding-submodules/ *)
  include (ScillaSyntax(SR)(ER) :
    (* We want all definitions from ScillaSyntax except for expr. *)
    module type of ScillaSyntax(SR)(ER) with
      type expr_annot := ScillaSyntax(SR)(ER).expr_annot and
      type expr := ScillaSyntax(SR)(ER).expr
  )

  (* This is identical to ScillaSyntax.expr except for
   *  - TFun replaced with TFunMap.
   *  - TApp replaced with TFunSel.
   *)
  type expr_annot = expr * ER.rep
  and expr =
    | Literal of literal
    | Var of ER.rep ident
    | Let of ER.rep ident * typ option * expr_annot * expr_annot
    | Message of (string * payload) list
    | Fun of ER.rep ident * typ * expr_annot
    | App of ER.rep ident * ER.rep ident list
    | Constr of string * typ list * ER.rep ident list
    | MatchExpr of ER.rep ident * (pattern * expr_annot) list
    | Builtin of ER.rep ident * ER.rep ident list
    (* Rather than one polymorphic function, we have expr for each instantiated type. *)
    (* The original polymorphic function is retained only for convenience *)
    | TFunMap of (ER.rep ident * expr_annot) * (typ * expr_annot) list
    (* Select an already instantiated expression of id based on the typ.
     * It is expected that id resolves to a TFunMap. *)
    | TFunSel of ER.rep ident * typ list
    (* Fixpoint combinator: used to implement recursion principles *)
    | Fixpoint of ER.rep ident * typ * expr_annot

end
