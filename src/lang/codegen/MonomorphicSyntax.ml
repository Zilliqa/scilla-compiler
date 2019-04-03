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
      type expr := ScillaSyntax(SR)(ER).expr and
      type stmt_annot := ScillaSyntax(SR)(ER).stmt_annot and
      type stmt := ScillaSyntax(SR)(ER).stmt and
      type transition := ScillaSyntax(SR)(ER).transition and
      type ctr_def := ScillaSyntax(SR)(ER).ctr_def and
      type lib_entry := ScillaSyntax(SR)(ER).lib_entry and
      type library := ScillaSyntax(SR)(ER).library and
      type contract := ScillaSyntax(SR)(ER).contract and
      type cmodule := ScillaSyntax(SR)(ER).cmodule
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
    | Builtin of ER.rep builtin_annot * ER.rep ident list
    (* Rather than one polymorphic function, we have expr for each instantiated type. *)
    (* The original polymorphic function is retained only for convenience *)
    | TFunMap of (ER.rep ident * expr_annot) * (typ * expr_annot) list
    (* Select an already instantiated expression of id based on the typ.
     * It is expected that id resolves to a TFunMap. *)
    | TFunSel of ER.rep ident * typ list
    (* Fixpoint combinator: used to implement recursion principles *)
    | Fixpoint of ER.rep ident * typ * expr_annot

    (***************************************************************)
    (* All definions below are identical to the ones in Syntax.ml. *)
    (***************************************************************)

    type stmt_annot = stmt * SR.rep
    and stmt =
      | Load of ER.rep ident * ER.rep ident
      | Store of ER.rep ident * ER.rep ident
      | Bind of ER.rep ident * expr_annot
      (* m[k1][k2][..] := v OR delete m[k1][k2][...] *)
      | MapUpdate of ER.rep ident * (ER.rep ident list) * ER.rep ident option
      (* v <- m[k1][k2][...] OR b <- exists m[k1][k2][...] *)
      (* If the bool is set, then we interpret this as value retrieve, 
         otherwise as an "exists" query. *)
      | MapGet of ER.rep ident * ER.rep ident * (ER.rep ident list) * bool
      | MatchStmt of ER.rep ident * (pattern * stmt_annot list) list
      | ReadFromBC of ER.rep ident * string
      | AcceptPayment
      | SendMsgs of ER.rep ident
      | CreateEvnt of ER.rep ident
      | Throw of ER.rep ident

    type transition = 
      { tname   : SR.rep ident;
        tparams : (ER.rep ident  * typ) list;
        tbody   : stmt_annot list }
  
    type ctr_def =
      { cname : ER.rep ident; c_arg_types : typ list }
    
    type lib_entry =
      | LibVar of ER.rep ident * expr_annot
      | LibTyp of ER.rep ident * ctr_def list
  
    type library =
      { lname : SR.rep ident;
        lentries : lib_entry list }
    
    type contract =
      { cname   : SR.rep ident;
        cparams : (ER.rep ident  * typ) list;
        cfields : (ER.rep ident * typ * expr_annot) list;
        ctrans  : transition list; }
  
    (* Contract module: libary + contract definiton *)
    type cmodule =
      { smver : int;                (* Scilla major version of the contract. *)
        cname : SR.rep ident;
        libs  : library option;     (* lib functions defined in the module *)
        elibs : SR.rep ident list;  (* list of imports / external libs *)
        contr : contract }

end
