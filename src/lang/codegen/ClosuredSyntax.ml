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
open MonomorphicSyntax

(* Scilla AST after closure-conversion.
 * This AST is lowered from MmphSyntax to be imperative
 * (which mostly means that we flatten out let-rec expressions).
 *)
module ClrCnvSyntax (SR : Rep) (ER : Rep) = struct
  (* Syntax reference: http://gallium.inria.fr/blog/overriding-submodules/ *)
  include (MmphSyntax(SR)(ER) :
    (* We want all definitions from MmphSyntax except for expr. *)
    module type of MmphSyntax(SR)(ER) with
      type expr_annot := MmphSyntax(SR)(ER).expr_annot and
      type expr := MmphSyntax(SR)(ER).expr and
      type stmt_annot := MmphSyntax(SR)(ER).stmt_annot and
      type stmt := MmphSyntax(SR)(ER).stmt and
      type component := MmphSyntax(SR)(ER).component and
      type ctr_def := MmphSyntax(SR)(ER).ctr_def and
      type lib_entry := MmphSyntax(SR)(ER).lib_entry and
      type library := MmphSyntax(SR)(ER).library and
      type contract := MmphSyntax(SR)(ER).contract and
      type cmodule := MmphSyntax(SR)(ER).cmodule and
      type lmodule := MmphSyntax(SR)(ER).lmodule and
      type libtree := MmphSyntax(SR)(ER).libtree
  )

  (* A function definition without any free variable references: sequence of statements.
   * For convenience, we also give the function definition a unique name as it's first component.
   * This definition allows for any number of arguments, with hope that a later optimization pass
   * will flatten out curryied functions into one taking multiple arguments. It allows for 0
   * arguments to accommodate wrapping up expressions as functions (done for TFunSel below).
   *)
  type fundef = (ER.rep ident) * ((ER.rep ident * typ) list) * clorec * (stmt_annot list)
  (* cloenv and it's uses are essentially for checking and nothing more.
   * They can as well be an empty definition with StoreEnv and LoadEnv referring
   * to "remembered" indices of the variables in the closure environment. *)
  and cloenv = ((ER.rep ident * typ) list)
  and clorec = { thisfun : (fundef ref); envvars : cloenv }
  and expr_annot = expr * ER.rep
  (* Unlike higher level AST expressions, these expressions are simpler
   * and only occur as the RHS of a `Bind` statement. No `let-in` expressions. *)
  and expr =
    | Literal of literal
    | Var of ER.rep ident
    | Message of (string * payload) list
    (* The AST will handle full closures only, not plain function definitions. *)
    | FunClo of clorec
    | App of ER.rep ident * ER.rep ident list
    | Constr of string * typ list * ER.rep ident list
    | Builtin of ER.rep builtin_annot * ER.rep ident list
    (* Each instantiated type function is wrapped in a function. *)
    | TFunMap of (typ * clorec) list
    | TFunSel of ER.rep ident * typ list
  and stmt_annot = stmt * SR.rep
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
    | CallProc of SR.rep ident * ER.rep ident list
    | Throw of ER.rep ident
    (* For functions returning a value. *)
    | Ret of ER.rep ident
    (* Put a value into a closure's env. The first component must be in the last. *)
    | StoreEnv of ER.rep ident * ER.rep ident * cloenv
    (* Load a value from a closure's env. The second component must be in the last. *)
    | LoadEnv of ER.rep ident * ER.rep ident * cloenv

  type component =
    { comp_type   : component_type;
      comp_name   : SR.rep ident;
      comp_params : (ER.rep ident * typ) list;
      comp_body   : stmt_annot list }

    type contract =
      { cname   : SR.rep ident;
        cparams : (ER.rep ident  * typ) list;
        cfields : (ER.rep ident * typ * (stmt_annot list)) list;
        ccomps  : component list; }
  
    (* Contract module: libary + contract definiton *)
    type cmodule =
      { smver : int;
        cname : SR.rep ident;
        (* Library definitions include internal and imported ones. *)
        lib_stmts  : stmt_annot list;
        contr : contract }

end
