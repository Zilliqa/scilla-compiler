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
open ExplicitAnnotationSyntax

(* Scilla AST after closure-conversion.
 * This AST is lowered from MmphSyntax to be imperative
 * (which mostly means that we flatten out let-rec expressions).
 *)
module CloCnvSyntax = struct

  type payload =
    | MLit of literal
    | MVar of eannot ident

  type pattern =
    | Wildcard
    | Binder of eannot ident
    | Constructor of string * (pattern list)

  (* A function definition without any free variable references: sequence of statements.
   * For convenience, we also give the function definition a unique name as it's first component.
   * This definition allows for any number of arguments, with hope that a later optimization pass
   * will flatten out curryied functions into one taking multiple arguments. It allows for 0
   * arguments to accommodate wrapping up expressions as functions (done for TFunMap below).
   *)
  type fundef = (eannot ident) * ((eannot ident * typ) list) * clorec * (stmt_annot list)
  (* cloenv tracks the name of the function for which it is an environment for. This is 
   * just a way of keeping track of the unique memory alloc site of the environment. *)
  and cloenv = (string * (eannot ident * typ) list)
  and clorec = { thisfun : (fundef ref); envvars : cloenv }
  and expr_annot = expr * eannot
  (* Unlike higher level AST expressions, these expressions are simpler
   * and only occur as the RHS of a `Bind` statement. No `let-in` expressions. *)
  and expr =
    | Literal of literal
    | Var of eannot ident
    | Message of (string * payload) list
    (* The AST will handle full closures only, not plain function definitions. *)
    | FunClo of clorec
    | App of eannot ident * eannot ident list
    | Constr of string * typ list * eannot ident list
    | Builtin of eannot builtin_annot * eannot ident list
    (* Each instantiated type function is wrapped in a function. *)
    | TFunMap of (typ * clorec) list
    | TFunSel of eannot ident * typ list
  and stmt_annot = stmt * eannot
  and stmt =
    | Load of eannot ident * eannot ident
    | Store of eannot ident * eannot ident
    | Bind of eannot ident * expr_annot
    (* m[k1][k2][..] := v OR delete m[k1][k2][...] *)
    | MapUpdate of eannot ident * (eannot ident list) * eannot ident option
    (* v <- m[k1][k2][...] OR b <- exists m[k1][k2][...] *)
    (* If the bool is set, then we interpret this as value retrieve, 
        otherwise as an "exists" query. *)
    | MapGet of eannot ident * eannot ident * (eannot ident list) * bool
    | MatchStmt of eannot ident * (pattern * stmt_annot list) list
    | ReadFromBC of eannot ident * string
    | AcceptPayment
    | SendMsgs of eannot ident
    | CreateEvnt of eannot ident
    | CallProc of eannot ident * eannot ident list
    | Throw of eannot ident
    (* For functions returning a value. *)
    | Ret of eannot ident
    (* Put a value into a closure's env. The first component must be in the last. *)
    | StoreEnv of eannot ident * eannot ident * cloenv
    (* Load a value from a closure's env. The second component must be in the last. *)
    | LoadEnv of eannot ident * eannot ident * cloenv

  type component =
    { comp_type   : component_type;
      comp_name   : eannot ident;
      comp_params : (eannot ident * typ) list;
      comp_body   : stmt_annot list }

    type contract =
      { cname   : eannot ident;
        cparams : (eannot ident  * typ) list;
        cfields : (eannot ident * typ * (stmt_annot list)) list;
        ccomps  : component list; }
  
    (* Contract module: libary + contract definiton *)
    type cmodule =
      { smver : int;
        cname : eannot ident;
        (* Library definitions include internal and imported ones. *)
        lib_stmts  : stmt_annot list;
        contr : contract }

end
