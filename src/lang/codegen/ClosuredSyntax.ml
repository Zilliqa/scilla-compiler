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

  type spattern_base =
    | Wildcard
    | Binder of eannot ident
  type spattern = 
    | Any of spattern_base
    | Constructor of string * (spattern_base list)

  (* A function definition without any free variable references: sequence of statements.
   * For convenience, we also give the function definition a unique name as it's first component.
   * This definition allows for any number of arguments, with hope that a later optimization pass
   * will flatten out curryied functions into one taking multiple arguments. It allows for 0
   * arguments to accommodate wrapping up expressions as functions (done for TFunMap below).
   *)
  type fundef = {
    fname : eannot ident;
    fargs : (eannot ident * typ) list;
    fclo : clorec; (* For convenience, to know the environment, given a function. *)
    fbody : (stmt_annot list)
  }
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
    (* Each instantiated type function is wrapped in a function "() -> t",
     * where "t" is the type of the type function's body. *)
    | TFunMap of (typ * clorec) list
    | TFunSel of eannot ident * typ list
  and stmt_annot = stmt * eannot
  and join_s = (eannot ident) * (stmt_annot list)
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
    | MatchStmt of eannot ident * (spattern * stmt_annot list) list * join_s option
    (* Transfers control to a (not necessarily immediate) enclosing match's join. *)
    | JumpStmt of eannot ident
    | ReadFromBC of eannot ident * string
    | AcceptPayment
    | SendMsgs of eannot ident
    | CreateEvnt of eannot ident
    | CallProc of eannot ident * eannot ident list
    | Throw of eannot ident option
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


   (* Gather all closures in the AST. *)
  let gather_closures stmts =
    let rec gather_from_expr (e, _) = match e with
      | Literal _ | Var _ | Message _ | App _ | Constr _  | Builtin _ | TFunSel _ -> []
      (* The AST will handle full closures only, not plain function definitions. *)
      | FunClo c ->
        c :: (gather_from_stmts !(c.thisfun).fbody)
      | TFunMap cls->
        List.concat @@ List.map (fun (_, c) ->
          c :: (gather_from_stmts !(c.thisfun).fbody)
        ) cls
    and gather_from_stmts sts =
      let gather_from_stmt (s, _) =
        match s with
        | Load _ | Store _ | MapUpdate _ | MapGet _ | ReadFromBC _ | AcceptPayment | SendMsgs _
        | CreateEvnt _ | CallProc _ | Throw _ | Ret _ | StoreEnv _ | LoadEnv _ | JumpStmt _ -> []
        | Bind (_, e) -> gather_from_expr e
        | MatchStmt (_, clauses, jopt) ->
          let res = List.fold_left (fun acc (_, sts') ->
            let res = gather_from_stmts sts' in
            res @ acc
          ) [] clauses
          in
          match jopt with
          | Some (_,  sts') ->
            let r = gather_from_stmts sts' in
            r @ res
          | None -> res
      in
      List.concat @@ List.map gather_from_stmt sts
    in
    gather_from_stmts stmts

  let gather_closures_cmod cmod =
    let libcls = gather_closures cmod.lib_stmts in
    let fieldcls = List.concat @@ List.map (fun (_, _, sts) -> gather_closures sts) cmod.contr.cfields in
    let compcls = List.concat @@ List.map (fun c -> gather_closures c.comp_body) cmod.contr.ccomps in
    libcls @ fieldcls @ compcls

  (* PrettyPrinters for the AST. *)
  open PrettyPrinters

  let pp_eannot_ident i =
    match (get_rep i).ea_tp with
    | Some t -> "(" ^ get_id i ^ " : " ^ (pp_typ t) ^ ")"
    | None -> get_id i

  let pp_payload = function
  | MLit l -> pp_literal l
  | MVar v -> pp_eannot_ident v

  let pp_spattern_base = function
  | Wildcard -> "_"
  | Binder b -> pp_eannot_ident b

  let pp_spattern = function
  | Any p -> pp_spattern_base p
  | Constructor (c, pl) -> if pl = [] then c else
    c ^ " " ^ String.concat " " (List.map pp_spattern_base pl)

  let pp_expr (e, _) : string = match e with
  | Literal l -> pp_literal l
  | Var v -> pp_eannot_ident v
  | Message psl ->
    "{ " ^ String.concat ";" (List.map (fun (s, p) -> s ^ " : " ^ (pp_payload p)) psl) ^ " }"
  (* The AST will handle full closures only, not plain function definitions. *)
  | FunClo fclo -> "[" ^ pp_eannot_ident !(fclo.thisfun).fname ^ "]"
  | App (f, alist) -> String.concat " " (List.map pp_eannot_ident (f :: alist))
  | Constr (cname, ts, ls) ->
    cname ^ " { " ^ (String.concat " " (List.map pp_typ ts)) ^ " }" ^
    (String.concat " " (List.map pp_eannot_ident ls))
  | Builtin ((b, _), alist) ->
    pp_builtin b ^ " " ^ String.concat " " (List.map pp_eannot_ident alist)
  (* Each instantiated type function is wrapped in a function. *)
  | TFunMap tclo ->
    let clos = List.map (fun (t, fclo) -> pp_typ t ^ " -> " ^ pp_eannot_ident !(fclo.thisfun).fname) tclo in
    "[" ^ String.concat "; " clos ^ "]"
  | TFunSel (i, tl) -> pp_eannot_ident i ^ " " ^ String.concat " " (List.map pp_typ tl)

  let rec pp_stmt indent (s, _) = match s with
  | Load (x, f) -> pp_eannot_ident x ^ " <- " ^ pp_eannot_ident f
  | Store (f, x) -> pp_eannot_ident f ^ " := " ^ pp_eannot_ident x
  | Bind (x, e) -> pp_eannot_ident x ^ " = " ^ pp_expr e
  (* m[k1][k2][..] := v OR delete m[k1][k2][...] *)
  | MapUpdate (m, kl, io) ->
    let mk = (pp_eannot_ident m) ^ (String.concat "" (List.map (fun k -> "[" ^ pp_eannot_ident k ^ "]") kl)) in
    (match io with
    | Some v -> mk ^ " := " ^ (pp_eannot_ident v)
    | None -> "delete " ^ mk
    )
  (* v <- m[k1][k2][...] OR b <- exists m[k1][k2][...] *)
  (* If the bool is set, then we interpret this as value retrieve, 
      otherwise as an "exists" query. *)
  | MapGet (bv, m, kl, fetchval) ->
    let mk = (pp_eannot_ident m) ^ (String.concat "" (List.map (fun k -> "[" ^ pp_eannot_ident k ^ "]") kl)) in
    (pp_eannot_ident bv) ^ if fetchval then mk else "exists " ^ mk
  | MatchStmt (p, clauses, jopt) ->
    "match " ^ (pp_eannot_ident p) ^ " with" ^
    (
      let clauses' = List.map (fun (p, sts) ->
        let pat = "\n" ^ indent ^ "| " ^ (pp_spattern p) ^ " =>\n" in
        let sts' = pp_stmts (indent ^ "  ") sts  in
        pat ^ sts'
      ) clauses in
      let clauses'' =
        (match jopt with
        | Some (lbl, sts) ->
          let pat = "\n" ^ indent ^ "join " ^ pp_eannot_ident lbl ^ " =>\n" in
          let sts' = pp_stmts (indent ^ "  ") sts  in
          clauses' @ [(pat ^ sts')]
        | None -> clauses')
      in
      String.concat "" clauses''
    )
  | JumpStmt jlbl -> "jump " ^ pp_eannot_ident jlbl
  | ReadFromBC (i, b) -> pp_eannot_ident i ^ " <- &" ^ b
  | AcceptPayment -> "accept"
  | SendMsgs m -> "send " ^ pp_eannot_ident m
  | CreateEvnt e -> "event " ^ pp_eannot_ident e
  | CallProc (p, alist) -> String.concat " " (List.map pp_eannot_ident (p :: alist))
  | Throw eopt ->
    (match eopt with
    | Some e ->
      "throw " ^ pp_eannot_ident e
    | None -> "throw"
    )
  (* For functions returning a value. *)
  | Ret v -> "ret " ^ pp_eannot_ident v
  (* Put a value into a closure's env. The first component must be in the last. *)
  | StoreEnv (x, v, (fname, _)) ->
    (* [fname](x) <- v *)
    "[" ^ fname ^ "](" ^ pp_eannot_ident x ^ ") <- " ^ pp_eannot_ident v
  (* Load a value from a closure's env. The second component must be in the last. *)
  | LoadEnv (x,  v, (fname, _)) ->
    pp_eannot_ident x ^ " <- [" ^ fname ^ "](" ^ pp_eannot_ident v ^ ")"

  and pp_stmts indent sts =
    let sts_string = List.map (pp_stmt indent) sts in
    indent ^ (String.concat ("\n" ^ indent) sts_string)

  let pp_fundef fd =
    "fundef " ^ (pp_eannot_ident fd.fname) ^ " (" ^
      (String.concat " , " (List.map (fun (a, t) ->
            (pp_eannot_ident a) ^ " : " ^ (pp_typ t)
          ) fd.fargs
        )
      ) ^ ")\n" ^
      "environment: (" ^
      (String.concat " , " (List.map (fun (a, t) ->
            (pp_eannot_ident a) ^ " : " ^ (pp_typ t)
          ) (snd @@ fd.fclo.envvars)
        )
      ) ^ ")\n" ^
      "body:\n" ^ (pp_stmts "  " fd.fbody)

  let pp_cmod cmod =
    "scilla_version " ^ Core.Int.to_string cmod.smver ^ "\n\n" ^

    (* Lifted top level functions *)
    String.concat "\n\n" (List.map (fun c ->
        pp_fundef !(c.thisfun)
      ) (gather_closures_cmod cmod)
    ) ^ "\n\n" ^

    (* all library definitions together *)
    "library:\n" ^ (pp_stmts "  " cmod.lib_stmts) ^ "\n\n" ^

    "contract " ^ get_id cmod.cname ^ "\n\n" ^

    (* immutable contract parameters *)
    "(" ^ String.concat ", " 
      (List.map (fun (p, t) -> (pp_eannot_ident p) ^ " : " ^ (pp_typ t)) cmod.contr.cparams)
      ^ ")\n\n" ^

    (* mutable fields *)
    (String.concat "\n" (List.map (fun (i, t, sts) ->
      (pp_eannot_ident i) ^ " : " ^ (pp_typ t) ^ "\n" ^ (pp_stmts "  " sts)
      ) cmod.contr.cfields)
    ) ^ "\n" ^

    (* transitions / procedures *)
    String.concat "\n" (List.map (fun c ->
        (* transition or procedure? *)
        (component_type_to_string c.comp_type) ^ " " ^
        (* component name *)
        (get_id c.comp_name) ^ " (" ^ 
          (* and parameters. *)
          String.concat ", "
          (List.map (fun (p, t) -> (pp_eannot_ident p) ^ " : " ^ (pp_typ t)) c.comp_params)
        ^ ")\n" ^
        (* The body *)
        pp_stmts "  " c.comp_body
      ) cmod.contr.ccomps
    )

  (* A wrapper to print a closure converted expression (now a list of statements)
   * from a runner, so as to include printing all closures. *)
  let pp_stmts_wrapper sts =
    (* Lifted top level functions *)
    String.concat "\n\n" (List.map (fun c ->
        pp_fundef !(c.thisfun)
      ) (gather_closures sts)
    ) ^ "\n\n" ^
    "expr_body:\n" ^
    pp_stmts "  " sts

end
