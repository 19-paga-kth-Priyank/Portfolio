open Printf
open Lexer
open Parser
open Ast

(* Define the simplified name type *)
type ty_Iden1 = | Iden_name1 of string

(* Updated types with simplified names *)
type ty_type1 = 
  | TY_VOID1 
  | TY_INT1 
  | TY_CHAR1 
  | TY_PTR1 of ty_type1
  | TY_Iden1 of ty_Iden1 (* Replaces `ty_Iden` *)

type expr1 = 
  | EInt1 of int 
  | EString1 of string 
  | EChar1 of string
  | EVar1 of ty_Iden1 (* Replaces `ty_Iden` *)
  | EBNOp1 of ty_BNOp * expr1 * expr1(* Removed line number `int` *)
  | EUNOp1 of ty_UNOp * expr1 (* Removed line number `int` *)
  | ECall1 of ty_Iden1 * (expr1 list)
  | Enew1 of ty_type1 * expr1
  | EArrayAccess1 of ty_Iden1 * expr1 * (ty_Iden1 option)

type stmt1 = 
  | SExpr1 of expr1
  | SVarDef1 of ty_type1 * ty_Iden1 * expr1
  | SVarAssign1 of ty_Iden1 * expr1 
  | SArrayAssign1 of ty_Iden1 * expr1 * (ty_Iden1 option) * expr1
  | SScope1 of (stmt1 list)
  | SIf1 of expr1 * stmt1 * (stmt1 option)
  | SWhile1 of expr1 * stmt1
  | SBreak1
  | SReturn1 of (expr1 option) (* Removed line number `int` *)
  | SDelete1 of ty_Iden1

type global1 = 
  | GFuncDef1 of ty_type1 * ty_Iden1 * ((ty_type1 * ty_Iden1) list) * stmt1
  | GFuncDecl1 of ty_type1 * ty_Iden1 * ((ty_type1 * ty_Iden1) list)
  | GVarDef1 of ty_type1 * ty_Iden1 * expr1
  | GVarDecl1 of ty_type1 * ty_Iden1
  | GStruct1 of ty_Iden1 * ((ty_type1 * ty_Iden1) list)

type program1 = 
  | Prog1 of (global1 list)

(* Helper function to convert ty_Iden to ty_Iden1 *)
let convert_iden_to_simple = function
  | Iden_name (name, _) -> Iden_name1(name)

(* Recursive function to simplify types *)
let rec simplify_ty_type = function
  | TY_VOID -> TY_VOID1
  | TY_INT -> TY_INT1
  | TY_CHAR -> TY_CHAR1
  | TY_PTR base_ty -> TY_PTR1 (simplify_ty_type base_ty)
  | TY_Iden id -> TY_Iden1 (convert_iden_to_simple id)

(* Recursive function to simplify expressions *)
let rec simplify_expr = function
  | EInt i -> EInt1 i
  | EString s -> EString1 s
  | EChar c -> EChar1 c
  | EVar id -> EVar1 (convert_iden_to_simple id)
  | EBNOp (op, e1, e2,_) -> EBNOp1 (op, simplify_expr e1, simplify_expr e2)
  | EUNOp (op, e,_) -> EUNOp1 (op, simplify_expr e)
  | ECall (id, args) -> ECall1 (convert_iden_to_simple id, List.map simplify_expr args)
  | Enew (ty, e) -> Enew1 (simplify_ty_type ty, simplify_expr e)
  | EArrayAccess (id, index_expr, opt_id) -> 
      EArrayAccess1 (
        convert_iden_to_simple id, 
        simplify_expr index_expr, 
        Option.map convert_iden_to_simple opt_id
      )

(* Recursive function to simplify statements *)
let rec simplify_stmt = function
  | SExpr e -> SExpr1 (simplify_expr e)
  | SVarDef (ty, id, e) -> SVarDef1 (simplify_ty_type ty, convert_iden_to_simple id, simplify_expr e)
  | SVarAssign (id, e) -> SVarAssign1 (convert_iden_to_simple id, simplify_expr e)
  | SArrayAssign (id, e1, opt_id, e2) -> 
      SArrayAssign1 (
        convert_iden_to_simple id, 
        simplify_expr e1, 
        Option.map convert_iden_to_simple opt_id, 
        simplify_expr e2
      )
  | SScope stmts -> SScope1 (List.map simplify_stmt stmts)
  | SIf (e, then_stmt, else_stmt_opt) -> 
      SIf1 (simplify_expr e, simplify_stmt then_stmt, Option.map simplify_stmt else_stmt_opt)
  | SWhile (e, body) -> SWhile1 (simplify_expr e, simplify_stmt body)
  | SBreak -> SBreak1
  | SReturn (e_opt,_) -> SReturn1 (Option.map simplify_expr e_opt)
  | SDelete (id,_) -> SDelete1 (convert_iden_to_simple id)

(* Simplify a global definition *)
let simplify_global = function
  | GFuncDef (ty, id, args, body) -> 
      GFuncDef1 (
        simplify_ty_type ty,
        convert_iden_to_simple id,
        List.map (fun (t, i) -> (simplify_ty_type t, convert_iden_to_simple i)) args,
        simplify_stmt body
      )
  | GFuncDecl (ty, id, args) -> 
      GFuncDecl1 (
        simplify_ty_type ty,
        convert_iden_to_simple id,
        List.map (fun (t, i) -> (simplify_ty_type t, convert_iden_to_simple i)) args
      )
  | GVarDef (ty, id, e) -> 
      GVarDef1 (simplify_ty_type ty, convert_iden_to_simple id, simplify_expr e)
  | GVarDecl (ty, id) -> 
      GVarDecl1 (simplify_ty_type ty, convert_iden_to_simple id)
  | GStruct (id, fields) -> 
      GStruct1 (
        convert_iden_to_simple id, 
        List.map (fun (t, i) -> (simplify_ty_type t, convert_iden_to_simple i)) fields
      )
(* Simplify an entire program *)
let simplify_program = function
  | Prog globals -> Prog1 (List.map simplify_global globals)


  

let pp_ty_Iden1 = function
| Iden_name1 (s) -> sprintf "\"%s\"" s

let rec pp_ty_type1 = function
  | TY_VOID1 -> "TVoid"
  | TY_INT1 -> "TInt"
  | TY_CHAR1 -> "TChar" 
  | TY_Iden1 (str) -> "TIdent (" ^ pp_ty_Iden1 str ^ ")" 
  | TY_PTR1 (y) -> "TPoint ( " ^ pp_ty_type1 y  ^ " )" 




  let rec pp_expr1 = function
  | EInt1(i) ->  "EInt (" ^ (sprintf "%d" i) ^ ")"
  | EString1(s) ->  "EString (" ^ (sprintf "\"%s\"" s) ^ ")"
  | EChar1(c) ->  "EChar (" ^ (sprintf "\'%s\'" c)  ^ ")"
  | EVar1(r) ->  "EVar (" ^ (pp_ty_Iden1 r) ^ ")"
  | EBNOp1(op,e1,e2) -> "EBinOp (" ^ (pp_ty_BNOp op) ^ "," ^ (pp_expr1 e1) ^  "," ^ (pp_expr1 e2) ^ ")"
  | EUNOp1(op,e) ->  "EUnOp (" ^ (pp_ty_UNOp op) ^ "," ^ (pp_expr1 e) ^ ")" 
  | ECall1(id, args) -> 
    "ECall (" ^ (pp_ty_Iden1 id) ^ ", {" ^ (pp_helper_expr1 args)^ "})"
  | Enew1(ty,e) -> "ENew" ^ "(" ^ (pp_ty_type1 ty) ^ "," ^ (pp_expr1 e) ^ ")"
  | EArrayAccess1(id, index_expr, opt_id) ->
    "EArrayAccess (" ^ (pp_ty_Iden1 id) ^ ", " ^ (pp_expr1 index_expr) ^ ", " ^
    (match opt_id with   
     | None -> ""
     | Some ty_id ->  (pp_ty_Iden1 ty_id)) ^ ")"
and pp_helper_expr1 = function
| [] -> ""
| x::xn -> (if List.length xn<>0 then ((pp_expr1 x) ^ " " ^ (pp_helper_expr1 xn)) else (pp_expr1 x))







