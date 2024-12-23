open Printf

type ty_Iden = | Iden_name of string * int

type ty_UNOp = | UNOP_LG_NOT | UNOP_BW_Comp | UNOP_MINUS 
type ty_BNOp = | BNOP_ADD | BNOP_SUB | BNOP_MUL | BNOP_DIV | BNOP_MOD 
               | BNOP_LG_LT | BNOP_LG_GT | BNOP_LG_LTET | BNOP_LG_GTET | BNOP_LG_ET | BNOP_LG_NET | BNOP_LG_AND | BNOP_LG_OR 
               | BNOP_BW_OR | BNOP_BW_AND | BNOP_BW_LS | BNOP_BW_RS 
type ty_type = | TY_VOID | TY_INT | TY_CHAR  | TY_Iden of ty_Iden  | TY_PTR of ty_type
 

type expr = 
  | EInt of int | EString of string | EChar of string  | EVar of ty_Iden
  | EBNOp of ty_BNOp * expr * expr * int
  | EUNOp of ty_UNOp * expr * int
  | ECall of ty_Iden * (expr list)
  | Enew of ty_type * expr
  | EArrayAccess of ty_Iden * expr * (ty_Iden option) (* optional type is for structure array access *)

type stmt = 

  | SExpr of expr
  | SVarDef of ty_type * ty_Iden * expr
  | SVarAssign of ty_Iden * expr 
  | SArrayAssign of ty_Iden * expr * (ty_Iden option) * expr
  | SScope of (stmt list) (*<- Need to work in recursive statement calls  *)
  | SIf of expr * stmt *(stmt option)
  | SWhile of expr * stmt               (*  For loop needs to parsed as a while loop*)
  | SBreak
  | SReturn of (expr option) * int
  | SDelete of ty_Iden * int

type global = 
  | GFuncDef of ty_type * ty_Iden * ((ty_type * ty_Iden) list) * stmt (* for curly braces checking parse as SScope *)
  | GFuncDecl of ty_type * ty_Iden * ((ty_type * ty_Iden) list) (* Need to parse with extern keywd *)
  | GVarDef of ty_type * ty_Iden * expr                           (* Always has an initial value *)
  | GVarDecl of ty_type * ty_Iden                                 (*| ty Ident "=" expr ";"| "extern" ty Ident ";"* syntax valid for both Def and Decl *)
  | GStruct of ty_Iden * ((ty_type * ty_Iden) list)                (* Only Decln no defn i.e. no defined values can be given b *)

type program = 
  | Prog of (global list)


let pp_ty_Iden = function
  | Iden_name (s,_) -> sprintf "\"%s\"" s

let pp_ty_UNOp = function
  | UNOP_LG_NOT -> "!"
  | UNOP_BW_Comp -> "~"
  | UNOP_MINUS -> "-"

let pp_ty_BNOp = function
  | BNOP_ADD -> "+"| BNOP_SUB -> "-" | BNOP_MUL -> "*" | BNOP_DIV -> "/" | BNOP_MOD -> "%" 
  | BNOP_LG_LT -> "<" | BNOP_LG_GT -> ">" | BNOP_LG_LTET -> "<=" | BNOP_LG_GTET -> ">=" | BNOP_LG_ET -> "==" | BNOP_LG_NET -> "!=" | BNOP_LG_AND -> "&&" | BNOP_LG_OR -> "||"
  | BNOP_BW_OR -> "|" | BNOP_BW_AND -> "&" | BNOP_BW_LS -> "<<" | BNOP_BW_RS -> ">>"


let rec pp_ty_type = function
  | TY_VOID -> "TVoid"
  | TY_INT -> "TInt"
  | TY_CHAR -> "TChar" 
  | TY_Iden (str) -> "TIdent (" ^ pp_ty_Iden str ^ ")" 
  | TY_PTR (y) -> "TPoint ( " ^ pp_ty_type y  ^ " )" 

let rec pp_expr = function
  | EInt(i) ->  "EInt (" ^ (sprintf "%d" i) ^ ")"
  | EString(s) ->  "EString (" ^ (sprintf "\"%s\"" s) ^ ")"
  | EChar(c) ->  "EChar (" ^ (sprintf "\'%s\'" c)  ^ ")"
  | EVar(r) ->  "EVar (" ^ (pp_ty_Iden r) ^ ")"
  | EBNOp(op,e1,e2,_) -> "EBinOp (" ^ (pp_ty_BNOp op) ^ "," ^ (pp_expr e1) ^  "," ^ (pp_expr e2) ^ ")"
  | EUNOp(op,e,_) ->  "EUnOp (" ^ (pp_ty_UNOp op) ^ "," ^ (pp_expr e) ^ ")" 
  | ECall(id, args) -> 
    "ECall (" ^ (pp_ty_Iden id) ^ ", {" ^ (pp_helper_expr args)^ "})"
  | Enew(ty,e) -> "ENew" ^ "(" ^ (pp_ty_type ty) ^ "," ^ (pp_expr e) ^ ")"
  | EArrayAccess(id, index_expr, opt_id) ->
    "EArrayAccess (" ^ (pp_ty_Iden id) ^ ", " ^ (pp_expr index_expr) ^ ", " ^
    (match opt_id with   
     | None -> ""
     | Some ty_id ->  (pp_ty_Iden ty_id)) ^ ")"
and pp_helper_expr = function
| [] -> ""
| x::xn -> (if List.length xn<>0 then ((pp_expr x) ^ " " ^ (pp_helper_expr xn)) else (pp_expr x))

let rec pp_stmt = function
  | SExpr (e) -> "SExpr (" ^ (pp_expr e) ^")"
  | SVarDef (ty,id,e) -> "SVarDef (" ^ (pp_ty_type ty) ^ "," ^ (pp_ty_Iden id) ^ "," ^ (pp_expr e) ^")"
  | SVarAssign (id , e) -> "SVarAssign (" ^ (pp_ty_Iden id) ^ "," ^ (pp_expr e) ^ ")"

  | SArrayAssign (id, e1 , op_id , e2) -> "SArrayAssign ( " ^ (pp_ty_Iden id) ^ "," ^ (pp_expr e1)  ^ "," ^ 
    (match op_id with
    | None -> ","
    | Some ty_id-> (pp_ty_Iden ty_id) ^ ", ") ^
    (pp_expr e2) ^")"

  | SScope (arg) -> "SScope ({" ^ (pp_helper_stmt arg) ^ "})" 
  
  | SIf(e, arg, op_arg) -> "SIf (" ^ (pp_expr e) ^ "," ^ (pp_stmt arg) ^ "," ^
  (match op_arg with
    | Some ty_arg->  (pp_stmt ty_arg)
    | None -> "") ^ ")"
  | SWhile(e,arg) -> "SWhile (" ^ (pp_expr e) ^ "," ^ (pp_stmt arg) ^ ")"             (*  For loop needs to parsed as a while loop and statement can only be SScope*)
  | SBreak -> "SBreak"
  | SReturn(op_e,_) -> "SReturn(" ^
    ( match op_e with
      | None -> ""
      | Some ty_e->  (pp_expr ty_e) 
    ) ^ ")"
  | SDelete(id,_) -> "SDelete (" ^ (pp_ty_Iden id) ^ ")"
and pp_helper_stmt = function
| [] -> ""
| x::xn -> (if List.length xn<>0 then ((pp_stmt x) ^ (pp_helper_stmt xn)) else (pp_stmt x))


let pp_global = function
| GFuncDef(ty, id, arg_list,arg_stmt ) ->
  "GFuncDef (" ^ (pp_ty_type ty) ^ ", " ^ (pp_ty_Iden id) ^ ", " ^ "{" ^ (String.concat " " (List.map (fun (t, i) -> "(" ^ pp_ty_type t ^ ", " ^ pp_ty_Iden i ^ ")") arg_list)) ^ "}"^ ", " 
  ^ (pp_stmt arg_stmt) ^ ")"

| GFuncDecl (ty, id, arg_list ) ->
  "GFuncDecl (" ^ (pp_ty_type ty) ^ ", " ^ (pp_ty_Iden id) ^ ", " ^ "{" ^ (String.concat " " (List.map (fun (t, i) -> "(" ^ pp_ty_type t ^ ", " ^ pp_ty_Iden i ^ ")") arg_list)) ^ "}"^
 ")" (* Need to parse with extern keywd *)

| GVarDef (ty,id,e) -> "GVarDef (" ^ (pp_ty_type ty) ^ "," ^ (pp_ty_Iden id) ^ "," ^ (pp_expr e) ^")"      (* Always has an initial value *)

| GVarDecl (ty,id) -> "GVarDecl (" ^ (pp_ty_type ty) ^ "," ^ (pp_ty_Iden id) ^")"       (*| ty Ident "=" expr ";"| "extern" ty Ident ";"* syntax valid for both Def and Decl *)

| GStruct (id, arg_list ) -> "GStruct (" ^ (pp_ty_Iden id) ^ ",{" ^ (String.concat "" (List.map (fun (t, i) -> "(" ^ pp_ty_type t ^ ", " ^ pp_ty_Iden i ^ ")") arg_list)) ^ "})"

(* Only Decln no defn i.e. no defined values can be given b *)

let pp_prog = function
| Prog (g) -> String.concat "\n\n" (List.map pp_global g)