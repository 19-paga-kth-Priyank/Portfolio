
open Printf
open Lexer
open Ast

exception ParseError of string * int

let fail_handler (msg, tokens) =
   let ln_no =
     match tokens with
     | [] -> -1 (* Default line number if no tokens are available *)
     | first_token :: _ -> extract_line_number first_token
   in
   raise (ParseError (msg, ln_no+1))
 

 
 (* Helper function to match a single token and return its type *)
 let help_typ_mat token =
   match token with
   | Tok_int _ -> TY_INT
   | Tok_char _ -> TY_CHAR
   | Tok_void _ -> TY_VOID
   | Tok_iden (s, ln) -> TY_Iden (Iden_name (s, ln))  (* Include both identifier name and line number *)
   | _ -> printf "%s" (pprint_token token) ;fail_handler ("Unknown base type", [token])
 
 (* Recursive function to handle pointer types *)
 let rec rem_ptr ty tokens =
   match tokens with
   | Tok_MUL ln :: rest ->
       (* Wrap the type in a pointer and continue parsing *)
       let (rest2, inner_type) = rem_ptr (TY_PTR(ty)) rest in
       (rest2, inner_type)
   | _ -> (tokens, ty)  (* Base case: return remaining tokens and the type *)
 
 (* Main function to parse a type *)
 let rec type_matcher tokens =
   match tokens with
   | t1 :: Tok_MUL ln :: rest ->
       (* Match the base type and process pointers *)
       let base_type = help_typ_mat t1 in
       rem_ptr base_type (Tok_MUL ln :: rest)
   | t1 :: rest ->
       (* Match a single base type without pointers *)
       (rest, help_typ_mat t1)
   | _ -> fail_handler ("Unknown type", tokens)  (* Catch-all error case *)
 
 
let rec parse_expr_factor tokens = 
   match tokens with    
   | Tok_iden (func_name, ln) :: Tok_SEP_LParen _ :: rest -> 
         (* Parse function call *)
         let (rest2, args) = parse_arguments_expr rest in
         (rest2, ECall (Iden_name (func_name, ln), args))
   
   | Tok_iden (name, ln) :: Tok_SEP_LBox _ :: rest -> 
         (* Parsing an array access: Ident "[" expr "]" *)
         let (rest_after_expr, index_expr) = parse_expr rest in
         (match rest_after_expr with
         | Tok_SEP_RBox _ :: Tok_ACC_DOT _ :: Tok_iden (field, field_ln) :: rest_final ->
            (* Handle array access followed by field access (e.g., a[5].field) *)
            (rest_final, EArrayAccess (Iden_name (name, ln), index_expr, Some (Iden_name (field, field_ln))))
         | Tok_SEP_RBox _ :: rest_final ->
            (* Handle just array access (e.g., a[5]) *)
            (rest_final, EArrayAccess (Iden_name (name, ln), index_expr, None))
         | _ -> fail_handler ("Expected ] after array index", rest_after_expr))
   
   | Tok_new _ :: tokens -> 
         (* Handle pointers and allocations *)
         let (rest_after_type, ty) = type_matcher tokens in
         (match rest_after_type with
         | Tok_SEP_LBox _ :: rest -> 
            (* Parse 'new' ty '[' expr ']' *)
            let (rest2, expr) = parse_expr rest in
            (match rest2 with
               | Tok_SEP_RBox _ :: rest3 -> (rest3, Enew (ty, expr))
               | _ -> fail_handler ("Expected ']' after expression", rest2))
         | _ -> fail_handler ("Expected '[' after type in 'new'", rest_after_type))
   
   | Tok_iden (name, ln) :: rest -> 
         (* Parse identifier *)
         (rest, EVar (Iden_name (name, ln)))
   
   | Tok_int_const (i, ln) :: rest -> 
         (* Parse unsigned integer *)
         (rest, EInt (i))
   
   | Tok_CC_char_const (c, ln) :: rest -> 
         (* Parse character *)
         (rest, EChar (c))
   
   | Tok_Str_const (s, ln) :: rest -> 
         (* Parse string *)
         (rest, EString (s))  
   
   | Tok_SEP_LParen _ :: rest -> 
         (* Parse '(' expr ')' *)
         let (rest2, expr) = parse_expr rest in
         (match rest2 with
         | Tok_SEP_RParen _ :: rest3 -> (rest3, expr)
         | _ -> fail_handler ("Expected ')'", rest2))
   
   | _ -> fail_handler ("Unexpected token in expression", tokens)
   
and parse_unary tokens =
   match tokens with
   | Tok_UN_BW_NOT ln :: next_tokens -> 
         (* Parse unary bitwise NOT *)
         let (tokens2, expr) = parse_unary next_tokens in
         (tokens2, EUNOp (UNOP_BW_Comp, expr,ln))
   
   | Tok_UN_Cnd_NOT ln :: next_tokens -> 
         (* Parse unary logical NOT *)
         let (tokens2, expr) = parse_unary next_tokens in
         (tokens2, EUNOp (UNOP_LG_NOT, expr,ln))
   
   | Tok_SUB ln :: next_tokens -> 
         (* Parse unary minus *)
         let (tokens2, expr) = parse_unary next_tokens in
         (tokens2, EUNOp (UNOP_MINUS, expr,ln))
   
   | _ -> parse_expr_factor tokens
   
and parse_term_7_prime tokens expr =
   match tokens with
   | Tok_MUL ln :: next_tokens -> 
         let (tokens2, expr2) = parse_unary next_tokens in
         parse_term_7_prime tokens2 (EBNOp (BNOP_MUL, expr, expr2,ln))
   
   | Tok_BN_DIV ln :: next_tokens -> 
         let (tokens2, expr2) = parse_unary next_tokens in
         parse_term_7_prime tokens2 (EBNOp (BNOP_DIV, expr, expr2,ln))
   
   | Tok_BN_MOD ln :: next_tokens -> 
         let (tokens2, expr2) = parse_unary next_tokens in
         parse_term_7_prime tokens2 (EBNOp (BNOP_MOD, expr, expr2,ln))
   
   | _ -> (tokens, expr)
   
and parse_term_7 tokens =
   let (tokens2, expr) = parse_unary tokens in
   parse_term_7_prime tokens2 expr
   
and parse_term_6_prime tokens expr =
   match tokens with
   | Tok_BN_ADD ln :: next_tokens -> 
         let (tokens2, expr2) = parse_term_7 next_tokens in
         parse_term_6_prime tokens2 (EBNOp (BNOP_ADD, expr, expr2,ln))
   
   | Tok_SUB ln :: next_tokens -> 
         let (tokens2, expr2) = parse_term_7 next_tokens in
         parse_term_6_prime tokens2 (EBNOp (BNOP_SUB, expr, expr2,ln))
   
   | _ -> (tokens, expr)
   
and parse_term_6 tokens =
   let (tokens2, expr) = parse_term_7 tokens in
   parse_term_6_prime tokens2 expr
   
and parse_term_5_prime tokens expr =
   match tokens with
   | Tok_BW_LS ln :: next_tokens -> 
         let (tokens2, expr2) = parse_term_6 next_tokens in
         parse_term_5_prime tokens2 (EBNOp (BNOP_BW_LS, expr, expr2,ln))
   
   | Tok_BW_RS ln :: next_tokens -> 
         let (tokens2, expr2) = parse_term_6 next_tokens in
         parse_term_5_prime tokens2 (EBNOp (BNOP_BW_RS, expr, expr2,ln))
   
   | _ -> (tokens, expr)
   
and parse_term_5 tokens =
   let (tokens2, expr) = parse_term_6 tokens in
   parse_term_5_prime tokens2 expr
   
and parse_term_4_prime tokens expr =
   match tokens with
   | Tok_LG_GT ln :: next_tokens -> 
         let (tokens2, expr2) = parse_term_5 next_tokens in
         parse_term_4_prime tokens2 (EBNOp (BNOP_LG_GT, expr, expr2,ln))
   
   | Tok_LG_LT ln :: next_tokens -> 
         let (tokens2, expr2) = parse_term_5 next_tokens in
         parse_term_4_prime tokens2 (EBNOp (BNOP_LG_LT, expr, expr2,ln))
   
   | Tok_LG_GTET ln :: next_tokens -> 
         let (tokens2, expr2) = parse_term_5 next_tokens in
         parse_term_4_prime tokens2 (EBNOp (BNOP_LG_GTET, expr, expr2,ln))
   
   | Tok_LG_LTET ln :: next_tokens -> 
         let (tokens2, expr2) = parse_term_5 next_tokens in
         parse_term_4_prime tokens2 (EBNOp (BNOP_LG_LTET, expr, expr2,ln))
   
   | _ -> (tokens, expr)
   
and parse_term_4 tokens =
   let (tokens2, expr) = parse_term_5 tokens in
   parse_term_4_prime tokens2 expr
   
and parse_term_3_prime tokens expr =
   match tokens with
   | Tok_LG_Not_ET ln :: next_tokens -> 
         let (tokens2, expr2) = parse_term_4 next_tokens in
         parse_term_3_prime tokens2 (EBNOp (BNOP_LG_NET, expr, expr2,ln))
   
   | Tok_LG_IS_ET ln :: next_tokens -> 
         let (tokens2, expr2) = parse_term_4 next_tokens in
         parse_term_3_prime tokens2 (EBNOp (BNOP_LG_ET, expr, expr2,ln))
   
   | _ -> (tokens, expr)
   
and parse_term_3 tokens =
   let (tokens2, expr) = parse_term_4 tokens in
   parse_term_3_prime tokens2 expr
   
and parse_term_2_prime tokens expr =
   match tokens with
   | Tok_BW_AND ln :: next_tokens -> 
         let (tokens2, expr2) = parse_term_3 next_tokens in
         parse_term_2_prime tokens2 (EBNOp (BNOP_BW_AND, expr, expr2,ln))
   
   | _ -> (tokens, expr)
   
and parse_term_2 tokens =
   let (tokens2, expr) = parse_term_3 tokens in
   parse_term_2_prime tokens2 expr
   
and parse_term_1_prime tokens expr =
   match tokens with
   | Tok_BW_OR ln :: next_tokens -> 
         let (tokens2, expr2) = parse_term_2 next_tokens in
         parse_term_1_prime tokens2 (EBNOp (BNOP_BW_OR, expr, expr2,ln))
   
   | _ -> (tokens, expr)
   
and parse_term_1 tokens =
   let (tokens2, expr) = parse_term_2 tokens in
   parse_term_1_prime tokens2 expr
   
and parse_term_0_prime tokens expr =
   match tokens with
   | Tok_LG_AND ln :: next_tokens -> 
         let (tokens2, expr2) = parse_term_1 next_tokens in
         parse_term_0_prime tokens2 (EBNOp (BNOP_LG_AND, expr, expr2,ln))
   
   | _ -> (tokens, expr)
   
and parse_term_0 tokens =
   let (tokens2, expr) = parse_term_1 tokens in
   parse_term_0_prime tokens2 expr
   
and parse_expr_prime tokens expr =
   match tokens with
   | Tok_LG_OR ln :: next_tokens -> 
         let (tokens2, expr2) = parse_term_0 next_tokens in
         parse_expr_prime tokens2 (EBNOp (BNOP_LG_OR, expr, expr2,ln))
   
   | _ -> (tokens, expr)
   
and parse_expr tokens =
   let (tokens2, expr) = parse_term_0 tokens in
   parse_expr_prime tokens2 expr
   
and parse_arguments_expr tokens =
   match tokens with
   | Tok_SEP_RParen _ :: rest -> (rest, []) (* End of argument list *)
   | _ ->
         let (rest2, arg) = parse_expr tokens in
         let (rest3, args) =
         (match rest2 with
            | Tok_SEP_Comma _ :: rest3 -> parse_arguments_expr rest3 (* Continue parsing more arguments *)
            | Tok_SEP_RParen _ :: rest3 -> (rest3, []) (* End of arguments *)
            | _ -> fail_handler ("Expected ',' or ')' in function arguments", rest2))
         in
         (rest3, arg :: args)
       


   let rec parse_stmt tokens =
   (match tokens with
   (* Parse block: stmt → "{" { stmt } "}" *)
   | Tok_SEP_LCurly ln :: rest ->
      let (rest_after_block, stmts) = parse_stmt_list rest in
      (match rest_after_block with
      | Tok_SEP_RCurly _ :: rest_final -> (rest_final, SScope stmts)
      | _ -> fail_handler ("Expected '}' to close block", rest_after_block))
  
  (* Parse standalone assignments: assign → lvalue "=" expr | lvalue "++" | lvalue "--" *)
  | Tok_iden (name, ln) :: Tok_SEP_LParen _ :: rest ->
      let (sexpr_parse_rest, sexpr) = parse_expr (Tok_iden (name, ln) :: Tok_SEP_LParen ln :: rest) in
      (match sexpr_parse_rest with
      | Tok_SEP_Semi _ :: rest_final -> (rest_final, SExpr (sexpr))
      | _ -> fail_handler ("; expected in the expression statement", sexpr_parse_rest))
  
  | Tok_iden (name, ln) :: Tok_SEP_LBox _ :: rest ->
      let (after_created_lval, created_expr_lval) = parse_expr rest in
      (match after_created_lval with
      | Tok_SEP_RBox _ :: Tok_ACC_DOT _ :: Tok_iden (field, ln_field) :: rest_final ->
          (match rest_final with
          | Tok_ASS_EQ _ :: rest_expr ->
              let (rest_after_expr, expr) = parse_expr rest_expr in
              (match rest_after_expr with
              | Tok_SEP_Semi _ :: rest_final ->
                  (rest_final, SArrayAssign (Iden_name (name, ln), created_expr_lval, Some (Iden_name (field, ln_field)), expr))
              | _ -> fail_handler ("Expected ';' after assignment", rest_after_expr))
          | Tok_SEP_LParen _ :: rest_expr ->
              let (rest_after_expr, expr) = parse_expr (Tok_iden (name, ln) :: Tok_SEP_LParen ln :: rest_expr) in
              (match rest_after_expr with
              | Tok_SEP_RParen _ :: restx ->
                  (restx, SExpr expr)
              | _ -> fail_handler ("Expected ')' after expression", rest_after_expr))
          | Tok_UN_INC_OP ln :: Tok_SEP_Semi _ :: rest_final ->
              (rest_final, SArrayAssign (Iden_name (name, ln), created_expr_lval, Some (Iden_name (field, ln_field)), EBNOp (BNOP_ADD, EArrayAccess (Iden_name (name, ln), created_expr_lval, Some (Iden_name (field, ln_field))), EInt 1,ln)))
          | Tok_UN_DEC_OP ln :: Tok_SEP_Semi _ :: rest_final ->
              (rest_final, SArrayAssign (Iden_name (name, ln), created_expr_lval, Some (Iden_name (field, ln_field)), EBNOp (BNOP_SUB, EArrayAccess (Iden_name (name, ln), created_expr_lval, Some (Iden_name (field, ln_field))), EInt 1,ln)))
          | _ -> fail_handler ("Invalid assignment or missing ';' --> ", rest_final))
      | Tok_SEP_RBox _ :: rest_final ->
          (match rest_final with
          | Tok_ASS_EQ _ :: rest_expr ->
              let (rest_after_expr, expr) = parse_expr rest_expr in
              (match rest_after_expr with
              | Tok_SEP_Semi _ :: rest_final ->
                  (rest_final, SArrayAssign (Iden_name (name, ln), created_expr_lval, None, expr))
              | _ -> fail_handler ("Expected ';' after assignment", rest_after_expr))
          | Tok_SEP_LParen _ :: rest_expr ->
              let (rest_after_expr, expr) = parse_expr (Tok_iden (name, ln) :: Tok_SEP_LParen ln :: rest_expr) in
              (match rest_after_expr with
              | Tok_SEP_RParen _ :: restx ->
                  (restx, SExpr expr)
              | _ -> fail_handler ("Expected ')' after expression", rest_after_expr))
          | Tok_UN_INC_OP ln_inc :: Tok_SEP_Semi _ :: rest_final ->
              (rest_final, SArrayAssign (Iden_name (name, ln), created_expr_lval, None, EBNOp (BNOP_ADD, EArrayAccess (Iden_name (name, ln), created_expr_lval, None), EInt 1,ln_inc)))
          | Tok_UN_DEC_OP ln_dec :: Tok_SEP_Semi _ :: rest_final ->
              (rest_final, SArrayAssign (Iden_name (name, ln), created_expr_lval, None, EBNOp (BNOP_SUB, EArrayAccess (Iden_name (name, ln), created_expr_lval, None), EInt 1, ln_dec)))
          | _ -> fail_handler ("Invalid assignment or missing ';' --> ", rest_final))
      | _ -> fail_handler ("Invalid array access", tokens))




(* Parse conditional: stmt → "if" "(" expr ")" stmt [ "else" stmt ] *)
   | Tok_if ln_if :: Tok_SEP_LParen ln_lp :: rest ->
      let (rest_after_cond, condition) = parse_expr rest in
      (match rest_after_cond with
      | Tok_SEP_RParen ln_rp :: rest_then ->
          let (rest_after_then, then_stmt) = parse_stmt rest_then in
          (match rest_after_then with
          | Tok_else ln_else :: rest_else ->
              let (rest_after_else, else_stmt) = parse_stmt rest_else in
              (rest_after_else, SIf (condition, then_stmt, Some else_stmt))
          | _ -> (rest_after_then, SIf (condition, then_stmt, None)))
      | _ -> fail_handler ("Expected ')' after condition", rest_after_cond))
  
  (* Parse loop: stmt → "while" "(" expr ")" stmt *)
  | Tok_while ln_while :: Tok_SEP_LParen ln_lp :: rest ->
      let (rest_after_cond, condition) = parse_expr rest in
      (match rest_after_cond with
      | Tok_SEP_RParen ln_rp :: rest_body ->
          let (rest_after_body, body_stmt) = parse_stmt rest_body in
          (rest_after_body, SWhile (condition, body_stmt))
      | _ -> fail_handler ("Expected ')' after while condition", rest_after_cond))
  
  (* Parse break: stmt → "break" ";" *)
  | Tok_break ln_break :: Tok_SEP_Semi ln_semi :: rest -> (rest, SBreak)
  
  (* Parse return: stmt → "return" [ expr ] ";" *)
  | Tok_return ln_return :: rest ->
      let (rest_after_expr, expr_option) =
          (match rest with
          | Tok_SEP_Semi ln_semi :: rest_final -> (rest_final, None)
          | _ ->
              let (rest_expr, expr) = parse_expr rest in
              (match rest_expr with
              | Tok_SEP_Semi ln_semi :: rest_final -> (rest_final, Some expr)
              | _ -> fail_handler ("Expected ';' after return expression", rest_expr)))
      in
      (rest_after_expr, SReturn (expr_option,ln_return))
  
  (* Parse delete: stmt → "delete" "[" "]" Ident ";" *)
  | Tok_delete ln_delete :: rest1->
     (match rest1 with 
      | Tok_SEP_LBox ln_lb :: Tok_SEP_RBox ln_rb :: rest2 ->
         (match rest2 with
         | Tok_iden (name, ln_name) :: rest3 -> 
            (match rest3 with
            | Tok_SEP_Semi ln_semi :: rest4 ->
               (rest4, SDelete (Iden_name (name, ln_name),ln_delete))
            | _ -> fail_handler ("; missing", rest3))
         | _ -> fail_handler ("Identifier missing" , rest2))
      | _ -> fail_handler("Box [] missing", rest1))
  
  
    
  
  (* Parse for loop: stmt → "for" "(" varassign ";" expr ";" assign ")" stmt *)
  
  | Tok_for (ln_for) :: rest_x ->
   (match rest_x with
   | Tok_SEP_LParen ln_lparen :: rest ->
      let (rest_after_varassign, init_stmt) = parse_stmt rest in
      let (rest_after_condition, condition) = parse_expr rest_after_varassign in
      let (rest_after_assign_loop, assign) =
         (match rest_after_condition with
         | Tok_SEP_Semi ln_semi :: Tok_iden (name, ln_name) :: Tok_SEP_LBox ln_lbox :: rest_assign ->
            let (after_created_lval, created_expr_lval) = parse_expr rest_assign in
               (match after_created_lval with
               | Tok_SEP_RBox ln_rbox :: Tok_ACC_DOT ln_dot :: Tok_iden (field, ln_field) :: rest_final ->
                  (match rest_final with 
                   | Tok_ASS_EQ ln_eq :: rest_expr ->
                      let (rest_after_expr, expr) = parse_expr rest_expr in
                      (match rest_after_expr with
                       | Tok_SEP_RParen ln_rparen :: rest_final ->
                          (rest_final, SArrayAssign (Iden_name (name, ln_name), created_expr_lval, Some (Iden_name (field, ln_field)), expr))
                       | _ -> fail_handler ("Expected ';' after assignment", rest_after_expr))
                   | Tok_SEP_LParen ln_inner_lparen :: rest_expr -> 
                      let (rest_after_expr, expr) = parse_expr (Tok_iden (name, ln_name) :: Tok_SEP_LParen ln_inner_lparen :: rest_expr) in 
                      (match rest_after_expr with 
                      | Tok_SEP_RParen ln_inner_rparen :: restx ->
                         (restx, SExpr(expr))
                      | _ -> fail_handler(") after expr ", rest_after_expr))
                   | Tok_UN_INC_OP ln_inc :: Tok_SEP_RParen ln_rparen :: rest_final ->
                      (rest_final, SArrayAssign (Iden_name (name, ln_name), created_expr_lval, Some (Iden_name (field, ln_field)), EBNOp (BNOP_ADD, EArrayAccess (Iden_name (name, ln_name), created_expr_lval, Some (Iden_name (field, ln_field))), EInt 1,ln_inc)))
                   | Tok_UN_DEC_OP ln_dec :: Tok_SEP_RParen ln_rparen :: rest_final ->
                      (rest_final, SArrayAssign (Iden_name (name, ln_name), created_expr_lval, Some (Iden_name (field, ln_field)), EBNOp (BNOP_SUB, EArrayAccess (Iden_name (name, ln_name), created_expr_lval, Some (Iden_name (field, ln_field))), EInt 1,ln_dec)))
                   | _ -> fail_handler ("Invalid assignment or missing ';' --> " , rest_final))
                   
               | Tok_SEP_RBox ln_rbox :: rest_final ->
                  (match rest_final with 
                   | Tok_ASS_EQ ln_eq :: rest_expr ->
                      let (rest_after_expr, expr) = parse_expr rest_expr in
                      (match rest_after_expr with
                       | Tok_SEP_RParen ln_rparen :: rest_final ->
                          (rest_final, SArrayAssign (Iden_name (name, ln_name), created_expr_lval, None, expr))
                       | _ -> fail_handler ("Expected ';' after assignment", rest_after_expr))
                   | Tok_SEP_LParen ln_inner_lparen :: rest_expr -> 
                      let (rest_after_expr, expr) = parse_expr (Tok_iden (name, ln_name) :: Tok_SEP_LParen ln_inner_lparen :: rest_expr) in 
                      (match rest_after_expr with 
                      | Tok_SEP_RParen ln_inner_rparen :: restx ->
                         (restx, SExpr(expr))
                      | _ -> fail_handler(") after expr ", rest_after_expr))
                   | Tok_UN_INC_OP ln_inc :: Tok_SEP_RParen ln_rparen :: rest_final ->
                      (rest_final, SArrayAssign (Iden_name (name, ln_name), created_expr_lval, None, EBNOp (BNOP_ADD, EArrayAccess (Iden_name (name, ln_name), created_expr_lval, None), EInt 1,ln_inc)))
                   | Tok_UN_DEC_OP ln_dec :: Tok_SEP_RParen ln_rparen :: rest_final ->
                      (rest_final, SArrayAssign (Iden_name (name, ln_name), created_expr_lval, None, EBNOp (BNOP_SUB, EArrayAccess (Iden_name (name, ln_name), created_expr_lval, None), EInt 1, ln_dec)))
                   | _ -> fail_handler ("Invalid assignment or missing ';' --> " , rest_final))
                  | _ -> fail_handler ("Invalid array_access", after_created_lval))

         | Tok_SEP_Semi ln_semi :: Tok_iden (name, ln_name) :: rest_assign ->
            (match rest_assign with
             | Tok_ASS_EQ ln_eq :: rest_expr ->
                let (rest_after_expr, expr) = parse_expr rest_expr in
                (match rest_after_expr with
                 | Tok_SEP_RParen ln_rparen :: rest_final ->
                    (rest_final, SVarAssign (Iden_name (name, ln_name), expr))
                 | _ -> fail_handler ("Expected ';' after assignment", rest_after_expr))
             | Tok_SEP_LParen ln_inner_lparen :: rest_expr -> 
                let (rest_after_expr, expr) = parse_expr (Tok_iden (name, ln_name) :: Tok_SEP_LParen ln_inner_lparen :: rest_expr) in 
                (match rest_after_expr with 
                | Tok_SEP_RParen ln_inner_rparen :: restx ->
                   (restx, SExpr(expr))
                | _ -> fail_handler(") after expr ", rest_after_expr))
             | Tok_UN_INC_OP ln_inc :: Tok_SEP_RParen ln_rparen :: rest_final ->
                (rest_final, SVarAssign (Iden_name (name, ln_name), EBNOp (BNOP_ADD, EVar (Iden_name (name, ln_name)), EInt 1, ln_inc)))
             | Tok_UN_DEC_OP ln_dec :: Tok_SEP_RParen ln_rparen :: rest_final ->
                (rest_final, SVarAssign (Iden_name (name, ln_name), EBNOp (BNOP_SUB, EVar (Iden_name (name, ln_name)), EInt 1, ln_dec)))
             | _ -> fail_handler ("Invalid assignment or missing ';'", rest_assign))
         | _ -> fail_handler ("Invalid update condition in for loop", rest_after_condition))
      
      in
      let (rest_after_loop, loop_construct) = parse_stmt rest_after_assign_loop in
      (rest_after_loop, SScope [init_stmt; SWhile (condition, SScope [loop_construct; assign])])
   | _ -> fail_handler ("( expected after for", rest_x))

   | Tok_iden (name, ln_name) :: Tok_ASS_EQ ln_eq :: rest_expr ->
      let (rest_after_expr, expr) = parse_expr rest_expr in
      (match rest_after_expr with
      | Tok_SEP_Semi ln_semi :: rest_final ->
         (rest_final, SVarAssign (Iden_name (name, ln_name), expr))
      | _ -> fail_handler ("Expected ';' after assignment", rest_after_expr))
   | Tok_iden (name, ln_name) :: Tok_UN_INC_OP ln_inc :: Tok_SEP_Semi ln_semi :: rest_final ->
      (rest_final, SVarAssign (Iden_name (name, ln_name), EBNOp (BNOP_ADD, EVar (Iden_name (name, ln_name)), EInt 1,ln_inc)))
   | Tok_iden (name, ln_name) :: Tok_UN_DEC_OP ln_dec :: Tok_SEP_Semi ln_semi :: rest_final ->
      (rest_final, SVarAssign (Iden_name (name, ln_name), EBNOp (BNOP_SUB, EVar (Iden_name (name, ln_name)), EInt 1, ln_dec)))
   

   (* Parse variable assignment: varassign → ty Ident "=" expr ";" *)
   
   | x :: rest_tokens ->
      let (rest_after_type, typ) = type_matcher (x :: rest_tokens) in
      (match rest_after_type with
      | Tok_iden (name, ln_name) :: Tok_ASS_EQ ln_eq :: rest ->
         (* Parse the right-hand side expression of the assignment *)
         let (rest_after_expr, expr) = parse_expr rest in
         (match rest_after_expr with
         | Tok_SEP_Semi ln_semi :: rest_final ->
            (* If semicolon is found, create the variable definition *)
            (rest_final, SVarDef (typ, Iden_name (name, ln_name), expr))
         | _ -> fail_handler ("Expected ';' after variable assignment", rest_after_expr))
      | _ -> fail_handler ("Expected variable assignment", rest_after_type))
   
   (* Fallback case for invalid statements *)
   | _ -> fail_handler ("Invalid statement", tokens))
   
   and parse_stmt_list tokens =
      (match tokens with
      | Tok_SEP_RCurly ln_rcurly :: _ -> (tokens, [])
      | _ ->
            let (rest, stmt) = parse_stmt tokens in
            let (rest_after_list, stmt_list) = parse_stmt_list rest in
            (rest_after_list, stmt :: stmt_list))

(* Assume parse_expr is already defined. *)


let rec parse_global tokens =
  match tokens with

  | Tok_extern ln :: typ ->
      let (rest_after_type, ty) = type_matcher typ in
      (match rest_after_type with
      | Tok_iden (name, ln_name) :: rest ->
          (match rest with
          | Tok_SEP_Semi _ :: rest_tokens -> (rest_tokens, GVarDecl (ty, Iden_name (name, ln_name)))
          | Tok_SEP_LParen _ :: rest_tokens2 ->
              let (rest2, ast_params_list) = parse_arg_params rest_tokens2 in
              (match rest2 with
              | Tok_SEP_Semi _ :: rest3 -> (rest3, GFuncDecl (ty, Iden_name (name, ln_name), ast_params_list))
              | _ -> fail_handler ("Expected ';' after function declaration", rest2))
          | _ -> fail_handler ("Invalid global extern declaration", rest))
      | _ -> fail_handler ("Invalid type for extern declaration", rest_after_type))

  | Tok_struct ln :: Tok_iden (name, ln_name) :: Tok_SEP_LCurly _ :: rest ->
      let (rest2, struct_p) = create_struct_tuple rest in
      (rest2, GStruct (Iden_name (name, ln_name), struct_p))

  
  
      | x :: rest_tokens ->
      let (rest_after_type, typ) = type_matcher (x :: rest_tokens) in
      (match rest_after_type with
      | Tok_iden (name, ln) :: Tok_SEP_LParen _ :: rest_tokens2 ->
          let (rest2, ast_params_list) = parse_arg_params rest_tokens2 in
          (match rest2 with
          | Tok_SEP_LCurly _ :: rest3 ->
              let (rest4, ast_stmt_tree) = parse_stmt (Tok_SEP_LCurly ln :: rest3) in
              (rest4, GFuncDef (typ, Iden_name (name, ln), ast_params_list, ast_stmt_tree))
          | Tok_SEP_Semi _ :: rest3 -> (rest3, GFuncDecl (typ, Iden_name (name, ln), ast_params_list))
          | _ -> fail_handler ("Invalid function declaration or definition", rest2))
      | Tok_iden (name, ln) :: Tok_ASS_EQ _ :: rest_tokens2 ->
          let (rest2, ast_expr) = parse_expr rest_tokens2 in
          (match rest2 with
          | Tok_SEP_Semi _ :: rest3 -> (rest3, GVarDef (typ, Iden_name (name, ln), ast_expr))
          | _ -> fail_handler ("Expected ';' after variable definition", rest2))
      | _ -> fail_handler ("Invalid global assignment or lvalue", rest_after_type))

  | _ -> fail_handler ("Invalid global declaration", tokens)

and create_struct_tuple tokens =
  match tokens with
  | Tok_SEP_RCurly _ :: Tok_SEP_Semi _ :: rest -> (rest, []) (* End of struct field list *)
  | Tok_SEP_RCurly _ :: rest -> fail_handler ("Expected ';' after '}' in struct declaration", rest)
  | _ ->
      let (rest2, field) = create_tuple tokens in
      let (rest3, fields) =
        match rest2 with
        | Tok_SEP_RCurly _ :: Tok_SEP_Semi _ :: rest3 -> (rest3, [])
        | Tok_SEP_Semi _ :: rest3 -> create_struct_tuple rest3
        | Tok_SEP_RCurly _ :: rest3 -> fail_handler ("Expected ';' before '}' in struct declaration", rest3)
        | _ -> fail_handler ("Unexpected token in struct field declaration", rest2)
      in
      (rest3, field :: fields)

and parse_arg_params tokens =
  match tokens with
  | Tok_SEP_RParen _ :: rest -> (rest, []) (* End of argument list *)
  | _ ->
      let (rest2, arg) = create_tuple tokens in
      let (rest3, args) =
        match rest2 with
        | Tok_SEP_Comma _ :: rest3 -> parse_arg_params rest3 (* Continue parsing more arguments *)
        | Tok_SEP_RParen _ :: rest3 -> (rest3, []) (* End of arguments *)
        | _ -> fail_handler ("Expected ',' or ')' in function arguments", rest2)
      in
      (rest3, arg :: args)


and create_tuple tokens =
  match tokens with
  | x :: rest_tokens ->
      let (rest_after_type, typ) = type_matcher (x :: rest_tokens) in
      (match rest_after_type with
      | Tok_iden (name, ln) :: rest2 -> (rest2, (typ, Iden_name (name, ln)))
      | _ -> fail_handler ("Expected type followed by identifier", tokens))
  | _ -> fail_handler ("Unexpected type in tuple creation", tokens)


let rec parse_program tokens =
   
  let rec parse_globals tokens acc =
    match tokens with
    | [] -> List.rev acc  (* Return the accumulated list when no more tokens are left *)
    | _ ->
        let (remaining_tokens, global_ast) = parse_global tokens in
        parse_globals remaining_tokens (global_ast :: acc)
  in
  let globals = parse_globals tokens [] in
  Prog(globals)

