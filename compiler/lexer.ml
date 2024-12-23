
exception LexError of string * int

let fail_handler (msg, ln) =
  raise (LexError (msg, !ln+1))

let ln = ref 0

open Printf

(* Token types *)
(* Type representing the line number *)
type line = int

(* All recognized tokens *)
type token =
  (* Keywords *)
  | Tok_break of line
  | Tok_char of line
  | Tok_extern of line
  | Tok_new of line (* Add in pretty print *)
  | Tok_for of line
  | Tok_delete of line
  | Tok_if of line (* Add in pretty print *)
  | Tok_else of line
  | Tok_int of line
  | Tok_return of line
  | Tok_struct of line
  | Tok_void of line
  | Tok_while of line

  (* Identifier *)
  | Tok_iden of string * line

  (* Integer Constants *)
  | Tok_int_const of int * line

  (* Char Constants *)
  | Tok_CC_char_const of string * line

  (* String Constants *)
  | Tok_Str_const of string * line

  (* Operators *)
  (* Unary operators ~, !, --, ++ *)
  | Tok_UN_BW_NOT of line
  | Tok_UN_Cnd_NOT of line
  (* | Tok_UN_MINUS unary/binary will be decided by the parser *)
  | Tok_UN_DEC_OP of line
  | Tok_UN_INC_OP of line

  (* Binary +, -, *, /, % *)
  | Tok_BN_ADD of line
  | Tok_SUB of line
  | Tok_MUL of line (* PTR and MUL *)
  | Tok_BN_DIV of line
  | Tok_BN_MOD of line

  (* Logical >, <, >=, <=, ==, !=, &&, || *)
  | Tok_LG_GT of line
  | Tok_LG_LT of line
  | Tok_LG_GTET of line
  | Tok_LG_LTET of line
  | Tok_LG_IS_ET of line
  | Tok_LG_Not_ET of line
  | Tok_LG_AND of line
  | Tok_LG_OR of line

  (* Bitwise binary &, |, <<, >> *)
  | Tok_BW_AND of line
  | Tok_BW_OR of line
  | Tok_BW_LS of line
  | Tok_BW_RS of line

  (* Separators: Carriage return, space, and program tabs excluded -> , ; ( ) { } [ ] *)
  | Tok_SEP_Comma of line
  | Tok_SEP_Semi of line
  | Tok_SEP_LParen of line
  | Tok_SEP_RParen of line
  | Tok_SEP_LCurly of line
  | Tok_SEP_RCurly of line
  | Tok_SEP_LBox of line
  | Tok_SEP_RBox of line

  (* Assignment = *)
  | Tok_ASS_EQ of line

  (* Access using . *)
  | Tok_ACC_DOT of line

(* ------------------------------------------------------------------------------- Helper Functions -------------------------------------------------------------------------------- *)

(* Returns longest string prefix matching predicate 'pred' *)
let string_until pred lst =
  let retv a xs = (List.rev a |> List.to_seq |> String.of_seq, xs) in
  let rec work acc = function
    | x::xs -> if pred x then work (x::acc) xs else retv acc (x::xs)
    | [] -> retv acc []
  in work [] lst

(* Predefined predicates *)
let is_digit x = x >= '0' && x <= '9'
let is_letter x = (x = '_') || (x >= 'a' && x <= 'z') || (x >= 'A' && x <= 'Z')
let is_digit_letter x = is_digit x || is_letter x
let hex_extension x = (x >= 'a' && x <= 'f') || (x >= 'A' && x <= 'F')
let is_hex x = is_digit x || hex_extension x
let is_x x = (x = 'x')||(x= 'X')
let is_char c = c >= ' ' && c <= '~' && c <> '\\' && c <> '\'' && c <> '\"'

(* -----------------------------------------------------------------Lexing a list of characters into a list of tokens------------------------------------------------------------ *)

let lexing lst =
  let rec work acc = function
    | '/'::'/'::xs ->  (* Handling comments *)
       let (_, ys) = string_until (fun x -> x <> '\n') xs in
       work acc ys

    | '/'::'*'::xs ->  (* Start of a multi-line comment *)
       let rec skip_comment line_cnt = function
         | [] -> fail_handler ("Lexing error: Unterminated comment", ln)  (* Handle end-of-input without closing comment *)
         | '\n' :: rest -> 
             ln := !ln + 1;  (* Increment the line counter on newline detection *)
             skip_comment (line_cnt + 1) rest
         | '*'::'/'::rest -> 
             line_cnt, rest  (* Found the end of the comment *)
         | '*'::rest -> 
             skip_comment line_cnt rest  (* Continue scanning within the comment *)
         | _::rest -> 
             skip_comment line_cnt rest  (* Continue scanning through the comment content *)
       in
       let _, rest_of_input = skip_comment 0 xs in
       work acc rest_of_input

    | '#'::xs ->  (* Handling preprocessing directives *)
       let (_, ys) = string_until (fun x -> x <> '\n') xs in
       work acc ys

    | '0'::x::xs when is_x x ->  (* Handling hexadecimal *)
       let (y, ys) = string_until is_hex xs in
       let hex_value = "0x" ^ y in
       work (Tok_int_const (int_of_string hex_value, !ln) :: acc) ys

    | '0' :: x ::xs when is_digit x -> 
        fail_handler ("Lexing error: Invalid Integer Literal", ln)

    | x::xs when is_digit x ->  (* Handling digits *)
       let (y, ys) = string_until is_digit (x::xs) in
       work (Tok_int_const (int_of_string y, !ln) :: acc) ys

    | '"'::xs ->  (* Handling string literals *)
       let rec parse_string_literal accum = function
         | '"'::rest -> 
             work (Tok_Str_const (String.concat "" (List.rev accum), !ln) :: acc) rest  (* End of string literal *)
         | '\\'::next::rest -> 
             (match next with
             | 'n' -> parse_string_literal ("\\n"::accum) rest
             | 't' -> parse_string_literal ("\\t"::accum) rest
             | '\\' -> parse_string_literal ("\\\\"::accum) rest
             | '"' -> parse_string_literal ("\\\""::accum) rest
             | '\'' -> parse_string_literal ("\\'"::accum) rest
             | _ -> fail_handler ("Lexing error: invalid escape sequence in string literal", ln))
         | c::rest when is_char c -> 
             parse_string_literal (String.make 1 c :: accum) rest
         | _ -> fail_handler ("Lexing error: unterminated string literal", ln)
       in
       parse_string_literal [] xs

    | '\''::'\\'::x::'\''::xs ->  (* Handling escaped character constants *)
       (match x with
       | 'n' -> work (Tok_CC_char_const ("\\n", !ln) :: acc) xs
       | 't' -> work (Tok_CC_char_const ("\\t", !ln) :: acc) xs
       | '\\' -> work (Tok_CC_char_const ("\\\\", !ln) :: acc) xs
       | '"' -> work (Tok_CC_char_const ("\\\"", !ln) :: acc) xs
       | '\'' -> work (Tok_CC_char_const ("\\\'", !ln) :: acc) xs
       | _ -> fail_handler ("Lexing error: invalid escape sequence", ln))
       
    | '\''::x::'\''::xs ->  (* Character constant enclosed in single quotes *)
       if is_char x then
         work (Tok_CC_char_const (String.make 1 x, !ln) :: acc) xs
       else 
         fail_handler ("Lexing error: invalid character constant", ln)

   | '&'::'&'::xs ->  work (Tok_LG_AND (!ln) :: acc) xs
   | '|'::'|'::xs ->  work (Tok_LG_OR (!ln) :: acc) xs 
   | '='::'='::xs ->  work (Tok_LG_IS_ET (!ln) :: acc) xs 
   | '!'::'='::xs ->  work (Tok_LG_Not_ET (!ln) :: acc) xs 
   | '>'::'='::xs ->  work (Tok_LG_GTET (!ln) :: acc) xs 
   | '<'::'='::xs ->  work (Tok_LG_LTET (!ln) :: acc) xs 

   | '~'::xs -> work (Tok_UN_BW_NOT (!ln) :: acc) xs
   | '!'::xs -> work (Tok_UN_Cnd_NOT (!ln) :: acc) xs
   | '+'::'+'::xs -> work (Tok_UN_INC_OP (!ln) :: acc) xs
   | '-'::'-'::xs -> work (Tok_UN_DEC_OP (!ln) :: acc) xs

   | '|'::xs -> work (Tok_BW_OR (!ln) :: acc) xs
   | '&'::xs -> work (Tok_BW_AND (!ln) :: acc) xs
   | '<'::'<'::xs -> work (Tok_BW_LS (!ln) :: acc) xs
   | '>'::'>'::xs -> work (Tok_BW_RS (!ln) :: acc) xs  

   | '<'::xs ->  work (Tok_LG_LT (!ln) :: acc) xs
   | '>'::xs ->  work (Tok_LG_GT (!ln) :: acc) xs

   | '='::xs -> work (Tok_ASS_EQ (!ln) :: acc) xs
   | '.'::xs -> work (Tok_ACC_DOT (!ln) :: acc) xs

   | '+'::xs -> work (Tok_BN_ADD (!ln) :: acc) xs
   | '-'::xs -> work (Tok_SUB (!ln) :: acc) xs
   | '*'::xs -> work (Tok_MUL (!ln) :: acc) xs
   | '/'::xs -> work (Tok_BN_DIV (!ln) :: acc) xs
   | '%'::xs -> work (Tok_BN_MOD (!ln) :: acc) xs

   | ','::xs -> work (Tok_SEP_Comma (!ln) :: acc) xs
   | ';'::xs -> work (Tok_SEP_Semi (!ln) :: acc) xs
   | '('::xs -> work (Tok_SEP_LParen (!ln) :: acc) xs
   | ')'::xs -> work (Tok_SEP_RParen (!ln) :: acc) xs
   | '{'::xs -> work (Tok_SEP_LCurly (!ln) :: acc) xs
   | '}'::xs -> work (Tok_SEP_RCurly (!ln) :: acc) xs
   | '['::xs -> work (Tok_SEP_LBox (!ln) :: acc) xs
   | ']'::xs -> work (Tok_SEP_RBox (!ln) :: acc) xs
     
    | '\n'::xs ->  (* Handle newline and increment line number *)
       ln := !ln + 1;
       work acc xs

    | ' '::xs | '\t'::xs ->  (* Skip spaces and tabs *)
       work acc xs

    | x::xs when is_letter x ->  (* Handle identifiers and keywords *)
       let (y, ys) = string_until is_digit_letter (x::xs) in
       (match y with
       | "if" -> work (Tok_if (!ln) :: acc) ys
       | "else" -> work (Tok_else (!ln) :: acc) ys
       | "struct" -> work (Tok_struct (!ln) :: acc) ys
       | "new" -> work (Tok_new (!ln) :: acc) ys
       | "for" -> work (Tok_for (!ln) :: acc) ys
       | "int" -> work (Tok_int (!ln) :: acc) ys
       | "char" -> work (Tok_char (!ln) :: acc) ys
       | "while" -> work (Tok_while (!ln) :: acc) ys
       | "return" -> work (Tok_return (!ln) :: acc) ys
       | "extern" -> work (Tok_extern (!ln) :: acc) ys
       | "void" -> work (Tok_void (!ln) :: acc) ys
       | "delete" -> work (Tok_delete (!ln) :: acc) ys
       | "break" -> work (Tok_break (!ln) :: acc) ys
       | x -> work (Tok_iden (x, !ln) :: acc) ys)

    | [] -> List.rev acc  (* End of input, return accumulated tokens *)

    | x::_ -> fail_handler ((sprintf "Toking error: unknown character '%c'." x), ln)
  in
  work [] lst

(* ---------------------------------------------------------------------Pretty Print Tokens ------------------------------------------------------------------------------------- *)

let pprint_token = function
  | Tok_break _ -> "break"
  | Tok_char _ -> "char"
  | Tok_extern _ -> "extern"
  | Tok_new _ -> "new"
  | Tok_for _ -> "for"
  | Tok_delete _ -> "delete"
  | Tok_if _ -> "if"
  | Tok_else _ -> "else"
  | Tok_int _ -> "int"
  | Tok_return _ -> "return"
  | Tok_struct _ -> "struct"
  | Tok_void _ -> "void"
  | Tok_while _ -> "while"
  | Tok_iden (s, _) -> sprintf "Tok_iden (%s)" s
  | Tok_int_const (x, _) -> sprintf "Tok_int_const(%d)" x
  | Tok_CC_char_const (c, _) -> sprintf "Tok_CC_char_const('%s')" c
  | Tok_Str_const (s, _) -> sprintf "Tok_Str_const(%s)" s
  | Tok_UN_BW_NOT _ -> "~"
  | Tok_UN_Cnd_NOT _ -> "!"
  | Tok_UN_DEC_OP _ -> "--"
  | Tok_UN_INC_OP _ -> "++"
  | Tok_BN_ADD _ -> "+"
  | Tok_SUB _ -> "-"
  | Tok_MUL _ -> "*"
  | Tok_BN_DIV _ -> "/"
  | Tok_BN_MOD _ -> "%"
  | Tok_LG_GT _ -> ">"
  | Tok_LG_LT _ -> "<"
  | Tok_LG_GTET _ -> ">="
  | Tok_LG_LTET _ -> "<="
  | Tok_LG_IS_ET _ -> "=="
  | Tok_LG_Not_ET _ -> "!="
  | Tok_LG_AND _ -> "&&"
  | Tok_LG_OR _ -> "||"
  | Tok_BW_AND _ -> "&"
  | Tok_BW_OR _ -> "|"
  | Tok_BW_LS _ -> "<<"
  | Tok_BW_RS _ -> ">>"
  | Tok_SEP_Comma _ -> ","
  | Tok_SEP_Semi _ -> ";"
  | Tok_SEP_LParen _ -> "("
  | Tok_SEP_RParen _ -> ")"
  | Tok_SEP_LCurly _ -> "{"
  | Tok_SEP_RCurly _ -> "}"
  | Tok_SEP_LBox _ -> "["
  | Tok_SEP_RBox _ -> "]"
  | Tok_ASS_EQ _ -> "="
  | Tok_ACC_DOT _ -> "."

(* Function to extract the line number from a token *)
let extract_line_number token =
   match token with
   | Tok_break ln -> ln
   | Tok_char  ln -> ln
   | Tok_extern ln -> ln
   | Tok_new ln -> ln
   | Tok_for ln -> ln
   | Tok_delete ln -> ln
   | Tok_if ln -> ln
   | Tok_else ln -> ln
   | Tok_int ln -> ln
   | Tok_return ln -> ln
   | Tok_struct ln -> ln
   | Tok_void ln -> ln
   | Tok_while ln -> ln

  (* Identifier *)
   | Tok_iden (_ , ln) -> ln

  (* Integer Constants *)
   | Tok_int_const (i, ln) -> ln

  (* Char Constants *)
   | Tok_CC_char_const (_,ln)-> ln

  (* String Constants *)
   | Tok_Str_const (_,ln) -> ln

  (* Operators *)
  (* Unary operators ~, !, --, ++ *)
   | Tok_UN_BW_NOT ln -> ln
   | Tok_UN_Cnd_NOT ln -> ln
  (* | Tok_UN_MINUS unary/binary will be decided by the parser *)
   | Tok_UN_DEC_OP ln -> ln
   | Tok_UN_INC_OP ln -> ln

  (* Binary +, -, *, /, % *)
   | Tok_BN_ADD ln -> ln
   | Tok_SUB ln -> ln
   | Tok_MUL ln -> ln (* PTR and MUL *)
   | Tok_BN_DIV ln -> ln
   | Tok_BN_MOD ln -> ln

  (* Logical >, <, >=, <=, ==, !=, &&, || *)
   | Tok_LG_GT ln -> ln
   | Tok_LG_LT ln -> ln
   | Tok_LG_GTET ln -> ln
   | Tok_LG_LTET ln -> ln
   | Tok_LG_IS_ET ln -> ln
   | Tok_LG_Not_ET ln -> ln
   | Tok_LG_AND ln -> ln
   | Tok_LG_OR ln -> ln

  (* Bitwise binary &, |, <<, >> *)
   | Tok_BW_AND ln -> ln
   | Tok_BW_OR ln -> ln
   | Tok_BW_LS ln -> ln
   | Tok_BW_RS ln -> ln

  (* Separators: Carriage return, space, and program tabs excluded -> , ; ( ) { } [ ] *)
   | Tok_SEP_Comma ln -> ln
   | Tok_SEP_Semi ln -> ln
   | Tok_SEP_LParen ln -> ln
   | Tok_SEP_RParen ln -> ln
   | Tok_SEP_LCurly ln -> ln
   | Tok_SEP_RCurly ln -> ln
   | Tok_SEP_LBox ln -> ln
   | Tok_SEP_RBox ln -> ln

  (* Assignment = *)
   | Tok_ASS_EQ ln -> ln

  (* Access using . *)
   | Tok_ACC_DOT ln -> ln

   