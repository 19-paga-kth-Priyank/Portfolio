open Printf
open Lexer
open Parser
open IR_generator
open IR1_generator_nl
open Ast
(* ----------------------------------------------------- Definitions --------------------------------------------------------*)

  type unop = Inc | Dec | Push | Pop | IMul | IDiv | Not | Neg | Setg | Setl | Setge | Setle | Sete | Setne

  type binop = Add | Sub | Cmp | Mov | And | Or | Xor | Movsx | Movzx

  type bitsize =
  | Byte | QWord

  let bitsize_value = function
  | Byte -> 1
  | QWord -> 8

  (* used for spiller function it helps create an anagram based on the size *)
  let bitsize_type = function
  | Byte -> TY_CHAR1
  | QWord -> TY_INT1

  type displacement = int
  type scale = int
  type reg = int * bitsize

  type jbinop = Je | Jc

  type blockend =
 | Ret
 | Jmp of ty_Iden1
 | JUnOp of jbinop * ty_Iden1 

type std_reg = 
| Rax | Rbx  | Rbp | R11 | R12 | R13 | R14 | R15| Rdi | Rsi | Rdx | R10 | Rsp |Al | Rcx | R8 | R9

  type op =
  | Imm of int
  | Reg of reg
  | TReg of reg * ty_Iden1
  | Mem of bitsize * reg * reg option * scale * displacement
  | Std_reg of std_reg
  | Stack of bitsize * std_reg * scale option
  | NoOp

  type inst =
  | Block_id of ty_Iden1
  | UnOp of unop * op
  | BinOp of binop * op * op
  | Call of ty_Iden1
  | Cqo
  | Blockend of blockend

 let ex_call_array = ref []
 let list_user_def = ref []

type envi =
  | Env of (ty_Iden1 * (int * ty_type1)) list

(* ------------------------------------------------------ Helper Funtions ------------------------------------------------------- *)




  let pp_block_Iden = function
  | Iden_name1 (s) -> 
      let len = String.length s in
      if len >= 2 && String.get s 0 = '"' && String.get s (len - 1) = '"' then
        String.sub s 1 (len - 2)  (* Remove the quotes *)
      else
        s
  
  let pp_ins_Iden = function
    | Iden_name1 (s) -> sprintf "%s" s

  let pp_unop = function
  | Inc -> "inc"
  | Dec -> "dec"
  | Push -> "push"
  | Pop -> "pop"
  | IMul -> "imul"
  | IDiv -> "idiv"
  | Not -> "not"
  | Neg -> "neg"
  | Setg -> "setg"
  | Setl -> "setl"
  | Setge -> "setge"
  | Setle -> "setle"
  | Sete -> "sete"
  | Setne -> "setne"

(* Pretty print binary operations *)
let pp_binop = function
  | Add -> "add"
  | Sub -> "sub"
  | Cmp -> "cmp"
  | Mov -> "mov"
  | Movsx -> "movsx"
  | Movzx -> "movzx"
  | And -> "and"
  | Or -> "or"
  | Xor -> "xor"

(* Pretty print jump binary operations *)
let pp_jbinop = function
  | Je -> "je"
  | Jc -> "jc"


(* Pretty print bitsizes *)
let pp_bitsize = function
  | Byte -> "byte"
  | QWord -> "qword"

(* Pretty print registers *)
let pp_reg (n, bitsize) =
  sprintf "r%d:%s" n (pp_bitsize bitsize)

(* Pretty print standard registers *)
let pp_std_reg = function
  | Rax -> "rax"
  | Rbx -> "rbx"
  | Rbp -> "rbp"
  | Rdi -> "rdi"
  | Rsi -> "rsi"
  | Rdx -> "rdx"
  | R11 -> "r11"
  | R12 -> "r12"
  | R13 -> "r13"
  | R14 -> "r14"
  | R15 -> "r15"
  | R10 -> "r10"
  | Rsp -> "rsp"
  | Rcx -> "rcx"
  | R8 -> "r8"
  | R9 -> "r9"
  | Al -> "al"

(* Pretty print operands *)
let pp_op = function
  | Imm(v) -> sprintf "%d" v
  | Reg(r) -> pp_reg r
  (* | TReg(r, sym) -> sprintf "treg(%s, %s)" (pp_reg r) (pp_ins_Iden sym) *)
  | TReg(r, sym) -> sprintf "%s" (pp_ins_Iden sym)

  | Mem(bitsize, base, opt_idx, scale, disp) ->
      let idx_str = match opt_idx with
        | None -> ""
        | Some idx -> sprintf " + %s*%d" (pp_reg idx) scale
      in
      sprintf "[%s%s + %d:%s]" (pp_reg base) idx_str disp (pp_bitsize bitsize)
  | Stack (sz, reg , off) -> 
    let idx_str = match off with
        | None -> ""
        | Some idx -> if idx <> 0  then sprintf " + %d" idx else ""
      in
      sprintf "%s[%s %s]" (pp_bitsize sz) (pp_std_reg reg) idx_str
  | Std_reg(r) -> pp_std_reg r
  | NoOp -> "no_op"

(* Pretty print block-end instructions *)
let pp_blockend = function
  | Ret -> "ret"
  | Jmp(id) -> sprintf "jmp %s " (pp_ins_Iden id)
  | JUnOp(jop, sym1) ->
      sprintf "%s %s" (pp_jbinop jop) (pp_ins_Iden sym1)

(* Pretty print instructions *)
let pp_inst = function
  | Block_id (id) -> sprintf "\n\t %s:\n" (pp_block_Iden id)
  | UnOp(op, operand) -> sprintf "%s %s" (pp_unop op) (pp_op operand)
  | BinOp(op, dest, src) -> sprintf "%s %s, %s" (pp_binop op) (pp_op dest) (pp_op src)
  | Call(id) -> sprintf "call $%s" (pp_ins_Iden id)
  | Cqo -> "cqo"
  | Blockend(be) -> pp_blockend be

(* Pretty print instruction lists *)
let pp_inst_list insts =
  String.concat "\n" (List.map pp_inst insts) 

let str2sym str = Iden_name1(str)

let tmp_reg n = TReg((n, QWord), str2sym ("tmp__"^(string_of_int n)))

let bitsize_of_type = function
| TY_INT1 -> QWord
| TY_CHAR1 -> QWord

  (* Pretty print a single environment entry *)
  let pp_env_entry (Iden_name1(name), (reg_num, ty)) =
    Printf.sprintf "%s -> (r%d, %s)" name reg_num (pp_ty_type1 ty)
  
  (* Pretty print the environment list *)
  let pp_environment env =
    let entries = List.map pp_env_entry env in
    Printf.sprintf "{ %s }" (String.concat "; " entries)
  

let make_reg l env =
  let (n, ty) = List.assoc l env in
  TReg((n, bitsize_of_type ty), l)

let print_global_block_env_list data =
  List.iter
    (fun (block_id,Env env) ->
      Printf.printf "Block ID: %s\n" (pp_block_Iden block_id);
      Printf.printf "Environment:\n%s\n" (pp_environment env)) data

  let analyze_global_block_env_list insts =
    (* Process instructions within a block to build its environment *)
    let rec process_child_function block_id acc_env = function
      | [] ->
          (* Finalize the environment for the current block *)
          [(block_id, Env (List.sort (fun (_, (n1, _)) (_, (n2, _)) -> compare n1 n2) acc_env))]
      | Block_id new_id :: rest ->
          (* Transition to parent when a new Block_id is found *)
          (* printf "Transitioning from child to parent. Found block: %s\n" (pp_block_Iden new_id); *)

      if List.exists (fun user_id -> user_id = new_id) !list_user_def then
          (block_id, Env (List.sort (fun (_, (n1, _)) (_, (n2, _)) -> compare n1 n2) acc_env))
          :: process_parent_function (Block_id new_id :: rest)
      else 
          process_child_function block_id acc_env rest

      | BinOp(_, TReg((n1, bitsize1), id1), TReg((n2, bitsize2), id2)) :: rest ->
          (* Handle BinOp with two registers *)
          let updated_env =
            let env_with_n1 =
              if List.exists (fun (_, (existing_n, _)) -> existing_n = n1) acc_env then
                acc_env
              else
                (id1, (n1, bitsize_type bitsize1)) :: acc_env
            in
            if List.exists (fun (_, (existing_n, _)) -> existing_n = n2) env_with_n1 then
              env_with_n1
            else
              (id2, (n2, bitsize_type bitsize2)) :: env_with_n1
          in
          process_child_function block_id updated_env rest
      | BinOp(_, TReg((n, bitsize), id), _) :: rest
      | BinOp(_, _, TReg((n, bitsize), id)) :: rest
      | UnOp(_, TReg((n, bitsize), id)) :: rest ->
          (* Handle single-register instructions *)
          let updated_env =
            if List.exists (fun (_, (existing_n, _)) -> existing_n = n) acc_env then
              acc_env
            else
              (id, (n, bitsize_type bitsize)) :: acc_env
          in
          process_child_function block_id updated_env rest
      | _ :: rest ->
          (* Skip other instructions *)
          process_child_function block_id acc_env rest
    
    (* Process the list of instructions to find block boundaries *)
    and process_parent_function = function
      | [] -> []
      | Block_id id :: rest ->
          (* Start processing a new block *)
          (* printf "Processing new block in parent: %s\n" (pp_block_Iden id); *)
          let env_for_block = process_child_function id [] rest in
          env_for_block @ process_child_function id [] rest
      | x :: rest ->
          (* Handle unexpected instructions *)
          (* printf "\nUnexpected instruction in parent: %s\n" (pp_inst x); *)
          failwith "Instructions must begin with Block_id"
    in
    process_parent_function insts
  
    let string_to_char s =
    if String.length s = 1 then
      String.get s 0
    else if String.length s = 2 && String.get s 0 = '\\' then
      match String.get s 1 with
      | 'n' -> '\n'
      | 't' -> '\t'
      | '\\' -> '\\'
      | 'r' -> '\r'
      | '"' -> '\"'
      | '\'' -> '\''
      | 'b' -> '\b'
      | _ -> failwith "Unsupported escape sequence"
    else
      failwith "Input must be a single character or a valid escape sequence"     
      
  let choose_op = function
  | BNOP_LG_ET -> Sete
  | BNOP_LG_GT -> Setg
  | BNOP_LG_LT -> Setl
  | BNOP_LG_GTET -> Setge
  | BNOP_LG_LTET -> Setle
  | BNOP_LG_NET -> Setne
    
  let rec pp_ty_type2 = function
  | TY_VOID1 -> "void "
  | TY_INT1 -> "int "
  | TY_CHAR1 -> "char " 
  | TY_Iden1 (str) -> pp_ty_Iden1 str
  | TY_PTR1 (y) -> pp_ty_type1 y  ^ "*" 

  let call_ext_fn_str (id, ty, params) =
    "extern " ^ pp_block_Iden id ^ "\n"
  
  let createextstr () =
    let remove_duplicates lst =
    List.fold_left (fun acc x -> if List.mem x acc then acc else x :: acc) [] lst in
    String.concat "" (List.map call_ext_fn_str (remove_duplicates !ex_call_array))
  
  

(* ------------------------------------------------------ ASM Funtions ------------------------------------------------------- *)


  let rec inst_select_ir_expr env n acc_text reg = function
  | EChar1 (c) -> BinOp(Mov, reg, Imm(Char.code (string_to_char c))) :: acc_text, n
  | EVar1(x) -> 
    BinOp(Mov, reg, (make_reg x env))::acc_text, n
  | EInt1(v) -> BinOp(Mov, reg, Imm(v)) :: acc_text, n
  | EBNOp1(BNOP_ADD, e1, e2) -> (* universal *)
      let (r1, r2) = (tmp_reg n, tmp_reg (n + 1)) in
      let n1 = n + 2 in
      let acc_text1, n2 = inst_select_ir_expr env n1 acc_text r1 e1 in
      let acc_text2, n3 = inst_select_ir_expr env n2 acc_text1 r2 e2 in
      let acc_text3 = BinOp(Add, reg, r2) :: BinOp(Mov, reg, r1) :: acc_text2 in
      acc_text3, n3

(* Subtraction *)



  | EBNOp1(BNOP_SUB, e1, e2) -> (* universal *)
      let (r1, r2) = (tmp_reg n, tmp_reg (n + 1)) in
      let n1 = n + 2 in
      let acc_text1, n2 = inst_select_ir_expr env n1 acc_text r1 e1 in
      let acc_text2, n3 = inst_select_ir_expr env n2 acc_text1 r2 e2 in
      let acc_text3 = BinOp(Sub, reg, r2) :: BinOp(Mov, reg, r1) :: acc_text2 in
      acc_text3, n3  

  (* Any other Mul *)
(* 
  | EBNOp1(BNOP_MUL, EInt1(x1), EInt1(x2)) -> (* universal *)
    BinOp(Mov , reg, Std_reg Rax) :: UnOp(IMul, reg) :: BinOp(Mov , reg, Imm(x2)) :: BinOp(Mov , (Std_reg Rax), Imm(x1)):: acc_text , n


  | EBNOp1(BNOP_MUL, EInt1(x1), (EVar1 x2)) -> 
    let acc_text1, n1 = inst_select_ir_expr env n acc_text reg (EVar1 x2) in
    BinOp(Mov , reg, Std_reg Rax) :: UnOp(IMul, Imm(x1)) :: BinOp(Mov , (Std_reg Rax), reg) :: acc_text1, n1


  | EBNOp1(BNOP_MUL, EVar1(x1), EVar1(x2)) -> (* universal *)
    let r1 = tmp_reg n in
    let acc_text1, n1 = inst_select_ir_expr env (n + 1) acc_text r1 (EVar1 x1) in
    let acc_text2, n2 = inst_select_ir_expr env n1 acc_text1 reg (EVar1 x2) in
    BinOp(Mov , reg, Std_reg Rax) :: UnOp(IMul, reg) :: BinOp(Mov , (Std_reg Rax), r1) :: acc_text2, n2 *)

  | EBNOp1(BNOP_MUL, e1, e2) -> (* universal *)
    let (r1, r2) = (tmp_reg n, tmp_reg (n + 1)) in
    let n1 = n + 2 in
    let acc_text1, n2 = inst_select_ir_expr env n1 acc_text r1 e1 in
    let acc_text2, n3 = inst_select_ir_expr env n2 acc_text1 r2 e2 in
    (* let acc_text3 = UnOp (Pop , (Std_reg Rax)):: BinOp(Mov , reg, Std_reg Rax) :: UnOp(IMul, r2) :: BinOp(Mov , (Std_reg Rax), r1):: UnOp (Push , (Std_reg Rax))::acc_text2 in *)
    let acc_text3 = BinOp(Mov , reg, Std_reg Rax) :: UnOp(IMul, r2) :: BinOp(Mov , (Std_reg Rax), r1) ::acc_text2 in
    
    acc_text3, n3  

  (* Any other Div *)
(*   
  | EBNOp1(BNOP_DIV, EInt1(x1), EInt1(x2)) -> (* universal *)
    BinOp(Mov , reg, Std_reg Rax) :: UnOp(IDiv, reg) :: Cqo :: BinOp(Mov , reg, Imm(x2)) :: BinOp(Mov , (Std_reg Rax), Imm(x1)):: acc_text , n

  | EBNOp1(BNOP_DIV, EInt1(x1), (EVar1 x2)) -> 
    let acc_text1, n1 = inst_select_ir_expr env n acc_text reg (EVar1 x2) in
    BinOp(Mov , reg, Std_reg Rax) :: UnOp(IDiv, reg) :: Cqo :: BinOp(Mov , (Std_reg Rax), Imm(x1)) :: acc_text1, n1


  | EBNOp1(BNOP_DIV, EVar1(x1), EVar1(x2)) -> (* universal *)
    let r1 = tmp_reg n in
    let acc_text1, n1 = inst_select_ir_expr env (n + 1) acc_text r1 (EVar1 x1) in
    let acc_text2, n2 = inst_select_ir_expr env n1 acc_text1 reg (EVar1 x2) in
    BinOp(Mov , reg, Std_reg Rax) :: UnOp(IDiv, reg) :: Cqo :: BinOp(Mov , (Std_reg Rax), r1) :: acc_text2, n2 *)

  | EBNOp1(BNOP_DIV, e1, e2) -> (* universal *)
      let (r1, r2) = (tmp_reg n, tmp_reg (n + 1)) in
      let n1 = n + 2 in
      let acc_text1, n2 = inst_select_ir_expr env n1 acc_text r1 e1 in
      let acc_text2, n3 = inst_select_ir_expr env n2 acc_text1 r2 e2 in
      (* let acc_text3 = UnOp (Pop , (Std_reg Rax)):: BinOp(Mov , reg, Std_reg Rax) :: UnOp(IDiv, r2) :: Cqo :: BinOp(Mov , (Std_reg Rax), r1):: UnOp (Push , (Std_reg Rax))::acc_text2 in *)
      let acc_text3 =  BinOp(Mov , reg, Std_reg Rax) :: UnOp(IDiv, r2) :: Cqo :: BinOp(Mov , (Std_reg Rax), r1):: acc_text2 in
      acc_text3, n3  

     (* Any other Div *)

  (* | EBNOp1(BNOP_MOD, EInt1(x1), EInt1(x2)) -> (* universal *)
  BinOp(Mov , reg, Std_reg Rdx) :: UnOp(IDiv, reg) :: Cqo :: BinOp(Mov , reg, Imm(x2)) :: BinOp(Mov , (Std_reg Rax), Imm(x1)):: acc_text , n


  | EBNOp1(BNOP_MOD, EInt1(x1), (EVar1 x2)) -> 
    let acc_text1, n1 = inst_select_ir_expr env n acc_text reg (EVar1 x2) in
    BinOp(Mov , reg, Std_reg Rdx) :: UnOp(IDiv, reg) :: Cqo :: BinOp(Mov , (Std_reg Rax), Imm(x1)) :: acc_text1, n1


  | EBNOp1(BNOP_MOD, EVar1(x1), EVar1(x2)) -> (* universal *)
    let r1 = tmp_reg n in
    let acc_text1, n1 = inst_select_ir_expr env (n + 1) acc_text r1 (EVar1 x1) in
    let acc_text2, n2 = inst_select_ir_expr env n1 acc_text1 reg (EVar1 x2) in
    BinOp(Mov , reg, Std_reg Rdx) :: UnOp(IDiv, reg) :: Cqo :: BinOp(Mov , (Std_reg Rax), r1) :: acc_text2, n2 *)

  | EBNOp1(BNOP_MOD, e1, e2) -> (* universal *)
    let (r1, r2) = (tmp_reg n, tmp_reg (n + 1)) in
    let n1 = n + 2 in
    let acc_text1, n2 = inst_select_ir_expr env n1 acc_text r1 e1 in
    let acc_text2, n3 = inst_select_ir_expr env n2 acc_text1 r2 e2 in
    (* let acc_text3 = UnOp (Pop , (Std_reg Rax)):: UnOp (Pop , (Std_reg Rdx)) :: BinOp(Mov , reg, Std_reg Rdx) :: UnOp(IDiv, r2) :: Cqo :: BinOp(Mov , (Std_reg Rax), r1):: UnOp (Push , (Std_reg Rdx)):: UnOp (Push , (Std_reg Rax)) :: acc_text2 in *)
    let acc_text3 = BinOp(Mov , reg, Std_reg Rdx) :: UnOp(IDiv, r2) :: Cqo :: BinOp(Mov , (Std_reg Rax), r1):: acc_text2 in
    acc_text3, n3  

(* compare ops *)

  | EBNOp1(op, EVar1(x1), EInt1(x2)) -> (* universal *)
  let r1 = tmp_reg n in
  let acc_text1, n1 = inst_select_ir_expr env (n + 1) acc_text r1 (EVar1 x1) in
    BinOp(Mov , reg, Std_reg Rax) :: BinOp(Movsx , (Std_reg Rax), (Std_reg Al)) :: UnOp((choose_op op), (Std_reg Al) ) :: BinOp(Cmp, r1 ,Imm(x2)) :: acc_text1, n1


  | EBNOp1(op, EInt1(x1), (EVar1 x2)) -> 
    let r1 = tmp_reg n in
  let acc_text1, n1 = inst_select_ir_expr env (n + 1) acc_text r1 (EVar1 x2) in
    BinOp(Mov , reg, Std_reg Rax) :: BinOp(Movsx , (Std_reg Rax), (Std_reg Al)) :: UnOp((choose_op op), (Std_reg Al) ) :: BinOp(Cmp, Imm(x1) ,r1):: acc_text1, n1

    
  | EBNOp1(op, e1, e2) -> (* universal *)
  let (r1, r2) = (tmp_reg n, tmp_reg (n + 1)) in
  let n1 = n + 2 in
  let acc_text1, n2 = inst_select_ir_expr env n1 acc_text r1 e1 in
  let acc_text2, n3 = inst_select_ir_expr env n2 acc_text1 r2 e2 in
  (* let acc_text3 = UnOp (Pop , (Std_reg Rax)):: UnOp (Pop , (Std_reg Rdx)) :: BinOp(Mov , reg, Std_reg Rdx) :: UnOp(IDiv, r2) :: Cqo :: BinOp(Mov , (Std_reg Rax), r1):: UnOp (Push , (Std_reg Rdx)):: UnOp (Push , (Std_reg Rax)) :: acc_text2 in *)
  let acc_text3 = BinOp(Mov , reg, Std_reg Rax) :: BinOp(Movsx , (Std_reg Rax), (Std_reg Al)) :: UnOp((choose_op op), (Std_reg Al) ) :: BinOp(Cmp, r1 ,r2) :: acc_text2 in
  acc_text3, n3

  | EUNOp1 (UNOP_MINUS , exp) -> 
    let r1 = tmp_reg n in
    let acc_text1 , n1 = inst_select_ir_expr env (n + 1) acc_text r1 exp in
    BinOp(Sub , reg , r1) :: BinOp(Mov , reg , Imm(0)) :: acc_text1 , n1
  
  | ECall1 (id, args) ->
    (* Check if the number of arguments exceeds the allowed limit *)
    let num_args = List.length args in
    (* let num_args = 3 in *)
    if num_args > 6 then
      failwith (Printf.sprintf "Function '%s' has more than 6 arguments, which is not supported." (pp_ty_Iden1 id));

    (* Define the argument registers in order *)

        (* let r1,r2,r3,r4,r5,r6,r7,r8 = (tmp_reg n , tmp_reg (n+1) , tmp_reg (n+2) , tmp_reg (n+3) , tmp_reg (n+4) , tmp_reg (n+5), tmp_reg (n+6) , tmp_reg (n+7)) in 
        *)let n=n+8 in 

        (* let r1,r2,r3,r4,r5,r6,r7,r8,r9,r10 = (tmp_reg n , tmp_reg (n+1) , tmp_reg (n+2) , tmp_reg (n+3) , tmp_reg (n+4) , tmp_reg (n+5), tmp_reg (n+6) , tmp_reg (n+7) , tmp_reg(n+8), tmp_reg(n+9)) in 
        let n=n+10 in *)

(* reserve and work with an stack adjustment where it can operate freely *)
        let push_list = UnOp(Push ,Std_reg Rdi) :: UnOp(Push , Std_reg Rsi) :: UnOp (Push , Std_reg Rdx) :: UnOp(Push , Std_reg Rcx) :: 
                        UnOp(Push , Std_reg R8) :: UnOp (Push , Std_reg R9) :: UnOp(Push, Std_reg R10) :: UnOp(Push, Std_reg R11) :: BinOp (Add,Std_reg Rsp ,Imm(64)):: [] in 


        let pop_list = BinOp (Sub,Std_reg Rsp ,Imm(64)):: UnOp(Pop ,Std_reg R11) :: UnOp(Pop , Std_reg R10) :: UnOp (Pop , Std_reg R9) :: UnOp(Pop , Std_reg R8) :: 
                        UnOp(Pop , Std_reg Rcx) :: UnOp (Pop , Std_reg Rdx) :: UnOp(Pop, Std_reg Rsi) :: UnOp(Pop, Std_reg Rdi) :: [] in 

      let acc_text = push_list @ acc_text in

    let arg_registers = [Std_reg Rdi; Std_reg Rsi; Std_reg Rdx; Std_reg Rcx; Std_reg R8; Std_reg R9] in

    (* Process each argument and assign it to the corresponding register *)
    let rec process_args acc_text idx = function
      | [] -> acc_text, n
      | arg :: rest ->
          let reg1 = List.nth arg_registers idx in
          let acc_text', n' = inst_select_ir_expr env n acc_text reg1 arg in
          process_args acc_text' (idx + 1) rest
    in
    let acc_text_with_args, n' = process_args acc_text 0 args 
  
  in

    (* Generate the call instruction and handle return type if necessary *)
    let acc_text_with_call = Call id  :: acc_text_with_args in
  

    (* If the function has a return type, pop the return value into `Rax` *)
    let acc_text_with_return =
      try
        let (_, func_ty, _) = List.find (fun (func_id, _, _) -> func_id = id) !ex_call_array in
        if func_ty <> TY_VOID1 then BinOp(Mov, reg , Std_reg Rax) :: acc_text_with_call
        else acc_text_with_call
      with
      | Not_found -> acc_text_with_call
    in
    let acc_text_with_return1 = pop_list @ acc_text_with_return in
    acc_text_with_return1, n'

(* Add ECall *)

  | _ -> failwith "TODO"


  let rec inst_select_ir_stmt env n acc_text = function

  | IRSVarDecl(x, ty)::xs ->
      let new_env = (x, (n, ty)) :: env in
      (* Debug print to inspect the environment *)
      (* Printf.printf "After declaring variable '%s': %s\n" (pp_ins_Iden x) (pp_environment new_env); *)
      inst_select_ir_stmt new_env (n + 1) acc_text xs

  | IRSVarAssign(x, expr)::xs ->
    (* Use the updated environment from previous steps *)
    let updated_env = env in
    if not (List.exists (fun (id, _) -> id = x) updated_env) then
      failwith (Printf.sprintf "Variable '%s' not declared in environment in assign: %s\n"
                  (pp_ins_Iden x) (pp_environment updated_env))
    else
      (* Debug print to verify the environment is correct *)
      (* Printf.printf "Assigning to variable '%s' in environment: %s\n"  *)
        (* (pp_ins_Iden x) (pp_environment updated_env); *)
      let acc_text1, n1 = inst_select_ir_expr updated_env n acc_text (make_reg x updated_env) expr in
      inst_select_ir_stmt updated_env n1 acc_text1 xs

      (* | IRSVarAssign(x, expr)::xs ->
    (* Use the updated environment from previous steps *)
    let updated_env = env in
    if not (List.exists (fun (id, _) -> id = x) updated_env) then
      failwith (Printf.sprintf "Variable '%s' not declared in environment in assign: %s\n"
                  (pp_ins_Iden x) (pp_environment updated_env))
    else
      (* Debug print to verify the environment is correct *)
      (* Printf.printf "Assigning to variable '%s' in environment: %s\n"  *)
        (* (pp_ins_Iden x) (pp_environment updated_env); *)
      let var_asssign_out = tmp_reg n in 
      let acc_text1, n1 = inst_select_ir_expr updated_env (n+1) acc_text var_asssign_out expr in
      inst_select_ir_stmt updated_env n1 (BinOp(Mov , (make_reg x updated_env) , var_asssign_out)::acc_text1) xs *)

  | IRSExpr (e) :: xs -> 
    let acc_text1, n1 =  inst_select_ir_expr env n acc_text (Std_reg Rax) e in
    inst_select_ir_stmt env n1 acc_text1 xs

  | [] -> env, n, acc_text


  let inst_select_ir_block env n acc_text = function
  | IRBlock(id, stmts, blockend_st) ->
      let acc_text = Block_id(id) :: acc_text in
      (* Process the list of statements within the block *)
      let env', n', acc_text' = inst_select_ir_stmt env n acc_text stmts in
      (* Handle the block-end instruction *)
      let acc_text'' = 
        match blockend_st with
        | IRSReturn(None) ->
            Blockend(Ret) :: acc_text'
        | IRSReturn(Some(expr)) ->
            let acc_text1, n2 = inst_select_ir_expr env' n' acc_text' (Std_reg Rax) expr in
            (* Ensure the result is stored in RAX before returning *)
            (match acc_text1 with
            | [] -> acc_text1
            | BinOp(_, src, _) :: _ when src <> Std_reg Rax ->
                BinOp(Mov, Std_reg Rax, src) :: Blockend(Ret) :: acc_text1
            | _ -> Blockend(Ret) :: acc_text1)
        | IRSBranch(condn, then_label, branch_label) ->
          let r_out = tmp_reg n' in
            let acc_condn, n_condn = inst_select_ir_expr env' (n'+1) acc_text' r_out  condn in
            (* Generate conditional branch instructions *)
             (* Blockend(JUnOp(Je, then_label)) ::  BinOp(Cmp, r_out, Imm(1)) :: acc_condn *)
            
             Blockend(Jmp(branch_label)) :: Blockend(JUnOp(Je, then_label)) ::  BinOp(Cmp, r_out, Imm(1))  ::acc_condn
        | IRSJump(id) ->
          Blockend(Jmp(id)) :: acc_text'
        | _ ->
            failwith "Unsupported block-end instruction"
      in
      env', n', acc_text''

  
  let rec inst_select_ir_global acc_text = function
    | IRFunc(id, (_, _, blocks)) ->
      (* Process all blocks of the function while threading env and n *)
      list_user_def := id :: !list_user_def;
      let rec process_blocks env n acc_text = function
        | [] -> acc_text (* When no more blocks, return the accumulated instructions *)
        | block :: rest ->
            (* Process the current block, thread updated env and n *)
            let env', n', acc_text' = inst_select_ir_block env n acc_text block in
            process_blocks env' n' acc_text' rest
      in
      process_blocks [] 0 acc_text blocks
    | IRFuncDecl(id, ty, params) ->
  
      ex_call_array := (id, ty, params) :: !ex_call_array;
      
      (* printf "\n %d %s ;new fn\n" (List.length !ex_call_array) (createextstr()); *)
      acc_text
      

  
  let inst_select_ir_program ir_global =
    (* printf "; Length of list: %d\n" (List.length ir_global); *)
    let rec process_globals acc_text = function
      | [] -> acc_text
      | global :: rest ->
          let acc_text' = inst_select_ir_global acc_text global in
          process_globals acc_text' rest
    in
    let text = process_globals [] ir_global in
    List.rev text
   
 
(* --------------------------------------------------------------------- Spiller functions V2 -------------------------------------------------------- *)

let global_block_env_list = ref []

let ins_spiller insts =
  (* Analyze the global environment list and update the reference *)
  global_block_env_list := analyze_global_block_env_list insts;

  (* Print the updated global block environment list *)
  (* print_global_block_env_list !global_block_env_list; *)

  let compute_max_offset block_id =
    try
      (* Retrieve the environment for the given block ID *)
      let Env env = List.assoc block_id !global_block_env_list in
      (* Compute the maximum offset based on the environment *)
      List.fold_left
        (fun acc (_, (_, ty)) -> acc + bitsize_value (bitsize_of_type ty))
        64
        env
    with Not_found ->
      failwith (Printf.sprintf "Block ID '%s' not found in environment list" (pp_block_Iden block_id))
  in

  let reg_to_mem block_id reg =
    try
      (* Retrieve the environment for the given block ID *)
      let Env env = List.assoc block_id !global_block_env_list in
      match reg with
      | TReg ((n, bitsize), id) ->
          let rec calculate_offset acc = function
            | [] ->
                failwith (Printf.sprintf "Register '%s' not found in environment for block '%s'"
                            (pp_ins_Iden id) (pp_block_Iden block_id))
            | (_, (idx, var_ty)) :: rest ->
              if idx = 0 then 
                if idx = n then 64 else calculate_offset 64 rest
                else
                  let new_acc = acc + bitsize_value (bitsize_of_type var_ty) in
                  if idx = n then new_acc else calculate_offset new_acc rest
          in
          let offset = calculate_offset 64 env in
          Stack (bitsize, Rsp, Some offset)
      | _ -> failwith "Unsupported register format for memory conversion"
    with Not_found ->
      failwith (Printf.sprintf "Block ID '%s' not found in environment list" (pp_block_Iden block_id)) in
  (* Other parts of the function can remain unchanged *)



  let spill_block insts =
    let rec process_block acc stack_adjustment current_block_id ref_id= function
      | [] -> List.rev acc
      | Block_id id:: rest ->

        if List.exists (fun user_id -> user_id = id) !list_user_def then  
          let max_offset = compute_max_offset id in
          let prologue = BinOp (Sub, Std_reg Rsp, Imm max_offset) in
          process_block ( prologue::(Block_id id) :: acc) max_offset id id rest
        else 
          process_block ((Block_id id) :: acc) stack_adjustment current_block_id ref_id rest

      | Blockend Ret :: rest ->
          let epilogue = BinOp (Add, Std_reg Rsp, Imm stack_adjustment) in
          process_block (Blockend Ret :: epilogue :: acc) stack_adjustment current_block_id ref_id rest

          (* ignore mov rax,rax *)
      | BinOp(Mov, Std_reg r1, Std_reg r2) :: rest ->
        if r1=r2 then
          process_block acc stack_adjustment current_block_id ref_id rest
        else
        let acc' =  BinOp(Mov, Std_reg r1, Std_reg r2) ::  acc in
        process_block acc' stack_adjustment current_block_id ref_id rest

      | BinOp(op, TReg(r1, r2), TReg(r3, r4)) :: rest ->
          let mem_r1 = reg_to_mem ref_id (TReg(r1, r2)) in
          let mem_r2 = reg_to_mem ref_id (TReg(r3, r4)) in
          if r1 = r3 && r2 = r4 then
            process_block acc stack_adjustment current_block_id ref_id rest
          else
          (let buffer = Std_reg R10 in
          let acc' =  BinOp(op , mem_r1 , buffer) :: BinOp(Mov, buffer , mem_r2) :: acc in
          process_block acc' stack_adjustment current_block_id ref_id rest)
      | BinOp(op, TReg(r1, r2), src) :: rest ->
          let mem_r1 = reg_to_mem ref_id (TReg(r1, r2)) in
          process_block (BinOp(op, mem_r1, src) :: acc) stack_adjustment current_block_id ref_id rest
      | BinOp(op, dest, TReg(r2, r3)) :: rest ->
          let mem_r2 = reg_to_mem ref_id (TReg(r2, r3)) in
          process_block (BinOp(op, dest, mem_r2) :: acc) stack_adjustment current_block_id ref_id rest
      | UnOp(op, TReg(r1, r2)) :: rest ->
          let mem_r1 = reg_to_mem ref_id (TReg(r1, r2)) in
          process_block (UnOp(op, mem_r1) :: acc) stack_adjustment current_block_id ref_id rest
          
      | inst :: rest ->
          process_block (inst :: acc) stack_adjustment current_block_id ref_id rest
    in
    process_block [] 0 (Iden_name1 "main") (Iden_name1 "main") insts
  in

  spill_block insts

(* ------------------------------------------------------------------Program Control--------------------------------------------------------- *)


(* Pretty print an unspilled program *)
let pp_ins_program_unspilled ir_prog =
  (* let text =  spill_instructions (inst_select_ir_program ir_prog) in *)
  let text1 = inst_select_ir_program ir_prog in
  (* let text_str = pp_inst_list text in *)
  let text_str_1 = pp_inst_list text1 in
  printf "\n %s \n\n\t\tglobal main \n\nSection .bss\n\nSection .text\n%s\n" (createextstr()) text_str_1
  (* printf "\tglobal main \n\nSection .bss\n\nSection .text\n%s\n" text_str  *)


    let pp_ins_program_unspilled_live ir_prog =
    (* let text =  spill_instructions (inst_select_ir_program ir_prog) in *)
    inst_select_ir_program ir_prog
    (* let text_str = pp_inst_list text in *)
    (* printf "\tglobal main \n\nSection .bss\n\nSection .text\n%s\n" text_str  *)

let pp_reg_alloc inst_list_op =
  (* let text1 = inst_select_ir_program ir_prog in *)
  let text_str = pp_inst_list (ins_spiller inst_list_op) in
  (* let text_str_1 = pp_inst_list text1 in *)
  (* printf "\n\n\n\n%s \tglobal main \n\nSection .bss\n\nSection .text\n%s\n" text_str_1 text_str *)
  printf "\n %s \n\n\t\tglobal main \n\nSection .bss\n\nSection .text\n%s\n" (createextstr()) text_str 

(* Pretty print an IR program *)
let pp_ins_program ir_prog =
  let text =  ins_spiller (inst_select_ir_program ir_prog) in
  (* let text1 = inst_select_ir_program ir_prog in *)
  let text_str = pp_inst_list text in
  (* let text_str_1 = pp_inst_list text1 in *)
  (* printf "\n\n\n\n%s \tglobal main \n\nSection .bss\n\nSection .text\n%s\n" text_str_1 text_str *)
  printf "\n %s \n\n\t\tglobal main \n\nSection .bss\n\nSection .text\n%s\n" (createextstr()) text_str 