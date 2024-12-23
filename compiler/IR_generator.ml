open Printf
open Ast
open Lexer
open Parser
open IR1_generator_nl

type ir_stmt = 
  | IRSExpr of expr1
  | IRSVarAssign of ty_Iden1 * expr1
  | IRSVarDecl of ty_Iden1 * ty_type1

  type ir_blockend =
  | IRSReturn of expr1 option
  | IRSBranch of expr1 * ty_Iden1 * ty_Iden1
  | IRSJump of ty_Iden1

type ir_block = IRBlock of ty_Iden1 * (ir_stmt list) * ir_blockend

let no_of_if_while = ref 0

let pp_block_Iden = function
| Iden_name1 (s) -> 
    let len = String.length s in
    if len >= 2 && String.get s 0 = '"' && String.get s (len - 1) = '"' then
      String.sub s 1 (len - 2)  (* Remove the quotes *)
    else
      s

type param = ty_type1 * ty_Iden1 (* relates to calling convention thatt supports upto 6 paramerters *)

type ir_global = 
| IRFunc of ty_Iden1 * (ty_type1 * param list * ir_block list) (* It is a function definition *)
| IRFuncDecl of ty_Iden1 * ty_type1 * param list

  
let rec ir_block_gen curr_id next_id list_of_blocks accum_for_inst stmt_list =
  match stmt_list with
  | [] ->
      (* Finalize the current block *)
      let blockend =
        match next_id with
        | None -> IRSReturn None
        | Some next_block_id -> IRSJump next_block_id
      in
      IRBlock (curr_id, List.rev accum_for_inst, blockend) :: list_of_blocks

  | SExpr1 e :: rest ->
      (* Accumulate expressions and continue *)
      ir_block_gen curr_id next_id list_of_blocks (IRSExpr e :: accum_for_inst) rest

  | SVarDef1 (ty, id, e) :: rest ->
      (* Accumulate variable definitions and continue *)
      ir_block_gen curr_id next_id list_of_blocks
        (IRSVarAssign (id, e) :: IRSVarDecl (id, ty) :: accum_for_inst) rest

  | SVarAssign1 (id, e) :: rest ->
      (* Accumulate variable assignments and continue *)
      ir_block_gen curr_id next_id list_of_blocks
        (IRSVarAssign (id, e) :: accum_for_inst) rest

  | SReturn1 e_opt :: _ ->
      (* Terminate the current block with a return statement *)
      IRBlock (curr_id, List.rev accum_for_inst, IRSReturn e_opt) :: list_of_blocks

      | SIf1 (condn, then_stmt, else_stmt) :: rest ->
        (* Handle if-statement *)
        no_of_if_while := !no_of_if_while + 1;
        let make_var_str = string_of_int !no_of_if_while in
        let then_block_id = Iden_name1 ((pp_block_Iden curr_id) ^ "_if_true_" ^ make_var_str) in
        let else_block_id = Iden_name1 ((pp_block_Iden curr_id) ^ "_else_" ^ make_var_str) in
        let end_block_id = Iden_name1 ((pp_block_Iden curr_id) ^ "_after_if_else_" ^ make_var_str) in
    
        (* Determine the appropriate next ID for the branches *)
        let branch_block =
          match else_stmt with
          | Some _ ->
              (* Else block exists, so use else_block_id and end_block_id *)
              IRBlock (curr_id, List.rev accum_for_inst, IRSBranch (condn, then_block_id, else_block_id))
          | None ->
              (* No else block, so use end_block_id directly *)
              IRBlock (curr_id, List.rev accum_for_inst, IRSBranch (condn, then_block_id, end_block_id))
        in
    
        (* Process the "then" block *)
        let then_next_id = end_block_id in
        let then_blocks = ir_block_gen then_block_id (Some then_next_id) [] [] [then_stmt] in
    
        (* Process the "else" block, if it exists *)
        let else_blocks =
          match else_stmt with
          | Some else_stmt ->
              let else_next_id = end_block_id in
              ir_block_gen else_block_id (Some else_next_id) [] [] [else_stmt]
          | None -> []
        in
    
        (* Process the remaining statements *)
        let remaining_blocks = ir_block_gen end_block_id next_id list_of_blocks [] rest in
    
        branch_block :: then_blocks @ else_blocks @ remaining_blocks
    
      
  | SScope1 nested_stmts :: rest ->
      (* Continue processing the nested scope within the same block ID *)
      ir_block_gen curr_id next_id list_of_blocks accum_for_inst (nested_stmts @ rest)

  | SWhile1 (condn, stmt) :: rest ->
    no_of_if_while := !no_of_if_while + 1;
    let make_var_str = string_of_int !no_of_if_while in
    let loop_cond_block_id = Iden_name1 ((pp_block_Iden curr_id) ^ "_loop_cond_" ^ make_var_str) in
    let loop_body_block_id = Iden_name1 ((pp_block_Iden curr_id) ^ "_loop_body_" ^ make_var_str) in
    let out_of_loop_block_id = Iden_name1 ((pp_block_Iden curr_id) ^ "_out_of_loop_" ^ make_var_str) in

    (* Terminate the current block with a jump to the loop condition *)
    let jump_to_cond_block =
      IRBlock (curr_id, List.rev accum_for_inst, IRSJump loop_cond_block_id)
    in

    (* Process the loop condition block *)
    let loop_cond_block =
      IRBlock (loop_cond_block_id, [], IRSBranch (condn, loop_body_block_id, out_of_loop_block_id))
    in

    (* Process the loop body block *)
    let loop_body_blocks = ir_block_gen loop_body_block_id (Some loop_cond_block_id) [] [] [stmt] in

    (* Process the remaining statements after the loop *)
    let remaining_blocks = ir_block_gen out_of_loop_block_id next_id list_of_blocks [] rest in

    jump_to_cond_block :: loop_cond_block :: loop_body_blocks @ remaining_blocks 

  | _ -> failwith "Unexpected statement structure"

(* Generate IR for a global definition *)
let ir_gen_global g =
  match g with
  | GFuncDef1 (ty, id, arg_list, arg_stmt) -> 
      no_of_if_while := 0; (* Reset counter for each function *)
      let ir_params = List.map (fun (t, i) -> (t, i)) arg_list in
      let blocks = ir_block_gen id None [] [] [arg_stmt] in 
      IRFunc (id, (ty, ir_params, blocks))

  | GFuncDecl1 (ty, id, arg_list) -> 
      IRFuncDecl (id, ty, arg_list)

  | _ -> failwith "Only GFuncDef and GFuncDecl are supported for now"



(* Generate IR for a program *)
let ir_gen_prog = function
  | Prog1 g -> List.map ir_gen_global g






(*-------------------------------------------------------------------- Pretty print for ir_block ------------------------------------------------------*)

(* Pretty print for ir_stmt *)
let rec pp_ir_stmt = function
  | IRSExpr e -> Printf.sprintf "IRSExpr(%s)" (pp_expr1 e)
  | IRSVarAssign (id, e) -> Printf.sprintf "IRSVarAssign(%s, %s)" (pp_ty_Iden1 id) (pp_expr1 e)
  | IRSVarDecl (id, ty) -> Printf.sprintf "IRSVarDecl(%s, %s)" (pp_ty_Iden1 id) (pp_ty_type1 ty)

(* Pretty print for ir_blockend *)
and pp_ir_blockend = function
  | IRSReturn None -> "IRSReturn(None)"
  | IRSReturn (Some e) -> Printf.sprintf "IRSReturn(Some(%s))" (pp_expr1 e)
  | IRSBranch (cond, t_id, f_id) -> 
      Printf.sprintf "IRSBranch(%s, %s, %s)" (pp_expr1 cond) (pp_ty_Iden1 t_id) (pp_ty_Iden1 f_id)
  | IRSJump id -> Printf.sprintf "IRSJump(%s)" (pp_ty_Iden1 id)

and pp_ir_block (IRBlock (id, stmts, blockend)) =
  Printf.sprintf "IRBlock(%s, [\n  %s\n], %s)" 
    (pp_ty_Iden1 id)
    (String.concat "\n  " (List.map pp_ir_stmt stmts))
    (pp_ir_blockend blockend)

(* Pretty print for parameters *)
and pp_param (ty, id) =
  Printf.sprintf "(%s, %s)" (pp_ty_type1 ty) (pp_ty_Iden1 id)

(* Pretty print for ir_global *)
and pp_ir_global = function
  | IRFunc (id, (ret_ty, params, blocks)) ->
      Printf.sprintf "IRFunc(%s, %s, [%s])" 
        (pp_ty_Iden1 id)
        (pp_ty_type1 ret_ty)
        (String.concat "\n  " (List.map pp_ir_block blocks))

  | IRFuncDecl (id,ty,params)-> 
    Printf.sprintf "IRFuncDecl(%s, %s,(%s))" 
        (pp_ty_Iden1 id)
        (pp_ty_type1 ty)
        (String.concat "\n  " (List.map pp_param params))

(* Pretty print for an entire program *)
and pp_ir_prog ir_globals =
  String.concat "\n\n" (List.map pp_ir_global ir_globals)

(* Helper functions for identifiers, types, and expressions *)

  (* Add other type representations as needed *)

(* Usage example for a program *)
let print_ir_program prog =
  Printf.printf "%s\n" (pp_ir_prog prog)


