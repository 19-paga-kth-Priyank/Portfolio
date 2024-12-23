 open Printf
open Lexer
open Parser
open IR_generator
open IR1_generator_nl
open Ast
open Asm_generator


let var_reg_table = ref []
let n_for_var = ref 1

let pp_block_Iden_live = function
  | Some(Iden_name1 (s)) -> 
      let len = String.length s in
      if len >= 2 && String.get s 0 = '"' && String.get s (len - 1) = '"' then
        String.sub s 1 (len - 2)  (* Remove the quotes *)
      else
        s

(* Pretty-printer for var_reg_table *)
let pp_var_reg_table () =
  Printf.printf "Variable Register Table:\n";
  List.iter (fun (symbol, vreg_num) ->
    Printf.printf "  %s -> Vreg%s\n" (pp_ty_Iden1 symbol) (string_of_int vreg_num)
  ) !var_reg_table

  (* Helper: Determines if an operand is a TReg and assigns Vreg *)
let if_treg = function
  | Std_reg (_) -> false, None
  | Stack (_, _, _) -> false, None
  | Imm (_) -> false, None
  | Reg (_) -> false, None
  | TReg (_, sym) ->
      (* Check if symbol is already in var_reg_table *)
      let existing_entry = List.assoc_opt sym !var_reg_table in
      match existing_entry with
      | Some vreg -> true, Some (Iden_name1 ("Vreg" ^ string_of_int vreg))
      | None ->
          (* Assign a new virtual register and update the table *)
          let new_vreg = !n_for_var in
          var_reg_table := (sym, new_vreg) :: !var_reg_table;
          n_for_var := new_vreg + 1;
          true, Some (Iden_name1 ("Vreg" ^ string_of_int new_vreg))

let if_treg_replace = function
  | TReg (ty, sym) ->
      (* Check if symbol is already in var_reg_table *)
      let existing_entry = List.assoc_opt sym !var_reg_table in
      (match existing_entry with
       | Some vreg -> 
           true, Some (TReg (ty, Iden_name1 ("Vreg" ^ string_of_int vreg)))  (* Return existing Vreg *)
       | None ->
           (* Assign a new virtual register and update the table *)
           let new_vreg = !n_for_var in
           var_reg_table := (sym, new_vreg) :: !var_reg_table;
           n_for_var := new_vreg + 1;
           true, Some (TReg (ty, Iden_name1 ("Vreg" ^ string_of_int new_vreg))))  (* Return new Vreg *)
  | op -> false, None  (* For all other operand types, return false, None *)

          
          


(* replace the Tregs by Vreg *)
let rec replace_treg accum = function
  | [] -> List.rev accum

  | Block_id id :: rest ->
      replace_treg (Block_id id :: accum) rest

  | UnOp (uop, operand) :: rest ->
      let replaced_operand =
        match if_treg_replace operand with
        | true, Some op -> op
        | _ -> operand
      in
      replace_treg (UnOp (uop, replaced_operand) :: accum) rest

  | BinOp (bop, op1, op2) :: rest ->
      let op1' =
        match if_treg_replace op1 with
        | true, Some op -> op
        | _ -> op1
      in
      let op2' =
        match if_treg_replace op2 with
        | true, Some op -> op
        | _ -> op2
      in
      replace_treg (BinOp (bop, op1', op2') :: accum) rest

  | Call id :: rest ->
      replace_treg (Call id :: accum) rest

  | Cqo :: rest ->
      replace_treg (Cqo :: accum) rest

  | Blockend blockend :: rest ->
      replace_treg (Blockend blockend :: accum) rest


(* Compute def and use sets for a list of unspilled instructions *)


let rec make_inst_def_use_list bl_id inst accum = function


  | Block_id (id) :: rest -> 
    if List.exists (fun user_id -> user_id = id) !list_user_def then
    make_inst_def_use_list bl_id (inst +1) ((pp_block_Iden id, (string_of_int(inst+2)::[]) , [] , []) :: accum) rest
    else
      make_inst_def_use_list (((pp_block_Iden id),inst+1)::bl_id) (inst +1) accum rest
  | UnOp (uop , operand) ::rest -> 
    let b,sy = if_treg operand in
      if b = true then make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), (string_of_int(inst+2)::[]) ,[] , sy::[]) :: accum) rest
      else make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), (string_of_int(inst+2)::[]) ,[] , [])::accum) rest

    
  | BinOp (Mov, op1, op2) :: rest-> 
    let b1, sy1 = if_treg (op1) 
    in let b2 , sy2 = if_treg (op2) in 
      if b1 = true && b2 = true then
        make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), (string_of_int(inst+2)::[]) , sy1::[] , sy2::[])::accum) rest
      else if b1 = true && b2 = false then 
        make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), (string_of_int(inst+2)::[]) , sy1::[] , [])::accum) rest
      else if b1 = false && b2 = true then 
        make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), (string_of_int(inst+2)::[]) , [] , sy2::[])::accum) rest
      else
        make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), (string_of_int(inst+2)::[]) , [] , [])::accum) rest

    | BinOp (Movsx, op1, op2) :: rest-> 
      let b1, sy1 = if_treg (op1) 
      in let b2 , sy2 = if_treg (op2) in 
        if b1 = true && b2 = true then
          make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), (string_of_int(inst+2)::[]) , sy1::[] , sy2::[])::accum) rest
        else if b1 = true && b2 = false then
          make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), (string_of_int(inst+2)::[]) , sy1::[] , [])::accum) rest
        else if b1 = false && b2 = true then 
          make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), (string_of_int(inst+2)::[]) , [] , sy2::[])::accum) rest
        else
          make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), (string_of_int(inst+2)::[]) , [] , [])::accum) rest

  | BinOp (_ , op1 , op2) :: rest-> 
    let b1, sy1 = if_treg (op1) 
    in let b2 , sy2 = if_treg (op2) in 
      if b1 = true && b2 = true then
        make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), (string_of_int(inst+2)::[]) ,[] , sy2::sy1::[])::accum) rest
      else if b1 = true && b2 = false then
        make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), (string_of_int(inst+2)::[]) ,[] , sy1::[])::accum) rest
      else if b1 = false && b2 = true then 
        make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), (string_of_int(inst+2)::[]) ,[] , sy2::[])::accum) rest
      else
        make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), (string_of_int(inst+2)::[]) ,[] , [])::accum) rest

  | Call (id) :: rest -> make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), (string_of_int(inst+2)::[]) , [] , [])::accum) rest
  | Cqo :: rest -> make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), (string_of_int(inst+2)::[]) , [] , [])::accum) rest
  | Blockend(Ret) :: rest -> make_inst_def_use_list bl_id (inst+1) ((string_of_int(inst+1), [] , [] , [])::accum) rest
  | Blockend (Jmp (id)) :: rest ->
    make_inst_def_use_list bl_id (inst + 1)
      ((string_of_int (inst + 1), ((pp_block_Iden id)::[]), [], []) :: accum) rest

  | Blockend (JUnOp (jop, id1)) :: Blockend (Jmp (id2)) :: rest ->
      make_inst_def_use_list bl_id (inst + 1)
        ((string_of_int (inst + 1), ((pp_block_Iden id2)::(pp_block_Iden id1)::[]), [], []) :: accum) rest
    | [] -> bl_id , (List.rev accum)

  | _ -> failwith "I am lost"


  (* Function to replace successors with corresponding instruction numbers if they match a block_id in bl_id *)
    let succ_assign bl_id accum =
      List.map (fun (inst_no, succ, def, use) ->
        (* Update the successor list by checking matches in bl_id *)
        let updated_succ =
          List.map (fun succ_elem ->
            try
              (* Find matching block_id in bl_id *)
              let _, inst = List.find (fun (block_id, _) -> block_id = succ_elem) bl_id in
              string_of_int (inst + 1)  (* Replace with inst + 1 *)
            with Not_found -> succ_elem  (* Keep original if no match *)
          ) succ
        in
        (* Return the updated tuple with replaced successors *)
        (inst_no, updated_succ, def, use)
      ) accum

(* Liveness Analysis Function *)
let rec liveness_analysis succ_spilled =
  (* Helper to remove duplicates from a list *)
  let remove_duplicates lst =
    List.fold_left (fun acc x -> if List.mem x acc then acc else x :: acc) [] lst
  in

  (* Work function to compute live-out and live-in for an instruction *)
  let compute_live_in_out inst_no succ def use live_in_list live_out_list =
    (* Compute live-out: union of live-in of successors *)
    let live_out =
      List.fold_left (fun acc succ_inst ->
        match List.assoc_opt succ_inst live_in_list with
        | Some succ_live_in -> remove_duplicates (acc @ succ_live_in)
        | None -> acc
      ) [] succ
    in
    (* Compute live-in: use(inst) ∪ (live-out(inst) - def(inst)) *)
    let live_in =
      (List.fold_left (fun acc v -> if List.mem v def then acc else v :: acc)) use live_out
    in
    (live_in, live_out)
  in

  (* Iteratively update live-in and live-out sets *)
  let rec iterate live_in_list live_out_list =
    let updated_live_in_list, updated_live_out_list =
      List.fold_left (fun (in_acc, out_acc) (inst_no, succ, def, use) ->
        (* Fetch current live-in and live-out for the instruction *)
        let current_live_in = List.assoc_opt inst_no live_in_list |> Option.value ~default:[] in
        let current_live_out = List.assoc_opt inst_no live_out_list |> Option.value ~default:[] in

        (* Compute new live-in and live-out sets *)
        let new_live_in, new_live_out = compute_live_in_out inst_no succ def use live_in_list live_out_list in

        (* Update the live-in and live-out lists *)
        ((inst_no, new_live_in) :: in_acc, (inst_no, new_live_out) :: out_acc)
      ) ([], []) succ_spilled
    in
    (* Check for convergence *)
    if updated_live_in_list = live_in_list && updated_live_out_list = live_out_list then
      (updated_live_in_list, updated_live_out_list)
    else
      iterate updated_live_in_list updated_live_out_list
  in

  (* Initialize live-in and live-out as empty sets *)
  let initial_live_in = List.map (fun (inst_no, _, _, _) -> (inst_no, [])) succ_spilled in
  let initial_live_out = List.map (fun (inst_no, _, _, _) -> (inst_no, [])) succ_spilled in
  iterate initial_live_in initial_live_out


  (* Integrate liveness results into the instruction list *)
let integrate_liveness succ_spilled live_in live_out =
  List.map (fun (inst_no, succ, def, use) ->
    let live_in_set = List.assoc_opt inst_no live_in |> Option.value ~default:[] in
    let live_out_set = List.assoc_opt inst_no live_out |> Option.value ~default:[] in
    (inst_no, succ, def, use, live_in_set, live_out_set)
  ) succ_spilled

(* Pretty-print function for the extended liveness results *)
let pp_use_def_list use_def_list =
  let process_iden_list lst = List.map pp_block_Iden_live lst in
  List.iter
    (fun (inst_no, succ, def, use, live_in, live_out) ->
      (* Process def, use, live-in, and live-out lists *)
      let def_processed = process_iden_list def in
      let use_processed = process_iden_list use in
      let succ_processed = String.concat ", " succ in
      let live_in_processed = process_iden_list live_in in
      let live_out_processed = process_iden_list live_out in
      Printf.printf
        "Node( %s, succ = {%s}, def = {%s}, use = {%s}, live-in = {%s}, live-out = {%s})\n"
        inst_no
        succ_processed
        (String.concat ", " def_processed)
        (String.concat ", " use_processed)
        (String.concat ", " live_in_processed)
        (String.concat ", " live_out_processed)
    )
    use_def_list


(* Main function to control liveness analysis *)
let liveliness_control unspilled_inst =
  let blid_list, def_use_list = make_inst_def_use_list [] 0 [] unspilled_inst in
  let succ_spilled = succ_assign blid_list def_use_list in
  (* Perform liveness analysis *)
  let live_in, live_out = liveness_analysis succ_spilled in
  (* Integrate liveness results into the instruction list *)pp_var_reg_table();
  let final_result = integrate_liveness succ_spilled live_in live_out in
  (* Print the final result *)
  pp_use_def_list final_result
  

(* For interference graph *)
let liveliness_control_intf unspilled_inst =
  (* Generate block ID list and def-use list *)
  let blid_list, def_use_list = make_inst_def_use_list [] 0 [] unspilled_inst in
  
  (* Assign successors to instructions *)
  let succ_spilled = succ_assign blid_list def_use_list in
  
  (* Perform liveness analysis *)
  let live_in, live_out = liveness_analysis succ_spilled in
  
  (* Integrate liveness results into the instruction list *)
  let final_result = integrate_liveness succ_spilled live_in live_out in
  
  (* Return the final liveness result *)
  final_result
  
