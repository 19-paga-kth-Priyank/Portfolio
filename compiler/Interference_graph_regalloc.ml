open Printf
open Lexer
open Parser
open IR_generator
open IR1_generator_nl
open Ast
open Asm_generator
open Liveliness

(* Helper to update the graph with a new interference edge *)
let add_edge graph key value =
  let existing_edges = List.assoc_opt key graph |> Option.value ~default:[] in
  if List.mem value existing_edges then graph
  else (key, value :: existing_edges) :: List.remove_assoc key graph

(* Interference graph generator based on live-in and live-out lists *)
let interference_graph_generator live_in_out_list =
  let rec process_node graph = function
    | [] -> graph
    | (inst_no, _, def, _, _, live_out) :: rest ->
        (* Process each definition and update the graph *)
        let graph_with_defs =
          List.fold_left (fun acc def_var ->
            (* Add interference edges for the definition with all live_out variables *)
            let updated_graph =
              List.fold_left (fun g live_var ->
                if def_var <> live_var then
                  let g = add_edge g def_var live_var in
                  add_edge g live_var def_var
                else g
              ) acc live_out
            in
            updated_graph
          ) graph def
        in
        (* Proceed to the next node *)
        process_node graph_with_defs rest
  in
  (* Initialize graph as an empty list *)
  let empty_graph = [] in
  process_node empty_graph live_in_out_list
(*  *)

let reg_options = [
  (* Std_reg Rax;  *)
  Std_reg Rbx; 
  Std_reg Rcx; 
  (* Std_reg Rdx;  *)
  Std_reg Rdi; 
  Std_reg Rsi; 
  Std_reg Rbp; 
  Std_reg R8; 
  Std_reg R9;
  (* Std_reg R10; *)
  Std_reg R11 ; 
  Std_reg R12 ; 
  Std_reg R13 ; 
  Std_reg R14 ; 
  Std_reg R15
  ]


(* Pretty-printer for the interference graph *)
let pp_interference_graph graph =
  Printf.printf "Interference Graph:\n";
  List.iter (fun (var, edges) ->
    let processed_edges = List.map pp_block_Iden_live edges in
    Printf.printf "  %s -> {%s}\n" (pp_block_Iden_live var) (String.concat ", " processed_edges)
  ) graph



 (* Register allocator using graph coloring *)
(* Immutable list of registers *)

(* Register allocator using graph coloring *)
let rec color_graph graph =
  let spill_counter = ref 0 in  (* Counter for spill slots *)
  let allocation = ref [] in    (* To store (variable, allocation) *)

  (* Helper to check neighbors and find an available register *)
  let find_available_register var neighbors =
    let used_regs =
      List.filter_map (fun neighbor ->
        List.assoc_opt neighbor !allocation
      ) neighbors
    in
    List.find_opt (fun reg -> not (List.mem reg used_regs)) reg_options
  in

  (* Recursive function to process each node in the graph *)
  let rec process_nodes = function
    | [] -> ()  (* All nodes processed *)
    | (var, neighbors) :: rest ->
        match find_available_register var neighbors with
        | Some reg ->
            (* Assign register and add to allocation *)
            allocation := (var, reg) :: !allocation;
            process_nodes rest
        | None ->
            (* Spill the variable and assign a temporary register *)
            let temp_spill = TReg ((!spill_counter, QWord), Iden_name1("__tmp__"^ (string_of_int !spill_counter))) in
            spill_counter := !spill_counter + 1;
            allocation := (var, temp_spill) :: !allocation;
            process_nodes rest
  in

  process_nodes graph;
  !allocation


    let pp_register_allocation allocation =
      Printf.printf "Register and Spill Allocation:\n";
      List.iter (fun (var, alloc) ->
        match alloc with
        | Std_reg r -> Printf.printf "  %s -> Reg(%s)\n" (pp_block_Iden_live var) (pp_std_reg r)
        | TReg ((ref_num, size), name) -> 
            Printf.printf "  %s -> Spill(TReg(%s)\n" 
              (pp_block_Iden_live var) (pp_block_Iden name)
      ) allocation


  (* Replace Vreg_n with allocated registers or spills *)
let replace_vregs_with_alloc unspilled_insts allocation =
  (* Helper function to replace a TReg operand *)
  let replace_op = function
    | TReg (tuple, Iden_name1 vreg_name) ->
        (* Check if vreg_name exists in the allocation table *)
        (match List.assoc (Some(Iden_name1 vreg_name)) allocation with
         | Std_reg reg -> Std_reg reg   (* Replace with allocated register *)
         | TReg ((n, size), name) -> TReg ((n, size), name)  (* Replace with spill *)
         | _ -> TReg (tuple, Iden_name1 vreg_name))  (* Leave unchanged if no allocation found *)
    | other -> other  (* Leave other operands unchanged *)
  in

  (* Recursive function to process instructions *)
  let rec process_instructions = function
    | [] -> []  (* Base case: empty list *)
    | Block_id id :: rest -> Block_id id :: process_instructions rest
    | UnOp (uop, op) :: rest ->
        let updated_op = replace_op op in
        UnOp (uop, updated_op) :: process_instructions rest
    | BinOp (bop, op1, op2) :: rest ->
        let updated_op1 = replace_op op1 in
        let updated_op2 = replace_op op2 in
        BinOp (bop, updated_op1, updated_op2) :: process_instructions rest
    | Call id :: rest -> Call id :: process_instructions rest
    | Cqo :: rest -> Cqo :: process_instructions rest
    | Blockend blockend :: rest -> Blockend blockend :: process_instructions rest
  in
  process_instructions unspilled_insts
        