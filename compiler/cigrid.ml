open Printf
open Ast
open Lexer
open Parser
open Sys
open Name_check
open IR_generator
open IR1_generator_nl
open Asm_generator
open Liveliness
open Interference_graph_regalloc

(* Reads from channel into a list of characters *)
let read_channel_to_list channel =
  let len = in_channel_length channel in
  let data = really_input_string channel len in
  List.init len (String.get data)

(* Function to print usage instructions *)
let print_usage () =
  print_endline "Usage: cigrid [--pretty-print] [--line-error] [--name-analysis] [--type-check] [--asm] [--ir-gen] [--unspilled] [--compile] [--liveness] [--interference] [--regalloc] <filename>"

(* Helper function to check if a flag is valid *)
let is_valid_flag flag = List.mem flag ["--pretty-print"; "--line-error"; "--name-analysis"; "--type-check"; "--asm"; "--ir-gen" ; "--unspilled" ; "--compile" ; "--liveness"; "--interference" ; "--regalloc"]

let execute_linux_commands asm_file =
  let commands = [
    Printf.sprintf "nasm -felf64 %s" asm_file;
    "gcc -no-pie a.o -o a.out";
    "./a.out > result.txt";
    "echo $?";
    "rm a.o a.out"
  ] in
  List.iter (fun cmd ->
    let result = Sys.command cmd in
    if result <> 0 then (
      Printf.eprintf "Error: Command failed: %s\n" cmd;
      exit 1
    )
  ) commands;
  (* Read and print the program's exit code *)
  let in_channel = open_in "return_code" in
  let return_code = input_line in_channel in
  close_in in_channel;
  Printf.printf "Program returned: %s\n" return_code;
  Sys.remove "return_code";
  (* Read and print the program's output *)
  let result_channel = open_in "result.txt" in
  let program_output = really_input_string result_channel (in_channel_length result_channel) in
  close_in result_channel;
  Printf.printf "Program output:\n%s\n" program_output;
  Sys.remove "result.txt"

let () =
  (* Extract arguments as a list *)
  let args = Array.to_list Sys.argv in

  (* Ensure at least one argument is provided *)
  if List.length args < 2 then (
    print_usage ();
    exit 0
  ) else
    (* Separate flags and filenames *)
    let flags = List.filter (fun arg -> String.starts_with ~prefix:"--" arg) args in
    let filenames = List.filter (fun arg -> not (String.starts_with ~prefix:"--" arg)) args in

    (* Check for unknown flags *)
    let unknown_flags = List.filter (fun flag -> not (is_valid_flag flag)) flags in

    (* Ensure a filename is provided *)
    if List.length filenames < 2 then (
      print_usage ();
      exit 0
    ) else
      let filename = List.nth filenames 1 in

      (* Check if the file exists *)
      if not (Sys.file_exists filename) then (
        Printf.eprintf "Error: File %s does not exist.\n" filename;
        exit 0
      ) else (
        (* Warn about unknown flags but continue execution *)
        if unknown_flags <> [] then (
          print_usage();
          exit 1
        );

        try
          (* Read the file contents *)
          let lst = read_channel_to_list (open_in filename) in

          (* Handle empty files gracefully *)
          if lst = [] then (
            Printf.printf "The file %s is empty.\n" filename;
            exit 0
          );

          (* Parse the file *)
          let ast = lst |> lexing |> parse_program in

          (* Check for valid flags and execute the corresponding behavior *)
          let pretty_print_flag = List.mem "--pretty-print" flags in
          let line_error_flag = List.mem "--line-error" flags in
          let name_flag = List.mem "--name-analysis" flags in
          let type_flag = List.mem "--type-check" flags in
          let asm_flag = List.mem "--asm" flags in
          let ir_gen_flag = List.mem "--ir-gen" flags in
          let unspilled_flag = List.mem "--unspilled" flags in
          let compile_flag = List.mem "--compile" flags in
          let liveliness_flag = List.mem "--liveness" flags in
          let interference_flag = List.mem "--interference" flags in
          let re_alloc_flag = List.mem "--regalloc" flags in


          if pretty_print_flag then (
            pp_prog ast |> Printf.printf "%s\n";
            if line_error_flag then Printf.eprintf "Line Error: Parsed successfully.\n";
            exit 0
          );

          if line_error_flag then (
            ast |> name_check_prog;
            Printf.eprintf "Line Error: Parsed successfully.\n";
            exit 0
          );

          if name_flag then (
            ast |> name_check_prog;
            Printf.printf "No Name Check Error\n";
            exit 0
          );

          if type_flag then (
            ast |> name_check_prog;
            Printf.printf "No Type Check Error\n";
            exit 0    
          );

          if asm_flag then (
            ast |> name_check_prog;
            ast |> simplify_program |> ir_gen_prog |> pp_ins_program;
            exit 0
          );

          if ir_gen_flag then (
            ast |> simplify_program |> ir_gen_prog |> pp_ir_prog |> printf "%s";
            exit 0
          );

          if unspilled_flag then (
            ast |> simplify_program |> ir_gen_prog |> pp_ins_program_unspilled;
            exit 0
          );

          if compile_flag then (
            let asm_file = "a.asm" in
            execute_linux_commands asm_file;
            exit 0
          );

          if liveliness_flag then (
            ast |> name_check_prog;
            ast |> simplify_program |> ir_gen_prog |>  pp_ins_program_unspilled_live |> liveliness_control;
            exit 0
          );

          if interference_flag then (
            ast |> name_check_prog;
            ast |> simplify_program |> ir_gen_prog |>  pp_ins_program_unspilled_live |> liveliness_control_intf |> interference_graph_generator |> pp_interference_graph;
            exit 0
          );
          if re_alloc_flag then (
            ast |> name_check_prog;
            let live_in_out_list =
              ast
              |> simplify_program
              |> ir_gen_prog
              |> pp_ins_program_unspilled_live
              |> liveliness_control_intf
              |> interference_graph_generator
              |> color_graph 

            in 
            (* pp_register_allocation live_in_out_list; *)
           
            let unspilled_list =
              ast
              |> simplify_program
              |> ir_gen_prog
              |> inst_select_ir_program
              |> (fun insts -> replace_treg [] insts)  (* Fix: provide [] as the accumulator *)
            in
            let optimized = replace_vregs_with_alloc unspilled_list live_in_out_list in
            pp_reg_alloc optimized;
            exit 0
          );
          

          (* Default behavior if no valid flags are passed *)
          Printf.printf "%s\n" (pp_prog ast);
          exit 0
        with
        | TypeError (msg, ln_no) ->
            Printf.printf "Type Error: %s\n" msg;  
            Printf.eprintf "%d\n" ln_no;
            exit 2

        | NameError (msg, ln_no) ->
            Printf.printf "Name Error: %s\n" msg;  
            Printf.eprintf "%d\n" ln_no;
            exit 2

        | ParseError (msg, ln_no) ->
            Printf.printf "Parse Error: %s\n" msg;  
            Printf.eprintf "%d\n" ln_no;
            exit 1

        | LexError (msg, tokens) ->
            Printf.printf "Lexical Error: %s\n" msg;
            Printf.eprintf "%d\n" tokens;
            exit 1
      )
