exception NameError of string * int
exception TypeError of string * int

open Printf
open Lexer
open Ast
open Parser

let fail_handler_name (msg, Iden_name (_, ln_no)) =
  raise (NameError (msg, ln_no + 1))

let fail_handler_type (msg, Iden_name (_, ln_no)) =
  raise (TypeError (msg, ln_no + 1))



type op_type = 
| GFnDecl of (ty_type * ty_Iden) list                        (* Global scope and list of parameters in order to check for the function signature *)
| GFnDef of (ty_type * ty_Iden) list                         (* Global scope and list of parameters in order to check for the function signature *)
| GVDecl
| GVDef
| Global_struct of (ty_type * ty_Iden) list

type var_sig = 
| Global of op_type * ty_type * ty_Iden                      (* handling of global scopes where struct will be identified as an identifier*)
| Local of var_sig * ty_type * ty_Iden                       (* handling of local variables where their global scope, idetifier and type are stored *)   


(* Function to compare two Iden_name values based on their string names *)
let name_cmp id1 id2 =
  match (id1, id2) with
  | Iden_name (name1, _), Iden_name (name2, _) -> name1 = name2

let rec check_type_exists ty accum =
  match ty with
  | TY_VOID | TY_INT | TY_CHAR -> true (* Predefined types are valid *)
  | TY_Iden id -> (* Check if `id` is a valid struct or global type *)
      List.exists (function
        | Global (Global_struct _, TY_Iden struct_id, _) when (name_cmp struct_id id) -> true
        | _ -> false
      ) accum
  | TY_PTR base_ty -> check_type_exists base_ty accum (* Recursively check pointer types *)


  let rec check_type_exists_gscope gscope ty accum =
    match ty with
    | TY_VOID | TY_INT | TY_CHAR -> true (* Predefined types are valid *)
    | TY_Iden id -> (* Check if `id` is a valid struct or global type *)
        List.exists (function
          | Global (Global_struct _, TY_Iden struct_id, _) when (name_cmp struct_id id) -> true
          | _ -> false
        ) accum
    | TY_PTR base_ty -> check_type_exists_gscope gscope base_ty accum (* Recursively check pointer types *)


  let rec check_type_exists_field (GStruct (id, fields)) field_ty accum =
    match field_ty with
    | TY_VOID | TY_INT | TY_CHAR -> true (* Predefined types are valid *)
  
    | TY_PTR base_ty ->
        (* Recursively check the base type of the pointer *)
        check_type_exists_field (GStruct (id, fields)) base_ty accum
  
    | TY_Iden struct_id ->
        (* Check if the identifier matches the current GStruct or a field within it, or is globally defined *)
        if name_cmp id struct_id (* Compare directly with the GStruct ID *)
            || List.exists (fun (field_ty, _) ->
                match field_ty with
                | TY_Iden existing_id -> name_cmp existing_id struct_id
                | _ -> false
              ) fields
            || List.exists (function
                | Global (Global_struct _, TY_Iden existing_id, _) when name_cmp existing_id struct_id -> true
                | _ -> false
              ) accum then
          true
        else
          fail_handler_type ("Undefined struct type in field", struct_id)

    

  let check_name_exists id accum =
    List.exists (function
      | Global (_, _, existing_id) when name_cmp existing_id id -> true
      | Local (_, _, existing_id) when name_cmp existing_id id -> true
      | _ -> false
    ) accum

    let check_name_exists_gscope gscope id accum =
      (* Check in function parameters if gscope is a GFnDef *)
         (* printf "\naccum_length = %d \n" (List.length accum); *)
      let in_function_params =
        match gscope with
        | Global (GFnDef (params), _, _) -> 
            List.exists (fun (_, arg_id) -> (name_cmp arg_id id)) params
        | _ -> false
      in
      (* Check in local and global variables *)
      let in_variables =
        List.exists (function
          | Global (_, _, existing_id) when (name_cmp existing_id id) -> true  (* Check global variables *) 
          | Local (gscope', _, existing_id) when gscope' = gscope && (name_cmp existing_id id) -> true
          | _ -> false
        ) accum
      in
      (* if in_function_params || in_variables then printf "found\n" else printf"not found\n"; *)
      (* Return true if the identifier is found in either place *)
      in_function_params || in_variables
  

    let rec extract_iden_name_from_type = function
    | TY_Iden id -> id
    | TY_PTR base_ty -> extract_iden_name_from_type base_ty
    | _ -> Iden_name ("unknown", -1)  (* Default if no identifier is found *)

let find_var_type id accum =
  List.find_map (function
    | Global (_, ty, existing_id) when (name_cmp existing_id id) -> Some ty
    | Local (_, ty, existing_id) when (name_cmp existing_id id) -> Some ty
    | _ -> None
  ) accum

let find_struct_fields id accum =
  match List.find_opt (function
    | Global (Global_struct fields, TY_Iden struct_id, _) when (name_cmp struct_id id) -> true
    | _ -> false
  ) accum with
  | Some (Global (Global_struct fields, _, _)) -> fields
  | _ -> fail_handler_type ("Struct not found", id)

let find_function_params id accum =
  match List.find_opt (function
    | Global (GFnDef params, _, existing_id) when (name_cmp existing_id id) -> true
    | Global (GFnDecl params, _, existing_id) when (name_cmp existing_id id) -> true
    | _ -> false
  ) accum with
  | Some (Global (GFnDef params, _, _)) -> params
  | Some (Global (GFnDecl params, _, _)) -> params
  | _ -> fail_handler_name ("Function not found", id)

let validate_argument_count id args expected_args =
  if List.length args <> List.length expected_args then
    fail_handler_type ("Function argument count mismatch", id)


(* Helper function to find variable type in the gscope and accum *)
let find_var_type_gscope gscope id accum =
  (* Check in function parameters if gscope is a GFnDef *)
  let in_function_params =
    match gscope with
    | Global (GFnDef (params), _, _) -> 
        List.find_map (fun (param_ty, param_id) -> if name_cmp param_id id then Some param_ty else None) params
    | _ -> None
  in
  (* Check in local and global variables *)
  let in_variables =
    List.find_map (function
      | Global (_, ty, existing_id) when name_cmp existing_id id -> Some ty  (* Check global variables *) 
      | Local (gscope', ty, existing_id) when gscope' = gscope && name_cmp existing_id id -> Some ty
      | _ -> None
    ) accum
  in
  match in_function_params, in_variables with
  | Some ty, _ -> Some ty
  | _, Some ty -> Some ty
  | _ -> None

(* Main function to detect pointers in expressions *)
let rec is_pointer_detect gscope accum = function
  | EInt(_) | EChar(_) | EString(_) -> false

  | EVar(id) -> 
      (match find_var_type_gscope gscope id accum with
      | Some (TY_PTR _) -> true
      | Some _ -> false
      | None -> fail_handler_type ("Undefined variable", id))

  | ECall(id, args) -> 
      (* Find function definition or declaration *)
      let matching_functions = 
        List.filter (function
          | Global (GFnDef _, _, fn_id) when name_cmp fn_id id -> true
          | Global (GFnDecl _, _, fn_id) when name_cmp fn_id id -> true
          | _ -> false
        ) accum
      in
      (match matching_functions with
      | [] -> fail_handler_type ("Undefined function", id)
      | Global (fn_type, _, _) :: _ -> 
          (match fn_type with
          | GFnDef _ | GFnDecl _ ->
              (* Check if the function's return type is a pointer *)
              (match find_var_type_gscope gscope id accum with
              | Some (TY_PTR _) -> true
              | Some _ -> false
              | None -> fail_handler_type ("Undefined function return type", id))
          | _ -> fail_handler_type ("Invalid function definition encountered", id))
      | _ -> fail_handler_type ("Invalid entity type encountered in function call", id))

  | EArrayAccess(id, _, _) -> 
      (* Array access always operates on pointers; validate the type *)
      (match find_var_type_gscope gscope id accum with
      | Some (TY_PTR _) -> false (* Valid case *)
      | Some _ -> fail_handler_type ("Array access requires a pointer type", id)
      | None -> fail_handler_type ("Undefined variable for array access", id))

  | Enew(ty, _) -> 
      (* Check if the new operation creates a pointer type *)
      (match ty with
      | TY_PTR _ -> true
      | _ -> false)

  | EBNOp(_, e1, e2,_)  -> 
      (* Recursively check for pointers in sub-expressions *)
      is_pointer_detect gscope accum e1 || is_pointer_detect gscope accum e2
  
  | EUNOp(_, e1,_) -> is_pointer_detect gscope accum e1

(* Validate list of arguments in a function call *)
and name_check_helper_expr gscope accum = function
  | [] -> false
  | x :: xs -> is_pointer_detect gscope accum x || name_check_helper_expr gscope accum xs

(* Main function to validate expressions and detect pointers *)
and name_check_expr gscope accum expr =
  if is_pointer_detect gscope accum expr then
    fail_handler_type ("Invalid pointer operation detected", Iden_name ("expression", -1))
  else
    accum


let rec name_check_expr gscope accum = function
  | EInt(_) -> accum 
    (* Ignore integer literals and continue parsing *)
  
  | EString(_) -> accum 
    (* Ignore string literals and continue parsing *)
  
  | EChar(_) -> accum 
    (* Ignore character literals and continue parsing *)

  | EVar(r) -> 
    (* printf "\naccum_length = %d \n" (List.length accum); *)
    (* Check if the variable is defined locally, globally, or in function arguments *)
    if (check_name_exists_gscope gscope r accum) then
      accum
    else
      fail_handler_type ("Unknown variable type or undefined argument", r);
  
  

  | EBNOp(op, e1, e2, ln_bnop) -> 
    (* Special case for `==` and `!=` *)
    (match op with
    | BNOP_LG_ET | BNOP_LG_NET  -> 

      let accum1 = name_check_expr gscope accum e1 in
        name_check_expr gscope accum1 e2
    | _ -> 
        (* Normal handling for other binary operations *)
        (* Ensure both operands are of pointer types *)
        let ty1 = is_pointer_detect gscope accum e1 in
        let ty2 = is_pointer_detect gscope accum e2 in
        if not (ty1 || ty2) then accum (* Valid case *)
        else fail_handler_type ("Only `==` or `!=` allowed for pointers", Iden_name ("binary_op", ln_bnop)))
        

  | EUNOp(_, e,ln_unop) -> 
    (* Traverse recursively to check the expression e *)
    let ty = is_pointer_detect gscope accum e in
        if not (ty) then accum (* Valid case *)
        else fail_handler_type ("Only `==` or `!=` allowed for pointers", Iden_name ("unary_op", ln_unop))
      
  | ECall(id, args) -> 
      (* Collect matching function definitions or declarations from the global scope *)
      let matching_functions = 
        List.filter (function
          | Global (GFnDef _, _, fn_id) when (name_cmp fn_id id) -> true
          | Global (GFnDecl _, _, fn_id) when (name_cmp fn_id id)-> true
          | _ -> false
        ) accum
      in
      (match matching_functions with
      | [] -> 
          (* Raise an error if no matching function is found *)
          fail_handler_type ("Undefined function", id)
      | Global (fn_type, _, _) :: _ -> 
          (match fn_type with
          | GFnDef params | GFnDecl params ->
              if List.length params <> List.length args then
                (* Raise an error if the argument count doesn't match *)
                fail_handler_type ("Argument mismatch in function call", id)
              else
                (* Validate the argument expressions *)
                accum
          | _ -> 
              (* Handle unexpected cases *)
              fail_handler_type ("Invalid function definition encountered", id))
      | _ -> 
          (* Handle cases where a non-global entity unexpectedly appears *)
          fail_handler_type ("Invalid entity type encountered in function call", id))

  | Enew(ty, e) -> 
    (* Check if the type is valid *)
    if not (check_type_exists_gscope gscope ty accum) then (
      (* Extract the identifier name from the type to pass to the error handler *)
      let id_name = extract_iden_name_from_type ty in
      fail_handler_type ("Invalid type in new expression", id_name)
    ) else
      (* If the type is valid, continue checking the expression *)
      name_check_expr gscope accum e
    
    | EArrayAccess(id, e1, op_id) ->
      (* Check if id is defined locally, in gscope arguments, or globally, and ensure it's a pointer *)
          (* Function to recursively resolve the base type and validate *)
          let rec resolve_and_validate_base_type ty =
            match ty with
            | TY_PTR inner_ty -> resolve_and_validate_base_type inner_ty (* Recurse into nested pointers *)
            | TY_Iden struct_id ->
                (* Check existence in global, local variables, and function arguments *)
                let exists_in_scope =
                  List.exists (function
                    | Global (Global_struct _, TY_Iden existing_id, _) when name_cmp existing_id struct_id -> true
                    | Local (_, TY_Iden existing_id, _) when name_cmp existing_id struct_id -> true
                    | _ -> false
                  ) accum
                in
                let exists_in_arguments =
                  match gscope with
                  | Global (GFnDef (params), _, _) ->
                      List.exists (fun (param_ty, _) ->
                        match param_ty with
                        | TY_Iden existing_id when name_cmp existing_id struct_id -> true
                        | _ -> false
                      ) params
                  | _ -> false
                in
                if exists_in_scope || exists_in_arguments then
                  TY_Iden struct_id (* Valid struct pointer base type *)
                else
                  fail_handler_type ("Undefined struct type in pointer field", struct_id)
            | TY_INT | TY_CHAR -> ty (* Valid base types *)
            | _ -> fail_handler_type ("Invalid base type for array access", id)
          in
      
          (* Check if the variable `id` is defined and retrieve its type *)
          let id_ty =
            match find_var_type_gscope gscope id accum with
            | Some ty -> ty
            | None -> fail_handler_type ("Undefined variable or not a pointer", id)
          in
      
          (* Ensure `id` is a pointer and resolve the base type *)
          let base_type = 
            match id_ty with
            | TY_PTR _ -> resolve_and_validate_base_type id_ty
            | _ -> fail_handler_type ("Variable is not a pointer for array access", id)
          in
      
          (* Handle the resolved base type *)
          (match base_type with
           | TY_Iden struct_id -> 
               (* Handle struct pointers *)
               (match op_id with
               | Some field_id ->
                   (* Find the struct fields and check if `field_id` exists *)
                   let struct_fields = find_struct_fields struct_id accum in
                   if not (List.exists (fun (_, field) -> name_cmp field field_id) struct_fields) then
                     fail_handler_type ("Field not found in struct for array access", field_id)
               | None -> fail_handler_type ("Missing field identifier for struct pointer array access", id))
      
           | TY_INT | TY_CHAR ->
               (* Handle array pointers (non-struct) *)
               (match op_id with
               | Some _ -> fail_handler_type ("Unexpected field identifier for non-struct pointer array access", id)
               | None -> ())
      
           | _ -> ());
      
          (* Validate the index and value expressions *)
          let _ = name_check_expr gscope accum e1 in
      
          accum
      
    
      

      

let rec name_check_stmt gscope accum = function
  (* Handle expression statements *)
  | SExpr (e) -> 
      (* This will generally be an `ECall`. In `ECall`, check if the function is defined as a global function.
         Validate the number of arguments sent matches the function definition.
         Raise type errors if the arguments do not match. *)
      name_check_expr gscope accum e

  (* Handle variable definitions *)
  | SVarDef (ty, id, e) -> 
    (* Check if the type is valid. If invalid, raise a type error. *)
    if not (check_type_exists_gscope gscope ty accum) then
      fail_handler_type ("Invalid type for variable definition", id);

    (* Check if the variable name is already defined in the global scope or in the current function's arguments. *)
    if check_name_exists_gscope gscope id accum then
      fail_handler_name ("Variable name already exists", id);

    (* Add the variable as a local to the accumulator. *)
    let updated_accum = Local (gscope, ty, id) :: accum in
    (* printf "\n%d\n" (List.length updated_accum);
    printf "Adding variable local:\n"; *)

    (* Validate the initializer expression. *)
    let _ = name_check_expr gscope updated_accum e in updated_accum
    

  (* Handle variable assignments *)
  | SVarAssign (id, e) -> 
      (* Check if the variable name is defined in the global scope or in the function's argument list.
         If it does not exist, raise a type error with the message "Undefined type for variable". *)
      if not (check_name_exists_gscope gscope id accum) then
        fail_handler_type ("Undefined variable in assignment", id);

      (* Validate the expression being assigned. *)
      let _ = name_check_expr gscope accum e in
      accum

  (* Handle array assignments *)
  | SArrayAssign (id, e1, op_id, e2) ->
    (* Function to recursively resolve the base type and validate *)
    let rec resolve_and_validate_base_type ty =
      match ty with
      | TY_PTR inner_ty -> resolve_and_validate_base_type inner_ty (* Recurse into nested pointers *)
      | TY_Iden struct_id ->
          (* Check existence in global, local variables, and function arguments *)
          let exists_in_scope =
            List.exists (function
              | Global (Global_struct _, TY_Iden existing_id, _) when name_cmp existing_id struct_id -> true
              | Local (_, TY_Iden existing_id, _) when name_cmp existing_id struct_id -> true
              | _ -> false
            ) accum
          in
          let exists_in_arguments =
            match gscope with
            | Global (GFnDef (params), _, _) ->
                List.exists (fun (param_ty, _) ->
                  match param_ty with
                  | TY_Iden existing_id when name_cmp existing_id struct_id -> true
                  | _ -> false
                ) params
            | _ -> false
          in
          if exists_in_scope || exists_in_arguments then
            TY_Iden struct_id (* Valid struct pointer base type *)
          else
            fail_handler_type ("Undefined struct type in pointer field", struct_id)
      | TY_INT | TY_CHAR -> ty (* Valid base types *)
      | _ -> fail_handler_type ("Invalid base type for array access", id)
    in

    (* Check if the variable `id` is defined and retrieve its type *)
    let id_ty =
      match find_var_type_gscope gscope id accum with
      | Some ty -> ty
      | None -> fail_handler_type ("Undefined variable or not a pointer", id)
    in

    (* Ensure `id` is a pointer and resolve the base type *)
    let base_type = 
      match id_ty with
      | TY_PTR _ -> resolve_and_validate_base_type id_ty
      | _ -> fail_handler_type ("Variable is not a pointer for array access", id)
    in

    (* Handle the resolved base type *)
    (match base_type with
     | TY_Iden struct_id -> 
         (* Handle struct pointers *)
         (match op_id with
         | Some field_id ->
             (* Find the struct fields and check if `field_id` exists *)
             let struct_fields = find_struct_fields struct_id accum in
             if not (List.exists (fun (_, field) -> name_cmp field field_id) struct_fields) then
               fail_handler_type ("Field not found in struct for array access", field_id)
         | None -> fail_handler_type ("Missing field identifier for struct pointer array access", id))

     | TY_INT | TY_CHAR ->
         (* Handle array pointers (non-struct) *)
         (match op_id with
         | Some _ -> fail_handler_type ("Unexpected field identifier for non-struct pointer array access", id)
         | None -> ())

     | _ -> ());

    (* Validate the index and value expressions *)
    let _ = name_check_expr gscope accum e1 in
    let _ = name_check_expr gscope accum e2 in

    accum


  (* Handle scoped statements *)
  | SScope (arg) -> 
      (* Continuously parse statements in the scope. *)
      name_check_stmt_help gscope accum arg

  (* Handle if statements *)
  | SIf (e, arg, op_arg) -> 
      (* Check the name and type of the condition expression. *)
      let test_expr_accum = name_check_expr gscope accum e in

      (* Check the statement types in the `then` block. *)
      let accum1 = name_check_stmt gscope test_expr_accum arg in

      (* Check the statement types in the `else` block, if present. *)
      (match op_arg with
       | Some stmt -> name_check_stmt gscope accum1 stmt
       | None -> accum)

  (* Handle while loops *)
  | SWhile (e, arg) -> 
      (* Check the name and type of the condition expression. *)
      let _ = name_check_expr gscope accum e in

      (* Check the statement types and names recursively in the loop body. *)
      name_check_stmt gscope accum arg

  (* Handle break statements *)
  | SBreak -> 
      (* Continue traversing, no checks needed for break. *)
      accum

  (* Handle return statements *)
  | SReturn (op_e,ln_return) -> 
    (* Check the return expression. *)
    let fn_ty =
      match gscope with
      | Global (GFnDef _, ty, _) -> ty  (* Extract the function return type from GFnDef. *)
      | _ -> fail_handler_type ("Invalid scope for return statement", Iden_name ("unknown", ln_return))
    in
    (match op_e with
     | Some _ ->
         (* If the function type is void, a return expression is not allowed. *)
         if fn_ty = TY_VOID then
           fail_handler_type ("Void function cannot return a value", Iden_name ("return statement", -1))
     | None ->
         (* If the function is non-void, a return value is required. *)
         if fn_ty <> TY_VOID then
           fail_handler_type ("Non-void function must return a value", Iden_name ("return statement", -1)));
    accum



  (* Handle delete statements *)
  | SDelete (id,_) -> 
      (* Check if the identifier exists in the global scope (GFnDef args) or local scope of the current function. *)
      if not (check_name_exists_gscope gscope id accum) then
        fail_handler_name ("Undefined variable for delete", id);
      accum

(* Helper function for handling scoped statements *)
and name_check_stmt_help gscope accum stmts =
  let rec aux gscope stmts return_value return_list current_accum =
    match stmts with
    | [] ->
        (* At the end of the list, validate return based on the function type. *)
        let fn_ty =
          match gscope with
          | Global (GFnDef _, ty, _) -> ty  (* Extract the function return type from GFnDef. *)
          | _ -> fail_handler_type ("Invalid scope for function type check", Iden_name ("unknown", -1))
        in
        (* Validate all return expressions in the list against the function type. *)
        List.iter (fun stmt ->
          match stmt with
          | SReturn (Some expr,ln_no) ->
              (match fn_ty with
              | TY_VOID -> fail_handler_type ("Invalid return type for void function", Iden_name ("return", ln_no))
              | _ -> ())
          | SReturn (None,ln_no) ->
              (match fn_ty with
              | TY_VOID -> ()
              | _ -> fail_handler_type ("Invalid return type for non-void function", Iden_name ("return", ln_no)))
          | _ -> ()) return_list;
        (None, return_list, current_accum)

    | stmt :: rest ->
        let (new_return_value, new_return_list, updated_accum) =
          match stmt with
          | SReturn (Some expr, ln_no) ->
              (* Check if return is valid for the function type. *)
              let _ = name_check_expr gscope current_accum expr in 
              let fn_ty = match gscope with
                | Global (GFnDef _, ty, _) -> ty
                | _ -> fail_handler_type ("Invalid scope for function type check", Iden_name ("unknown", ln_no))
              in
              if fn_ty = TY_VOID then
                fail_handler_type ("Invalid return type for void function", Iden_name ("return", -1));
              (Some expr, stmt :: return_list, name_check_stmt gscope current_accum stmt)

          | SReturn (None,ln_no) ->
              (* Check if the function type is void for return without expression. *)
              let fn_ty = match gscope with
                | Global (GFnDef _, ty, _) -> ty
                | _ -> fail_handler_type ("Invalid scope for function type check", Iden_name ("unknown", ln_no))
              in
              if fn_ty <> TY_VOID then
                fail_handler_type ("Invalid return type for non-void function", Iden_name ("return", ln_no));
              (None, stmt :: return_list, name_check_stmt gscope current_accum stmt)

          | SScope inner_stmts ->
              (* Handle nested scopes, potentially recursive. *)
              let (inner_return_value, inner_return_list, inner_accum) = aux gscope inner_stmts None [] current_accum in
              let final_return_value = if inner_return_value = None then return_value else inner_return_value in
              (final_return_value, inner_return_list @ return_list, inner_accum)

          | SWhile (expr, body_stmt) ->
              (* Ignore return statements within while loops. *)
              let _ = name_check_expr gscope current_accum expr in
              let (_, while_return_list, while_accum) =
                match body_stmt with
                | SScope body_stmts -> aux gscope body_stmts None [] current_accum
                | _ -> aux gscope [body_stmt] None [] current_accum
              in
              (return_value, return_list @ while_return_list, while_accum)

          | SIf (cnd, then_stmt, else_stmt_opt) ->
              (* Handle if statements. *)
                let _ = name_check_expr gscope current_accum cnd in
              let (then_return_value, then_return_list, then_accum) =
                match then_stmt with
                | SScope then_stmts -> aux gscope then_stmts None [] current_accum
                | _ -> aux gscope [then_stmt] None [] current_accum
              in
              (match else_stmt_opt with
              | Some else_stmt ->
                  let (else_return_value, else_return_list, else_accum) =
                    match else_stmt with
                    | SScope else_stmts -> aux gscope else_stmts None [] then_accum
                    | _ -> aux gscope [else_stmt] None [] then_accum
                  in
                  if then_return_value = None && else_return_value = None then
                    (None, return_list @ then_return_list @ else_return_list, else_accum)  (* No return in either branch, defer to parent scope. *)
                  else if then_return_value <> None && else_return_value <> None then
                    (then_return_value, return_list @ then_return_list @ else_return_list, else_accum)  (* Both branches have return, ensure consistency. *)
                  else
                    fail_handler_type ("Inconsistent return in if-else branches", Iden_name ("if-else", -1))
              | None ->
                  (* No else block, check return in parent scope. *)
                  if then_return_value = None then
                    (None, return_list @ then_return_list, then_accum)  (* Defer to parent scope if no return in then block. *)
                  else
                    (then_return_value, return_list @ then_return_list, then_accum))

          | _ ->
              (* Handle all other statements. *)
              (return_value, return_list, name_check_stmt gscope current_accum stmt)
        in
        aux gscope rest new_return_value new_return_list updated_accum
  in
  let (_, _, final_accum) = aux gscope stmts None [] accum in
  final_accum


  
  (* Process arguments of a function to validate their types and uniqueness *)
 (* Validate the types and uniqueness of function arguments *)
let rec name_check_arg_list accum args =
  let rec aux seen args =
    match args with
    | [] -> ()
    | (ty, id) :: rest ->
        (* Check if the type of the argument is valid in the global scope *)
        if not (check_type_exists ty accum) then
          fail_handler_type ("Invalid type in argument list", id);

        (* Check if the argument name is unique in the function scope *)
        if List.mem id seen then
          fail_handler_name ("Duplicate argument name in function declaration", id);

        (* Check if the argument name conflicts with global scope identifiers *)
        (* if check_name_exists id accum then
          fail_handler_name ("Argument name conflicts with global scope", id); *)

        (* Add the argument to the seen list and continue *)
        aux (id :: seen) rest
  in
  aux [] args

  let rec name_check_global accum = function
  | GFuncDef (ty, id, arg_list, body) ->
      (* Check if the return type of the function is valid *)
      if not (check_type_exists ty accum) then
        fail_handler_type ("Invalid return type for function", id);

      (* Check if the function name already exists in the global scope *)
      (match List.find_opt (function
        | Global (GFnDecl existing_args, existing_ty, existing_id) when name_cmp existing_id id -> true
        | Global (GFnDef _, _, existing_id) when name_cmp existing_id id -> true
        | _ -> false
      ) accum with
      | Some (Global (GFnDecl existing_args, existing_ty, _)) ->
          (* If the function is declared, check if the argument lists match *)
          if List.length existing_args <> List.length arg_list then
            fail_handler_name ("Function argument list mismatch with declaration", id);

          (* Traverse argument by argument and check type and name *)
          List.iter2 (fun (decl_ty, decl_id) (def_ty, def_id) ->
            if not (name_cmp decl_id def_id && decl_ty = def_ty) then
              fail_handler_type ("Function argument type or name mismatch", def_id)
          ) existing_args arg_list;

          (* Check if the return type matches *)
          if existing_ty <> ty then
            fail_handler_type ("Function return type mismatch with declaration", id)
      | Some (Global (GFnDef _, _, _)) ->
          (* If the function is already defined, raise an error *)
          fail_handler_name ("Function already defined", id)
      | Some _ ->
          fail_handler_type ("Conflicting definition for function", id)
      | None -> ());

      (* Validate the arguments of the function *)
      name_check_arg_list accum arg_list;

      (* Add the function definition to the global scope *)
      let new_accum = Global (GFnDef arg_list, ty, id) :: accum in

      (* Check the body of the function *)
      let _ = name_check_stmt (Global (GFnDef arg_list, ty, id)) new_accum body in
      new_accum


  
  | GFuncDecl (ty, id, arg_list) ->
      (* Check if the return type of the function is valid *)
      if not (check_type_exists ty accum) then
        fail_handler_type ("Invalid return type for function", id);
  
      (* Check if the function name already exists in the global scope *)
      if check_name_exists id accum then
        fail_handler_name ("Function name already exists", id);
  
      (* Validate the arguments of the function *)
      name_check_arg_list accum arg_list;
  
      (* Add the function declaration to the global scope *)
      Global (GFnDecl arg_list, ty, id) :: accum
  
  | GVarDef (ty, id, expr) ->
      if not (check_type_exists ty accum) then
        fail_handler_type ("Invalid type for variable", id);
      if check_name_exists id accum then
        fail_handler_name ("Variable name already exists", id);
      let _ = name_check_expr (Global (GVDef, ty, id)) accum expr in
      Global (GVDef, ty, id) :: accum
  
  | GVarDecl (ty, id) ->
      if not (check_type_exists ty accum) then
        fail_handler_type ("Invalid type for variable", id);
      if check_name_exists id accum then
        fail_handler_name ("Variable name already exists", id);
      Global (GVDecl, ty, id) :: accum
  
  | GStruct (id, fields) ->
      if check_name_exists id accum then
        fail_handler_name ("Struct name already exists", id);
      let seen_field_ids = ref [] in
      List.iter (fun (field_ty, field_id) ->
        if not (check_type_exists_field (GStruct(id, fields)) field_ty accum) then
          fail_handler_type ("Invalid type in struct field", field_id);
        if List.mem field_id !seen_field_ids then
          fail_handler_name ("Duplicate field name in struct", field_id);
        seen_field_ids := field_id :: !seen_field_ids
      ) fields;
      Global (Global_struct fields, TY_Iden id, id) :: accum


(* Entry point for program name checking *)
(* let name_check_prog = function
| Prog g -> 
    let accum = List.fold_left name_check_global [] g in
    let pretty_output = pretty_print_accum accum in
    Printf.printf "%s\n\n" pretty_output *)


    (* let rec pretty_print_accum accum =
      let string_of_op_type = function
        | GFnDecl params -> 
            let params_str = 
              List.map (fun (ty, id) -> string_of_ty_type ty ^ " " ^ string_of_iden id) params
              |> String.concat ", "
            in
            "GFnDecl(" ^ params_str ^ ")"
        | GFnDef params ->
            let params_str = 
              List.map (fun (ty, id) -> string_of_ty_type ty ^ " " ^ string_of_iden id) params
              |> String.concat ", "
            in
            "GFnDef(" ^ params_str ^ ")"
        | GVDecl -> "GVDecl"
        | GVDef -> "GVDef"
        | Global_struct fields ->
            let fields_str =
              List.map (fun (ty, id) -> string_of_ty_type ty ^ " " ^ string_of_iden id) fields
              |> String.concat ", "
            in
            "Global_struct(" ^ fields_str ^ ")"
      in
      let rec string_of_var_sig = function
        | Global (op_type, ty, id) ->
            "Global(" ^ string_of_op_type op_type ^ ", " ^ string_of_ty_type ty ^ ", " ^ string_of_iden id ^ ")"
        | Local (gscope, ty, id) ->
            "Local(" ^ string_of_var_sig gscope ^ ", " ^ string_of_ty_type ty ^ ", " ^ string_of_iden id ^ ")"
      in
      let entries = 
        List.map string_of_var_sig accum
        |> String.concat "\n"
      in
      "Accumulator Contents:\n" ^ entries
    
    (* Helper functions for converting `ty_type` and `ty_Iden` to strings *)
    and string_of_ty_type = function
      | TY_VOID -> "void"
      | TY_INT -> "int"
      | TY_CHAR -> "char"
      | TY_PTR base_ty -> "ptr(" ^ string_of_ty_type base_ty ^ ")"
      | TY_Iden id -> "struct " ^ string_of_iden id
    
    and string_of_iden = function
      | Iden_name (name, _) -> name *)
    

  let name_check_prog = function
  | Prog g -> List.fold_left name_check_global [] g
      (* let accum = List.fold_left name_check_global [] g in
      let pretty_output = pretty_print_accum accum in
      Printf.printf "%s\n\n" pretty_output *)
  
