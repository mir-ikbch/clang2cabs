open Util

type location = {
  file : string option;
  start_line : int option;
  end_line : int option;
  start_column : int option;
  end_column : int option
}

let empty_location = {
  file= None;
  start_line= None;
  end_line= None;
  start_column= None;
  end_column= None
}

type file = string * definition list

and type_specifier =
  | Tvoid
  | Tbool
  | Tchar_s
  | Tchar
  | Tuchar
  | Tshort
  | Tushort
  | Tint
  | Tuint
  | Tlong
  | Tulong
  | Tlonglong
  | Tulonglong
  | Tfloat
  | Tdouble

and specifier = type_specifier list

and decl_type =
  | JUSTBASE
  | PTR of decl_type
  | ARRAY of decl_type * expression

and init_name_group = specifier * init_name list

and name = string * decl_type

and init_name = name * init_expression

and single_name = specifier * name * location

and variable_scope = {
  is_global : bool;
  is_static : bool;
  is_static_local : bool
}

and definition =
  | FUNDEF of single_name * single_name list * block * location
  | DECDEF of init_name_group * variable_scope * location

and block = statement list

and statement =
  | NOP
  | COMPUTATION of expression
  | BLOCK of block * location
  | IF of expression * statement * statement * location
  | FOR of expression * expression * expression * statement * location
  | WHILE of expression * statement * location
  | RETURN of expression option * location
  | SWITCH of expression * statement * location
  | CASE of expression * statement * location
  | VARDECL of init_name_group * variable_scope * location
  | BREAK of location
  | CONTINUE of location
  | GOTO of string * location
  | LABEL of string * statement * location

and binary_operator =
  | ADD | SUB | MUL | DIV | MOD
  | AND | OR
  | EQ | NE | LT | GT | LE | GE
  | ASSIGN

and unary_operator =
  | MINUS | PLUS | NOT | BNOT | MEMOF | ADDROF
  | PREINCR | PREDECR | POSINCR | POSDECR

and expression =
  | UNARY of unary_operator * expression * location
  | BINARY of binary_operator * expression * expression * location
  | CALL of string * expression list * location
  | CONSTANT of constant * location
  | PAREN of expression * location
  | VARIABLE of string * location
  | INDEX of expression * expression * location

and constant =
  | CONST_INT of string (* the textual representation *)

and init_expression =
  | NO_INIT
  | SINGLE_INIT of expression

let rec show_file indent = function (filename, definition_list) ->
  let defs =
    definition_list
    |> List.map (show_definition ("  " ^ indent))
    |> String.concat "\n"
  in
  indent ^ "File(name: " ^ filename ^ "\n" ^
  defs ^ "\n" ^
  ")"
and show_name (name, decl_type) =
  name ^ (show_decl_type decl_type)
and show_variable_scope {is_global; is_static; is_static_local} =
  let info = [] in
  let info = if is_static_local then "static_local" :: info else info in
  let info = if is_static then "static" :: info else info in
  let info = if is_global then "global" :: info else info in
  String.concat " " info
and show_definition indent = function
  | FUNDEF ((return_type, func_name, _location1), single_name_list, block, _location2) ->
    let args =
      single_name_list
      |> List.map (fun (specifier, name, _location) -> show_name name ^ ":" ^ show_specifier specifier )
      |> String.concat ", "
    in
    indent ^ "Function(\n" ^
    indent ^ "  name: " ^ show_name func_name ^ "; return_type: " ^ show_specifier return_type ^ "\n" ^
    indent ^ "  arguments: " ^ args ^ "\n" ^
    (
      if List.is_empty block then
        ""
      else
        indent ^ "  {\n" ^
        show_block ("  " ^ indent) block ^ "\n" ^
        indent ^ "  }\n"
    ) ^
    indent ^ ")"
  | DECDEF (init_name_group, scope_info, _location) ->
    let init_name_group = show_init_name_group ("  " ^ indent) init_name_group in
    indent ^ "Decdef[" ^ show_variable_scope scope_info ^ "](\n" ^
    init_name_group ^ "\n" ^
    indent ^ ")"
and show_init_name_group indent (specifier, init_name_list) =
  let names =
    init_name_list
    |> List.map (fun init_name -> "  " ^ indent ^ show_init_name init_name)
    |> String.concat "\n"
  in
  indent ^ "names: \n" ^
  names ^ "\n" ^
  indent ^ "types: " ^ show_specifier specifier
and show_init_name ((name, decl_type), init_expr) =
  let name = show_decl_type decl_type ^ name in
  match init_expr with
  | NO_INIT ->
    name
  | SINGLE_INIT expr ->
    name ^ " = " ^ show_expression expr
and show_decl_type = function
  | JUSTBASE -> ""
  | PTR decl_type -> "*" ^ show_decl_type decl_type
  | ARRAY (decl_type, expr) -> show_decl_type decl_type ^ "[" ^ show_expression expr ^ "]"
and show_specifier specifier_list =
  String.concat ", " @@ List.map show_type_specifier specifier_list
and show_type_specifier = function
  | Tvoid -> "void"
  | Tbool -> "bool"
  | Tchar_s -> "char"
  | Tchar -> "signed char"
  | Tuchar -> "unsigned char"
  | Tshort -> "signed short"
  | Tushort -> "unsigned short"
  | Tint -> "signed int"
  | Tuint -> "unsigned int"
  | Tlong -> "signed long"
  | Tulong -> "unsigned long"
  | Tlonglong -> "signed long long"
  | Tulonglong -> "unsigned long long"
  | Tfloat -> "float"
  | Tdouble -> "double"
and show_block indent block =
  block
  |> List.map (show_statement indent)
  |> String.concat "\n"
and show_statement indent = function
  | NOP ->
    ""
  | COMPUTATION expr ->
    indent ^ show_expression expr
  | BLOCK (block, _location) ->
    indent ^ "{\n" ^
    show_block ("  " ^ indent) block ^ "\n" ^
    indent ^ "}"
  | IF (cond, if_true, if_false, _location) ->
    indent ^ "IF (" ^ show_expression cond ^ ") {\n" ^
    show_statement ("  " ^ indent) if_true ^ "\n" ^
    if if_false = NOP then
      indent ^ "}"
    else
      indent ^ "} else {\n" ^
      show_statement ("  " ^ indent) if_false ^ "\n" ^
      indent ^ "}"
  | FOR (init, cond, mut, stats, _location) ->
    indent ^ "FOR(\n" ^
    indent ^ "  " ^ show_expression init ^ "\n" ^
    indent ^ "  " ^ show_expression cond ^ "\n" ^
    indent ^ "  " ^ show_expression mut ^ "\n" ^
    indent ^ ") {\n" ^
    indent ^ show_statement ("  " ^ indent) stats ^ "\n" ^
    indent ^ "}"
  | WHILE (cond, stat, _location) ->
    indent ^ "WHILE (" ^ show_expression cond ^ ") {\n" ^
    show_statement ("  " ^ indent) stat ^ "\n" ^
    indent ^ "}"
  | RETURN (expr, _location) ->
    begin match expr with
    | Some expr -> indent ^ "RETURN " ^ show_expression expr
    | None -> indent ^ "RETURN"
    end
  | VARDECL (init_name_group, scope_info, _location) ->
    let init_name_group = show_init_name_group ("  " ^ indent) init_name_group in
    indent ^ "VARDECL[" ^ show_variable_scope scope_info ^ "](\n" ^
    init_name_group ^ "\n" ^
    indent ^ ")"
  | BREAK _ ->
    indent ^ "BREAK"
  | CONTINUE _ ->
    indent ^ "CONTINUE"
  | GOTO (label, _location) ->
    indent ^ "GOTO " ^ label
  | LABEL (label, stat, _location) ->
    indent ^ "LABEL " ^ label ^ ":\n" ^ show_statement indent stat
  | SWITCH (expr, stat, _location) ->
    indent ^ "SWITCH (" ^ show_expression expr ^ ") {\n" ^
    show_statement ("  " ^ indent) stat ^ "\n" ^
    indent ^ "}"
  | CASE (expr, stat, _location) ->
    indent ^ "CASE " ^ show_expression expr ^ ":\n" ^
    show_statement indent stat
and show_expression = function
  | UNARY (op, expr, _location) ->
    show_unary_operator (show_expression expr) op
  | BINARY (op, lhs, rhs, _location) ->
    show_expression lhs ^ " " ^ show_binary_operator op ^ " " ^ show_expression rhs
  | CALL (name, expr_list, _location) ->
    name ^ "(" ^ (expr_list |> List.map show_expression |> String.concat ", ") ^ ")"
  | CONSTANT (constant, _location) ->
    show_constant constant
  | PAREN (expr, _location) ->
    "(" ^ show_expression expr ^ ")"
  | VARIABLE (name, _location) ->
    name
  | INDEX (arr, idx, _location) ->
    show_expression arr ^ "[" ^ show_expression idx ^ "]"
and show_unary_operator v = function
  | MINUS -> "-" ^ v
  | PLUS -> "+" ^ v
  | NOT -> "!" ^ v
  | BNOT -> "^" ^ v
  | MEMOF -> "*" ^ v
  | ADDROF -> "&" ^ v
  | PREINCR -> "++" ^ v
  | PREDECR -> "--" ^ v
  | POSINCR -> v ^ "++"
  | POSDECR -> v ^ "--"
and show_binary_operator = function
  | ADD -> "+"
  | SUB -> "-"
  | MUL -> "*"
  | DIV -> "/"
  | MOD -> "%"
  | AND -> "&&"
  | OR -> "||"
  | EQ -> "=="
  | NE -> "!="
  | LT -> "<"
  | GT -> ">"
  | LE -> "<="
  | GE -> ">="
  | ASSIGN -> "="
and show_constant = function
  | CONST_INT i_as_str -> i_as_str

let show file = show_file "" file

let save_to_file = Util.save_to_file

let load_from_file = Util.load_from_file
