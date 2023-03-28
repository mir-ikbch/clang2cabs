open Util

exception Invalid_Yojson of string * Yojson.Safe.t

type [@warning "-37"] c_type =
  | Just of Cabs.typeSpecifier
  | Pointer of int
  | Array of { ptr: int; size: int }

module PointerMap = Map.Make(Int)

let find_type typemap i =
  let rec impl p =
    match PointerMap.find_opt p typemap with
    | Some (Just tpe) -> Some (tpe, Cabs.JUSTBASE)
    | Some (Pointer ptr) ->
      begin match impl ptr with
      | Some (tpe, decl_type) ->
        Some (tpe, Cabs.PTR ([], decl_type))
      | None -> None
      end
    | Some (Array { ptr; size }) ->
      begin match impl ptr with
      | Some (tpe, decl_type) ->
        let expr = Cabs.CONSTANT (Cabs.CONST_INT (string_of_int size)) in
        Some (tpe, Cabs.ARRAY (decl_type, [], expr))
      | None -> None
      end
    | None -> None
  in
  impl i

let make_typemap typedata = List.fold_left (fun map -> function
  | `Variant (
    "BuiltinType", Some (`Tuple (
      `Assoc [("pointer", `Int i)] ::
      `Variant ((
        "Bool" |
        "Char_S" | "SChar" | "UChar" |
        "Short" | "UShort" |
        "Int" | "UInt" |
        "Long" | "ULong" | 
        "LongLong" | "ULongLong" |
        "Float" |
        "Double"
      ) as tpe, None) ::
      _
    ))
  ) as yojson ->
    let tpe = match tpe with
    | "Int" -> Cabs.Tint
	(*
    | "Bool"  -> Ast.Tbool
    | "Char_S" -> Ast.Tchar_s
    | "SChar" -> Ast.Tchar
    | "UChar" -> Ast.Tuchar
    | "Short" -> Ast.Tshort
    | "UShort" -> Ast.Tushort
    | "UInt" -> Ast.Tuint
    | "Long" -> Ast.Tlong
    | "ULong" -> Ast.Tulong
    | "LongLong" -> Ast.Tlonglong
    | "ULongLong" -> Ast.Tulonglong
    | "Float" -> Ast.Tfloat
    | "Double" -> Ast.Tdouble
	*)
    | _ -> raise (Invalid_Yojson ("Invalid buildin type.", yojson))
    in
    PointerMap.add i (Just tpe) map
  | `Variant (
    "BuiltinType", Some (`Tuple (
      `Assoc [("pointer", `Int i)] ::
      `Variant ("Void", None) ::
      _
    ))
  ) ->
    PointerMap.add i (Just Cabs.Tvoid) map
(*
  | `Variant (
    "PointerType", Some (`Tuple (
      `Assoc [("pointer", `Int i)] ::
      `Assoc [("type_ptr", `Int p)] ::
      _
    ))
  ) ->
    PointerMap.add i (Pointer p) map 
  | `Variant (
    "ConstantArrayType", Some (`Tuple (
      `Assoc [("pointer", `Int i)] ::
      `Assoc [
        ("element_type", `Assoc [("type_ptr", `Int p)]);
        _stride
      ] ::
      (`Int size) ::
      _
    ))
  ) ->
    PointerMap.add i (Array { ptr= p; size }) map
	*)
  | _ ->
    map
  )
  PointerMap.empty
  typedata

(*
let show_c_type = function
  | Just tpe -> Ast.show_type_specifier tpe
  | Pointer p -> "Pointer->" ^ string_of_int p
  | Array { ptr; size } -> "Array[" ^ string_of_int size ^ "]->" ^ string_of_int ptr

let show_typemap typemap =
  typemap |> PointerMap.iter (fun idx tpe ->
    Printf.printf "%d => %s\n" idx (show_c_type tpe)
  )
*)
type function_typeinfo = {
  return_type: c_type;
  param_types: c_type list
}

let parse_params_type typemap params_type yojson =
  match List.assoc_opt "params_type" params_type with
  | Some `List param_types ->
    param_types
    |> List.map (
      function
      | `Assoc[("type_ptr", `Int ptr)] ->
        begin match PointerMap.find_opt ptr typemap with
        | Some typ -> typ
        | None -> raise (Invalid_Yojson ("Type not found. ptr: " ^ string_of_int ptr, yojson))
        end
      | _ -> raise (Invalid_Yojson ("type_ptr not found", yojson))
    )
  | _ -> []

let make_fuction_typeinfo typemap typedata = List.fold_left (fun map -> function
  | `Variant (
    ("FunctionNoProtoType" | "FunctionProtoType"), Some (`Tuple (
      `Assoc [("pointer", `Int i)] ::
      `Assoc [("return_type", `Assoc [("type_ptr", `Int type_ptr)])] ::
      `Assoc params_type ::
      _
    ))
  ) as yojson ->
    let return_type =
      begin match PointerMap.find_opt type_ptr typemap with
      | Some typ -> typ
      | None -> raise (Invalid_Yojson ("Return type not found.", yojson))
      end
    in
    let param_types = parse_params_type typemap params_type yojson in
    PointerMap.add i { return_type; param_types } map
  | `Variant (
    ("FunctionNoProtoType" | "FunctionProtoType"), Some (`Tuple [
      `Assoc [("pointer", `Int i)];
      `Assoc [("return_type", `Assoc [("type_ptr", `Int type_ptr)])];
    ])
  ) as yojson ->
    let return_type =
      begin match PointerMap.find_opt type_ptr typemap with
      | Some typ -> typ
      | None -> raise (Invalid_Yojson ("Return type not found.", yojson))
      end
    in
    PointerMap.add i { return_type; param_types= [] } map
  | _ ->
    map
  )
  PointerMap.empty
  typedata

(*
let show_fuction_typeinfo function_typeinfo =
  function_typeinfo |> PointerMap.iter (fun idx {return_type; param_types} ->
    let rt = show_c_type return_type in
    let at = param_types |> List.map show_c_type |> String.concat "," in
    Printf.printf "%d => { return: %s, args: %s }\n" idx rt at
  )
*)
let dummy_loc: Cabs.cabsloc = {
  lineno= 0;
  filename= "";
  byteno= 0;
  ident= 0;
}

let extract_location _info =
  let result = dummy_loc in
  result

let parse_parameters typemap : Yojson.Safe.t -> Cabs.single_name = function
  | `Variant (
    "ParmVarDecl", Some (`Tuple (
      `Assoc _source_info ::
      `Assoc name_info ::
      `Assoc [("type_ptr", `Int type_ptr)] ::
      _
    ))
  ) as yojson ->
    let name =
      begin match List.assoc_opt "name" name_info with
      | Some (`String name) -> name
      | _ -> raise (Invalid_Yojson ("Paramater name not found.", yojson))
      end
    in
    let tpe, decl_type =
      begin match find_type typemap type_ptr with
      | Some (tpe, decl_type) -> tpe, decl_type
      | None -> raise (Invalid_Yojson ("Paramater type not found.", yojson))
      end
    in
    [SpecType tpe], (name, decl_type, [], dummy_loc)
  | yojson ->
    raise (Invalid_Yojson ("Invalid paramater data.", yojson))

let extract_variable_scope map =
  let get_scope scope =
    match List.assoc_opt scope map with
    | Some (`Bool true) -> true
    | _ -> false
  in
  Ast.{
    is_global= get_scope "is_global";
    is_static= get_scope "is_static";
    is_static_local= get_scope "is_static_local"
  }

let rec parse_expression typemap : Yojson.Safe.t -> Cabs.expression = function
  | `Variant (
    "UnaryOperator", Some (`Tuple (
      `Assoc _source_info ::
      `List [expr] ::
      _qual_type ::
      `Assoc (("kind", `Variant (kind, None)) :: _) ::
      _
    ))
  ) as yojson ->
    let expr = parse_expression typemap expr in
    begin match kind with
    | "LNot" -> Cabs.UNARY (Cabs.NOT, expr )
    | "Minus" -> Cabs.UNARY (Cabs.MINUS, expr)
    | "PostInc" -> Cabs.UNARY (Cabs.POSINCR, expr)
    | "PreInc" -> Cabs.UNARY (Cabs.PREINCR, expr)
    | "PostDec" -> Cabs.UNARY (Cabs.POSDECR, expr)
    | "PreDec" -> Cabs.UNARY (Cabs.PREDECR, expr)
    | _ -> raise (Invalid_Yojson ("Invalid unary operation.", yojson))
    end
  | `Variant (
    "BinaryOperator", Some (`Tuple (
      `Assoc _source_info ::
      `List [
        left_expr;
        right_expr;
      ] ::
      _qual_type ::
      `Assoc [("kind", `Variant (kind, None))] ::
      _
    ))
  ) as yojson ->
    let left = parse_expression typemap left_expr
    and right = parse_expression typemap right_expr
    in
    begin match kind with
    | "Add" -> Cabs.BINARY (Cabs.ADD, left, right)
    | "Sub" -> Cabs.BINARY (Cabs.SUB, left, right)
    | "Mul" -> Cabs.BINARY (Cabs.MUL, left, right)
    | "Div" -> Cabs.BINARY (Cabs.DIV, left, right)
    | "Rem" -> Cabs.BINARY (Cabs.MOD, left, right)
    | "EQ" -> Cabs.BINARY (Cabs.EQ, left, right)
    | "NE" -> Cabs.BINARY (Cabs.NE, left, right)
    | "LT" -> Cabs.BINARY (Cabs.LT, left, right)
    | "LE" -> Cabs.BINARY (Cabs.LE, left, right)
    | "GT" -> Cabs.BINARY (Cabs.GT, left, right)
    | "GE" -> Cabs.BINARY (Cabs.GE, left, right)
    | "LAnd" -> Cabs.BINARY (Cabs.AND, left, right)
    | "LOr" -> Cabs.BINARY (Cabs.OR, left, right)
    | "Assign" -> Cabs.BINARY (Cabs.ASSIGN, left, right)
    | _ -> raise (Invalid_Yojson ("Invalid binary operation.", yojson))
    end
  (* We should care function call if and only if it is called with constant name. *)
  | `Variant (
    "CallExpr", Some (`Tuple (
      `Assoc _source_info ::
      `List (
        `Variant (
          "ImplicitCastExpr", Some (`Tuple (
            _source_info2 ::
            `List [
              `Variant (
                "DeclRefExpr", Some (`Tuple (
                  _source_info3 ::
                  _body ::
                  _qual_type3 ::
                  `Assoc [("decl_ref", `Assoc [
                    ("kind", `Variant ("Function", None));
                    _decl_pointer;
                    ("name", `Assoc [
                      ("name", `String name);
                      _qual_name
                    ]);
                    _qual_type4;
                  ])] ::
                  _
                ))
              )
            ] ::
            _
          ))
        ) :: args
      ) ::
      _
    ))
  ) ->
    let args = List.map (parse_expression typemap) args in
    Cabs.CALL (Cabs.CONSTANT (Cabs.CONST_STRING name), args)
  | `Variant (
    "ParenExpr", Some (`Tuple (
      `Assoc _source_info ::
      `List [expr] ::
      _
    ))
  ) ->
    Cabs.PAREN (parse_expression typemap expr)
  | `Variant (
    "ImplicitCastExpr", Some (`Tuple (
      _source_info ::
      `List [expr] ::
      _
    ))
  ) ->
    parse_expression typemap expr
  | `Variant (
    "DeclRefExpr", Some (`Tuple (
      `Assoc _source_info ::
      _children ::
      _qual_type ::
      `Assoc [("decl_ref", `Assoc decl_data)] ::
      _
    ))
  ) as yojson ->
    let name =
      begin match List.assoc_opt "name" decl_data with
      | Some (`Assoc name) ->
        begin match List.assoc_opt "name" name with
        | Some (`String name) -> name
        | _ -> raise (Invalid_Yojson ("Name data not found.", yojson))
        end
      | _ -> raise (Invalid_Yojson ("Name data not found.", yojson))
      end
    in
    Cabs.VARIABLE name
  | `Variant (
    "IntegerLiteral", Some (`Tuple (
      `Assoc _source_info ::
      _children ::
      _qual_type ::
      `Assoc data ::
      _
    ))
  ) as yojson ->
    let value =
      begin match List.assoc_opt "value" data with
      | Some (`String value) -> value
      | _ -> raise (Invalid_Yojson ("Invalid expression data.", yojson))
      end
    in
    Cabs.CONSTANT (Cabs.CONST_INT value)
  | `Variant (
    "ArraySubscriptExpr", Some (`Tuple (
      `Assoc _source_info ::
      `List [
        arr;
        idx
      ] ::
      _
    ))
  ) ->
    Cabs.INDEX (
      parse_expression typemap arr,
      parse_expression typemap idx
    )
  | yojson ->
    raise (Invalid_Yojson ("Invalid expression data.", yojson))

and parse_statement typemap : Yojson.Safe.t -> Cabs.statement = function
  | `Variant (
    "DeclStmt", Some (`Tuple (
      `Assoc source_info ::
      _left_expressions ::
      `List var_decls ::
      _
    ))
  ) ->
    let stmts = var_decls |> List.map (parse_statement typemap) in
    let location = extract_location source_info in
    Cabs.BLOCK (conv_block stmts, location)
  | `Variant (
    "VarDecl", Some (`Tuple (
      `Assoc source_info ::
      `Assoc varname_data ::
      `Assoc [("type_ptr", `Int type_ptr)] ::
      `Assoc var_info ::
      _
    ))
  ) as yojson ->
    let name =
      begin match List.assoc_opt "name" varname_data with
      | Some (`String name) -> name
      | _ -> raise (Invalid_Yojson ("Variable name not found.", yojson))
      end
    in
    let tpe, decl_type =
      begin match find_type typemap type_ptr with
      | Some (tpe, decl_type) -> tpe, decl_type
      | None -> raise (Invalid_Yojson ("Variable type not found.", yojson))
      end
    in
    let location = extract_location source_info in
    begin match List.assoc_opt "init_expr" var_info with
    | Some init_expr ->
      let init_expr = parse_expression typemap init_expr in
      Cabs.DEFINITION (Cabs.DECDEF (
        ([Cabs.SpecType tpe], [(name, decl_type, [], dummy_loc), Cabs.SINGLE_INIT init_expr]),
        location
      ))
    | None ->
      Cabs.DEFINITION (Cabs.DECDEF (
        ([Cabs.SpecType tpe], [(name, decl_type, [], dummy_loc), Cabs.NO_INIT]),
        location
      ))
    end
  | `Variant (
    "IfStmt", Some (`Tuple (
      `Assoc source_info ::
      `List body ::
      _
    ))
  ) as yojson ->
    let location = extract_location source_info in
    begin match body with
    | [cond; true_stmts; false_stmts] ->
      Cabs.IF (
        parse_expression typemap cond,
        Cabs.BLOCK (parse_body typemap true_stmts, location),
        Cabs.BLOCK (parse_body typemap false_stmts, location),
        location
      )
    | [cond; true_stmts] ->
      Cabs.IF (
        parse_expression typemap cond,
        Cabs.BLOCK (parse_body typemap true_stmts, location),
        Cabs.NOP dummy_loc,
        location
      )
    | _ -> raise (Invalid_Yojson ("Invalid IF statement.", yojson))
    end
	(*
  | `Variant (
    "ForStmt", Some (`Tuple (
      `Assoc source_info ::
      `List [
        expr1;
        _; (* What is it? *)
        expr2;
        expr3;
        stmts;
      ] ::
      _
    ))
  ) ->
    let location = extract_location source_info in
    Cabs.FOR (
      parse_expression typemap expr1,
      parse_expression typemap expr2,
      parse_expression typemap expr3,
      Cabs.BLOCK (parse_body typemap stmts, location),
      location
    )
	*)
  | `Variant (
    "WhileStmt", Some (`Tuple (
      `Assoc source_info ::
      `List [
        expr;
        stmts;
      ] ::
      _
    ))
  ) ->
    let expr = parse_expression typemap expr in
    let body = parse_body typemap stmts in
    let location = extract_location source_info in
    Cabs.WHILE (expr, (Cabs.BLOCK (body, location)), location)
  | `Variant (
    "SwitchStmt", Some (`Tuple (
      `Assoc source_info ::
      `List [expr; stmts] ::
      _
    ))
  ) ->
  let expr = parse_expression typemap expr in
  let body = parse_body typemap stmts in
  let location = extract_location source_info in
  Cabs.CASE (expr, Cabs.BLOCK (body, location), location)
  | `Variant (
    "ReturnStmt", Some (`Tuple (
      `Assoc source_info ::
      `List expr ::
      _
    ))
  ) as yojson ->
    let location = extract_location source_info in
    begin match expr with
    | [expr] -> Cabs.RETURN (parse_expression typemap expr, location)
    | [] -> Cabs.RETURN (Cabs.NOTHING, location)
    | _ -> raise (Invalid_Yojson ("Return statements has multiple expressions.", yojson))
    end
  | `Variant (
    "BreakStmt", Some (`Tuple (
      `Assoc source_info ::
      _
    ))
  ) ->
    let location = extract_location source_info in
    Cabs.BREAK location
  | `Variant (
    "ContinueStmt", Some (`Tuple (
      `Assoc source_info ::
      _
    ))
  ) ->
    let location = extract_location source_info in 
    Cabs.CONTINUE location
  | `Variant (
    "GotoStmt", Some (`Tuple (
      `Assoc source_info ::
      `List _ ::
      `Assoc lbl ::
      _
    ))
  ) ->
    let location = extract_location source_info in
    let label =
      match List.assoc_opt "label" lbl with
      | Some (`String name) -> name
      | _ -> ""
    in
    Cabs.GOTO (label, location)
  | `Variant (
    "LabelStmt", Some (`Tuple (
      `Assoc source_info ::
      `List [stmt] ::
      `String label ::
      _
    ))
  ) ->
    let location = extract_location source_info in
	Cabs.LABEL (label, parse_statement typemap stmt, location)
  | `Variant (
    "CaseStmt", Some (`Tuple (
      `Assoc source_info ::
      `List lst ::
      _
    ))
  ) as yojson ->
    let location = extract_location source_info in
    (match lst with
    | [expr; stmt] ->
      let expr = parse_expression typemap expr in print_string "here\n";
      Cabs.CASE (expr, parse_statement typemap stmt, location)
    | _ -> raise (Invalid_Yojson ("Something wrong with case statement.", yojson)))
  | expr ->
    Cabs.COMPUTATION (parse_expression typemap expr, dummy_loc)

and parse_body typemap : Yojson.Safe.t -> Cabs.block = function
  | `Variant (
    "CompoundStmt", Some (`Tuple (
      _source_info ::
      `List statements ::
      _
    ))
  ) ->
    conv_block (statements |> List.map (parse_statement typemap))
  | yojson ->
    conv_block [parse_statement typemap yojson]

and conv_block block : Cabs.block = {
  blabels= [];
  battrs= [];
  bstmts= block
}

let cabs_of_yojson typemap function_typeinfo definitions =
  let parse_definition definitions = function
    | `Variant (
      "VarDecl", Some (`Tuple (
        `Assoc source_info :: (* filename, line num, col num, &c. *)
        `Assoc name_data ::
        `Assoc [("type_ptr", `Int type_ptr)] ::
        `Assoc var_info ::
        _
      ))
    ) as yojson ->
      let location = extract_location source_info in
      let name =
        begin match List.assoc_opt "name" name_data with
        | Some (`String name) -> name
        | _ -> raise (Invalid_Yojson ("Function name not found.", yojson))
        end
      in
      let tpe, decl_type =
        begin match find_type typemap type_ptr with
        | Some (tpe, decl_type) -> tpe, decl_type
        | None -> raise (Invalid_Yojson ("Type not found.", yojson))
        end
      in
      begin match List.assoc_opt "init_expr" var_info with
      | Some init_expr ->
        let init_expr = parse_expression typemap init_expr in
        Cabs.DECDEF (
          ([Cabs.SpecType tpe], [(name, decl_type, [], dummy_loc), Cabs.SINGLE_INIT init_expr]),
          location
        ) :: definitions
      | None ->
        Cabs.DECDEF (
          ([Cabs.SpecType tpe], [(name, decl_type, [], dummy_loc), Cabs.NO_INIT]),
          location
        ) :: definitions
      end
    | `Variant (
      "FunctionDecl", Some (`Tuple (
        `Assoc source_info ::
        `Assoc name_data ::
        `Assoc [("type_ptr", `Int type_ptr)] ::
        `Assoc data ::
        _
      ))
    ) as yojson ->
        let name =
          begin match List.assoc_opt "name" name_data with
          | Some (`String name) -> name
          | _ -> raise (Invalid_Yojson ("Function name not found.", yojson))
          end
        in
        let location = extract_location source_info in
        let return_type, decl_type =
          begin match PointerMap.find_opt type_ptr function_typeinfo with
          | Some { return_type; _ } ->
            begin match return_type with
            | Just tpe -> tpe, Cabs.JUSTBASE
            | Array { ptr; size} ->
              begin match find_type typemap ptr with
              | Some (tpe, decl_type) ->
                let expr = Cabs.CONSTANT (Cabs.CONST_INT (string_of_int size)) in
                tpe, (Cabs.ARRAY (decl_type, [], expr))
              | None -> raise (Invalid_Yojson ("Function type not found.", yojson))
              end
            | Pointer i ->
              match find_type typemap i with
              | Some (tpe, decl_type) -> tpe, (Cabs.PTR ([], decl_type))
              | None -> raise (Invalid_Yojson ("Function type not found.", yojson))
            end
          | None -> raise (Invalid_Yojson ("Function type not found.", yojson))
          end
        in
        let single_name = [Cabs.SpecType return_type], (name, decl_type, [], dummy_loc) in
		(*
        let params =
          begin match List.assoc_opt "parameters" data with
          | Some `List params -> List.map (parse_parameters typemap) params
          | _ -> []
          end
        in
		*)
        begin match List.assoc_opt "body" data with
        | Some body ->
          let body = parse_body typemap body in
          Cabs.FUNDEF (single_name, body, location, location) :: definitions
        | None ->
          Cabs.FUNDEF (single_name, conv_block [], location, location) :: definitions
        end
    | _ ->
      definitions
  in
  definitions
  |> List.fold_left parse_definition []
  |> List.rev

let cabs_of_yojson (fname:string) : Yojson.Safe.t -> Cabs.file = function
  | `Variant (
      "TranslationUnitDecl", Some (`Tuple (
        _metadata :: (* ? *)
        `List decls ::
        _any :: (* This is empty. *)
        `Assoc data ::
        _
      ))
    ) as yojson ->
        let typedata =
          begin match List.assoc_opt "types" data with
          | Some (`List typedata) -> typedata
          | _ -> raise (Invalid_Yojson ("Type data not found.", yojson))
          end
        in
        let typemap = make_typemap typedata in
        (* For debbug 
        show_typemap typemap;*)
        let function_typeinfo = make_fuction_typeinfo typemap typedata in
        (* For debbug 
        show_fuction_typeinfo function_typeinfo;*)
        let definitions = cabs_of_yojson typemap function_typeinfo decls in
        fname, definitions
  | yojson ->
    raise (Invalid_Yojson ("Invalid AST Yojson.", yojson))

let parse_yojson fname =
  let yojson = Yojson.Safe.from_file fname in
  try Ok (cabs_of_yojson fname yojson) with
  | Invalid_Yojson (message, yojson) ->
    Error (Invalid_Yojson (message, yojson))
