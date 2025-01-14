type cabsloc = {
  lineno: int;
  filename: string;
  byteno: int;
  ident: int;
}

type file = string * definition list

and typeSpecifier = 
    Tvoid            
  | Tint

and spec_elem =
    SpecType of typeSpecifier
  
and specifier = spec_elem list

and decl_type =
    JUSTBASE
  | PTR of attribute list * decl_type (* Not appearing because it is outside the range of 'small c'. *)
  | ARRAY of decl_type * attribute list * expression                                      

and name_group = specifier * name list

and field_group = specifier * (name * expression option) list

and init_name_group = specifier * init_name list

and name = string * decl_type * attribute list * cabsloc

and init_name = name * init_expression

and single_name = specifier * name

and definition =
    FUNDEF of single_name * block * cabsloc * cabsloc
  | DECDEF of init_name_group * cabsloc        (* global variable(s), or function prototype *)

and block = 
    { blabels: string list;
      battrs: attribute list;
      bstmts: statement list
    } 

and statement =
    NOP of cabsloc
  | COMPUTATION of expression * cabsloc
  | BLOCK of block * cabsloc
  | IF of expression * statement * statement * cabsloc
  | WHILE of expression * statement * cabsloc
  | FOR of (*formula * *) for_clause * expression * expression * statement * cabsloc
  | RETURN of expression * cabsloc
  | SWITCH of expression * statement * cabsloc
  | CASE of expression * statement * cabsloc
  | DEFINITION of definition 
  | BREAK of cabsloc
  | CONTINUE of cabsloc
  | GOTO of string * cabsloc
  | LABEL of string * statement * cabsloc

and for_clause = 
    FC_EXP of expression
  | FC_DECL of definition

(*
and compound = (string * string list * expression list) 

and formula = string list * expression list * bool * compound list * (string * expression list) list 
*)
 
and binary_operator =
    ADD | SUB | MUL | DIV | MOD
  | AND | OR
  | EQ | NE | LT | GT | LE | GE
  | ASSIGN
  
and unary_operator =
    MINUS | PLUS | NOT | BNOT | MEMOF | ADDROF
  | PREINCR | PREDECR | POSINCR | POSDECR

and expression =
    NOTHING
  | UNARY of unary_operator * expression
  | BINARY of binary_operator * expression * expression
  | CALL of expression * expression list
  | CONSTANT of constant
  | PAREN of expression
  | VARIABLE of string
  | INDEX of expression * expression
 
and constant =
  | CONST_INT of string   (* the textual representation *)
  | CONST_STRING of string
 
and init_expression =
  | NO_INIT
  | SINGLE_INIT of expression
  
and attribute = string * expression list
