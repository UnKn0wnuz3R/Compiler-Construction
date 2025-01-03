// Signature file for parser generated by fsyacc
module Parser
type token = 
  | ID of (string)
  | NUM of (int)
  | EOF
  | AMP
  | COMMA
  | SEMICOLON of (int)
  | RPAR of (int)
  | LPAR
  | LBRA
  | RBRA
  | ASSIGN
  | PLUS
  | MINUS
  | STAR
  | DIVIDE
  | EQUAL
  | NOTEQ
  | LEQ
  | LESS
  | GEQ
  | GREATER
  | AND
  | OR
  | NOT
  | NUL
  | TRUE
  | FALSE
  | INT
  | BOOL
  | IF
  | ELSE
  | WHILE
  | RETURN
type tokenId = 
    | TOKEN_ID
    | TOKEN_NUM
    | TOKEN_EOF
    | TOKEN_AMP
    | TOKEN_COMMA
    | TOKEN_SEMICOLON
    | TOKEN_RPAR
    | TOKEN_LPAR
    | TOKEN_LBRA
    | TOKEN_RBRA
    | TOKEN_ASSIGN
    | TOKEN_PLUS
    | TOKEN_MINUS
    | TOKEN_STAR
    | TOKEN_DIVIDE
    | TOKEN_EQUAL
    | TOKEN_NOTEQ
    | TOKEN_LEQ
    | TOKEN_LESS
    | TOKEN_GEQ
    | TOKEN_GREATER
    | TOKEN_AND
    | TOKEN_OR
    | TOKEN_NOT
    | TOKEN_NUL
    | TOKEN_TRUE
    | TOKEN_FALSE
    | TOKEN_INT
    | TOKEN_BOOL
    | TOKEN_IF
    | TOKEN_ELSE
    | TOKEN_WHILE
    | TOKEN_RETURN
    | TOKEN_end_of_input
    | TOKEN_error
type nonTerminalId = 
    | NONTERM__startprog
    | NONTERM_exp
    | NONTERM_ctype
    | NONTERM_stmts
    | NONTERM_stmt
    | NONTERM_elseopt
    | NONTERM_args
    | NONTERM_func
    | NONTERM_prog
/// This function maps tokens to integer indexes
val tagOfToken: token -> int

/// This function maps integer indexes to symbolic token ids
val tokenTagToTokenId: int -> tokenId

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
val prodIdxToNonTerminal: int -> nonTerminalId

/// This function gets the name of a token as a string
val token_to_string: token -> string
val prog : (FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> FSharp.Text.Lexing.LexBuffer<'cty> -> (AST.Program) 
