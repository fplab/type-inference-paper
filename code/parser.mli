
(* The type of tokens. *)

type token = 
  | TIMES
  | THEN
  | RPRJ
  | RPAREN
  | RHOLEP
  | RBRA
  | R
  | PLUS
  | OFTYPE
  | OF
  | NUM
  | LPRJ
  | LPAREN
  | LHOLEP
  | LET
  | LBRA
  | L
  | INT of (int)
  | IN
  | IF
  | ID of (string)
  | HOLE
  | FUN
  | EOL
  | ELSE
  | COMMA
  | CASE
  | BOOLLIT of (bool)
  | BOOL
  | BE
  | ARROW

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val main: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.Exp.t)
