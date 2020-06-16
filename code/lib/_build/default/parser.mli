
(* The type of tokens. *)

type token = 
  | RPAREN
  | RHOLEP
  | RBRA
  | PLUS
  | OFTYPE
  | NUM
  | LPAREN
  | LHOLEP
  | LBRA
  | INT of (int)
  | ID of (string)
  | HOLE
  | FUN
  | EOL
  | ARROW

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val main: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.Exp.t)
