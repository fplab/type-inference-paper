
(* The type of tokens. *)

type token = 
  | UNROLL
  | UNIT
  | TIMES
  | TID of (string)
  | THEN
  | RSQUARE
  | RPRJ
  | RPAREN
  | ROLL
  | REC
  | R
  | PLUS
  | OFTYPE
  | OF
  | NUM
  | MINUS
  | LT
  | LSQUARE
  | LPRJ
  | LPAREN
  | LET
  | L
  | INT of (int)
  | IN
  | IF
  | GT
  | FUN
  | FORALLT
  | FORALL
  | FIX
  | EQ
  | EOL
  | ELSE
  | EID of (string)
  | DOT
  | COMMA
  | CASE
  | BOOLLIT of (bool)
  | BOOL
  | BE
  | AT
  | ARROW

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val main: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.Exp.t)
