# 1 "lexer.mll"
 
  open Parser

  exception Error of string


# 9 "lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base =
   "\000\000\254\255\255\255\001\000\253\255\003\000\239\255\087\000\
    \241\255\242\255\000\000\017\000\012\000\195\000\000\000\249\255\
    \250\255\006\000\252\255\015\000\254\255\255\255\244\255\248\255\
    \023\001\107\001\022\000\246\255\024\000\032\000\245\255\243\255\
    ";
  Lexing.lex_backtrk =
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\015\000\
    \255\255\255\255\016\000\016\000\016\000\015\000\016\000\255\255\
    \255\255\004\000\255\255\002\000\255\255\255\255\255\255\255\255\
    \015\000\008\000\255\255\255\255\255\255\255\255\255\255\255\255\
    ";
  Lexing.lex_default =
   "\003\000\000\000\000\000\003\000\000\000\006\000\000\000\255\255\
    \000\000\000\000\255\255\255\255\255\255\255\255\255\255\000\000\
    \000\000\255\255\000\000\255\255\000\000\000\000\000\000\000\000\
    \255\255\255\255\255\255\000\000\255\255\255\255\000\000\000\000\
    ";
  Lexing.lex_trans =
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\002\000\002\000\021\000\020\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\021\000\000\000\000\000\000\000\000\000\
    \000\000\031\000\000\000\017\000\016\000\000\000\018\000\000\000\
    \014\000\000\000\000\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\015\000\023\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\000\000\000\000\011\000\000\000\000\000\000\000\000\000\
    \000\000\012\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\009\000\000\000\
    \008\000\000\000\000\000\000\000\007\000\007\000\007\000\007\000\
    \007\000\013\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\010\000\
    \028\000\026\000\022\000\027\000\029\000\030\000\000\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\000\000\000\000\000\000\
    \001\000\004\000\000\000\255\255\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \024\000\007\000\007\000\007\000\007\000\007\000\007\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\025\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000";
  Lexing.lex_check =
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\000\000\003\000\005\000\005\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\005\000\255\255\255\255\255\255\255\255\
    \255\255\010\000\255\255\005\000\005\000\255\255\005\000\255\255\
    \005\000\255\255\255\255\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\014\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\255\255\255\255\005\000\255\255\255\255\255\255\255\255\
    \255\255\005\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\005\000\255\255\
    \005\000\255\255\255\255\255\255\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\007\000\005\000\
    \011\000\012\000\017\000\026\000\028\000\029\000\255\255\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\013\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\255\255\255\255\255\255\
    \000\000\003\000\255\255\005\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\024\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\025\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255";
  Lexing.lex_base_code =
   "";
  Lexing.lex_backtrk_code =
   "";
  Lexing.lex_default_code =
   "";
  Lexing.lex_trans_code =
   "";
  Lexing.lex_check_code =
   "";
  Lexing.lex_code =
   "";
}

let rec line lexbuf =
   __ocaml_lex_line_rec lexbuf 0
and __ocaml_lex_line_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
let
# 13 "lexer.mll"
                     line
# 209 "lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 15 "lexer.mll"
    ( Some line, true )
# 213 "lexer.ml"

  | 1 ->
# 18 "lexer.mll"
    ( None, false )
# 218 "lexer.ml"

  | 2 ->
let
# 19 "lexer.mll"
               line
# 224 "lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 22 "lexer.mll"
    ( Some (line ^ "\n"), false )
# 228 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_line_rec lexbuf __ocaml_lex_state

and token lexbuf =
   __ocaml_lex_token_rec lexbuf 5
and __ocaml_lex_token_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 29 "lexer.mll"
    ( token lexbuf )
# 240 "lexer.ml"

  | 1 ->
# 31 "lexer.mll"
    ( EOL )
# 245 "lexer.ml"

  | 2 ->
let
# 32 "lexer.mll"
                i
# 251 "lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 33 "lexer.mll"
    ( INT (int_of_string i) )
# 255 "lexer.ml"

  | 3 ->
# 35 "lexer.mll"
    ( PLUS )
# 260 "lexer.ml"

  | 4 ->
# 37 "lexer.mll"
    ( LPAREN )
# 265 "lexer.ml"

  | 5 ->
# 39 "lexer.mll"
    ( RPAREN )
# 270 "lexer.ml"

  | 6 ->
# 41 "lexer.mll"
    ( OFTYPE )
# 275 "lexer.ml"

  | 7 ->
# 43 "lexer.mll"
    ( ARROW )
# 280 "lexer.ml"

  | 8 ->
# 45 "lexer.mll"
    ( FUN )
# 285 "lexer.ml"

  | 9 ->
# 47 "lexer.mll"
    ( NUM )
# 290 "lexer.ml"

  | 10 ->
# 49 "lexer.mll"
    ( HOLE )
# 295 "lexer.ml"

  | 11 ->
# 51 "lexer.mll"
    (LHOLEP)
# 300 "lexer.ml"

  | 12 ->
# 53 "lexer.mll"
    (RHOLEP)
# 305 "lexer.ml"

  | 13 ->
# 55 "lexer.mll"
    (LBRA)
# 310 "lexer.ml"

  | 14 ->
# 57 "lexer.mll"
    (RBRA)
# 315 "lexer.ml"

  | 15 ->
let
# 58 "lexer.mll"
                                           i
# 321 "lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 59 "lexer.mll"
    ( ID (i) )
# 325 "lexer.ml"

  | 16 ->
# 61 "lexer.mll"
    ( raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) )
# 330 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_token_rec lexbuf __ocaml_lex_state

;;

