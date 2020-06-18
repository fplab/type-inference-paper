let process (line : string) =
  let linebuf = Lexing.from_string line in
  Parser.main Lexer.token linebuf

let process (optional_line : string option) =
match optional_line with
| None ->
process "1+2"
| Some line ->
    process line

(* let rec repeat channel =
(* Attempt to read one line. *)
let optional_line, continue = Lexer.line channel in
process optional_line;
if continue then
  repeat channel *)

  let repeat channel =
    (* Attempt to read one line. *)
    let optional_line, _ = Lexer.line channel in
    process optional_line
    ;;

let parse s =
repeat (Lexing.from_string s)
