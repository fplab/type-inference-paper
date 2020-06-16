let parse line =
  let linebuf = Lexing.from_string line in
  Parser.main Lexer.token linebuf
(* open Syntax
let string_of_unop u = match u with
  | Syntax.OpNeg -> "OpNeg"

let string_of_binop b = match b with
  | Syntax.OpPlus -> "OpPlus"
  | Syntax.OpMinus -> "OpMinus"
  | Syntax.OpTimes -> "OpTimes"

let rec string_of_expr e = match e with
  | Syntax.ENumLiteral n -> "ENumLiteral "^(string_of_int n)
  | Syntax.EUnOp (unop, e) ->
    String.concat
      ""
      [
        "EUnOp";
        " (";
        string_of_unop unop;
        ", ";
        string_of_expr e;
        ")"
      ]
  | Syntax.EBinOp (e1, binop, e2) ->
    String.concat
      ""
      [
        "EBinOp";
        " (";
        string_of_expr e1;
        ", ";
        string_of_binop binop;
        ", ";
        string_of_expr e2;
        ")";
      ]

let process (line : string) =
  let linebuf = Lexing.from_string line in
  try
    (* Run the parser on this line of input. *)
    Printf.printf "\n%s\n%!" (string_of_expr (Parser.main Lexer.token linebuf))
  with
  | Lexer.Error msg ->
      Printf.fprintf stderr "%s\n%!" msg
  | Parser.Error ->
      Printf.fprintf stderr "\nAt offset %d: syntax error.\n%!" (Lexing.lexeme_start linebuf)

let process (optional_line : string option) =
  match optional_line with
  | None ->
      ()
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

let parse =
  repeat (Lexing.from_channel stdin) *)


(* [subst e1 e2 x] is [e1] with [e2] substituted for [x]. *)
(* let rec subst e1 e2 x = match e1 with
  | Var y      -> if x=y then e2 else e1
  | Int c      -> Int c
  | Add(el,er) -> Add(subst el e2 x, subst er e2 x)
  | Let(y,ebind,ebody) ->
    if x=y
    then Let(y, subst ebind e2 x, ebody)
    else Let(y, subst ebind e2 x, subst ebody e2 x)
  | Mult(el,er) -> Mult(subst el e2 x, subst er e2 x) *)

(* A single step of evaluation. *)
(* let rec step = function
  | Int n               -> failwith "Does not step"
  | Var _               -> failwith "Unbound variable"
  | Add(Int n1, Int n2) -> Int (n1+n2)
  | Add(Int n1, e2)     -> Add(Int n1, step e2)
  | Add(e1,e2)          -> Add(step e1, e2)
  | Let(x,Int n,e2)     -> subst e2 (Int n) x
  | Let(x,e1,e2)        -> Let(x,step e1, e2)
  | Mult(Int n1, Int n2)-> Int (n1*n2)
  | Mult(Int n1, e2)    -> Mult(Int n1, step e2)
  | Mult(e1,e2)         -> Mult(step e1, e2) *)

(* The reflexive, transitive closure of [step]. *)
(* let rec multistep = function
  | Int n -> Int n
  | e     -> multistep (step e) *)

(***********************************************************************)
(* Everything above this is essentially the same as we saw in lecture. *)
(***********************************************************************)

(* Parse a string into an ast *)


(*   let lexbuf = Lexing.from_string s in
  let ast = Parser.main Lexer.token lexbuf in
  ast *)

(* Extract a value from an ast node.
   Raises Failure if the argument is a node containing a value. *)
(* let extract_value = function
  | Int i -> i
  | _ -> failwith "Not a value" *)

(* Interpret an expression *)
(* let interp e =
  e |> parse |> multistep |> extract_value *)

(* A few test cases *)
(* let run_tests () =
  assert (22 = interp "22");
  assert (22 = interp "11+11");
  assert (22 = interp "(10+1)+(5+6)");
  assert (22 = interp "let x = 22 in x");
  assert (22 = interp "let x = 0 in let x = 22 in x");
  assert (22 = interp "2*11");
  assert (22 = interp "2+2*10");
  assert (14 = interp "2*2+10");
  assert (40 = interp "2*2*10") *)


