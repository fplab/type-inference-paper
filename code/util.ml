open Syntax

let format_ty (typ: Typ.t) (typ_str: string): string =
  match typ with
  | THole _ 
  | TNum
  | TBool -> typ_str
  | _ -> "(" ^ typ_str ^ ")"
;;

let rec string_of_typ (typ:Typ.t) =
  match typ with
  | THole var ->  "T?["^string_of_int(var)^"]"
  | TNum -> "TNum"
  | TBool -> "TBool"
  | TArrow (t1,t2) -> (format_ty t1 (string_of_typ t1)) ^ "->" ^ (format_ty t2 (string_of_typ t2))
  | TSum (t1,t2) -> (format_ty t1 (string_of_typ t1)) ^ "+" ^ (format_ty t2 (string_of_typ t2))
  | TProd (t1,t2) -> (format_ty t1 (string_of_typ t1)) ^ "*" ^ (format_ty t2 (string_of_typ t2))
;;
(*
let rec string_of_typ (typ:Typ.t) =
  match typ with
  | THole var ->  "THole["^string_of_int(var)^"]"
  | TNum -> "TNum"
  | TBool -> "TBool"
  | TArrow (t1,t2) -> "(" ^ string_of_typ(t1) ^ ")->(" ^ string_of_typ(t2) ^ ")"
  | TSum (t1,t2) -> "(" ^ string_of_typ(t1) ^ ")+(" ^ string_of_typ(t2) ^ ")"
  | TProd (t1,t2) -> "(" ^ string_of_typ(t1) ^ ")*(" ^ string_of_typ(t2) ^ ")"
;;
*)

let rec string_of_typ_ls (typ_ls:Typ.t list) =
  match typ_ls with
  | [] -> " "
  | hd::tl -> 
    (string_of_typ hd)^ ", " ^ (string_of_typ_ls tl);
;;

let rec string_of_u_results (results: Typ.unify_results) =
  match results with
  | [] -> "\n"
  | hd::tl -> (
    let (var,typ) = hd in
    (
      match typ with 
      | Solved typ' -> ("solved: (" ^ string_of_int(var) ^ ") ("^ string_of_typ(typ') ^ ")\n");
      | Ambiguous (typ_op, typ_ls) -> (
        match typ_op with
        | Some typ -> 
          ("ambiguous: (" ^ string_of_int(var) ^ ") (" ^ string_of_typ(typ) ^ "; "
            ^ string_of_typ_ls(typ_ls) ^ ")\n");
        | None -> ("ambiguous: (" ^ string_of_int(var) ^ ") (None; "^ string_of_typ_ls(typ_ls) ^ ")\n");
      )
      | UnSolved typ_ls -> 
        ("unsolved: (" ^ string_of_int(var) ^ ") ("^ string_of_typ_ls(typ_ls) ^ ")\n");
    ) ^ string_of_u_results(tl);
  )
;;

let rec string_of_r_results (results: Typ.rec_unify_results) =
  match results with
  | [] -> "\n"
  | hd::tl -> (
    let (typ,res) = hd in
    (
      match res with 
      | Solved res' -> ("solved: (" ^ string_of_typ(typ) ^ ") ("^ string_of_typ(res') ^ ")\n");
      | Ambiguous (res_op, res_ls) -> (
        match res_op with
        | Some res' -> 
          ("ambiguous: (" ^ string_of_typ(typ) ^ ") (" ^ 
            string_of_typ(res') ^ "; " ^ string_of_typ_ls(res_ls) ^ ")\n");
        | None -> ("ambiguous: (" ^ string_of_typ(typ) ^ ") (None; "^ string_of_typ_ls(res_ls) ^ ")\n");
      )
      | UnSolved res_ls -> 
        ("unsolved: (" ^ string_of_typ(typ) ^ ") ("^ string_of_typ_ls(res_ls) ^ ")\n");
    ) ^ string_of_r_results(tl);
  )
;;

let rec string_of_typ_gens (gen: TypGen.typ_gens) =
  match gen with
  | [] -> "\n"
  | hd::[] -> (string_of_typ_gen hd);
  | hd::tl -> (
    let hd_str = string_of_typ_gen hd in
    (hd_str ^ "//" ^ (string_of_typ_gens tl));
  )
and string_of_typ_gen (gen_elt: TypGen.typ_gen) =
  match gen_elt with
  | Base btyp -> (string_of_typ (TypGen.base_typ_to_typ btyp));
  | Compound (ctr, gens1, gens2) -> (
    let str1 = string_of_typ_gens gens1 in
    let str2 = string_of_typ_gens gens2 in
    let ctr_str = 
      match ctr with
      | Arrow -> "->"
      | Prod -> "*"
      | Sum -> "+"
    in
    ("[{" ^ str1 ^ "}" ^ ctr_str ^ "{" ^ str2 ^ "}]");
  )
;;

let rec string_of_solutions (sol: Status.solution list) =
  match sol with
  | [] -> "\n";
  | hd::tl -> (
    let (key, res) = hd in
    let hd_str =
      match res with
      | Solved typ -> ("solved: (" ^ string_of_typ(key) ^ ") - " ^ string_of_typ(typ) ^ "\n");
      | UnSolved gen -> (
        let sorted_gen = TypGen.gens_sort_layer gen in
        ("unsolved: (" ^ string_of_typ(key) ^ ") - " ^ string_of_typ_gens(sorted_gen) ^ "\n");
      )
    in
    hd_str ^ (string_of_solutions tl)
  )
;;

let rec string_of_gen_res (gen_results: TypGenRes.results) =
  match gen_results with
  | [] -> "\n";
  | hd::tl -> (
    let (key, res) = hd in
    let hd_str = 
      (string_of_typ key) ^ " type_gen_res: " ^ (string_of_typ_gens res) ^ "\n"
    in
    hd_str ^ (string_of_gen_res tl)
  )
;;

let rec string_of_exp(exp: Exp.t) =
  match exp with
  | EVar id -> id
  | ELam (id,exp) -> "λ"^id^"."^string_of_exp(exp);
  | ELamAnn (id,typ,exp) -> "λ"^id^":"^string_of_typ(typ)^"."^string_of_exp(exp);
  | EBinOp (exp1,binop,exp2) -> (
    match binop with
    | OpAp -> string_of_exp(exp1)^" "^string_of_exp(exp2)
    | OpPlus -> string_of_exp(exp1)^" + "^string_of_exp(exp2)
  )
  | ENumLiteral num -> string_of_int(num)
  | EBoolLiteral boo -> string_of_bool(boo)
  | EAsc (exp,typ) -> string_of_exp(exp)^":"^string_of_typ(typ)
  | EEmptyHole hole_id -> "(|["^string_of_int(hole_id)^"]|)"
  | EExpHole (hole_id, exp)->"(|["^string_of_int(hole_id)^"]"^string_of_exp(exp)^"|)"
  | EIf(e1,e2,e3) -> "if "^string_of_exp(e1)^" then "^string_of_exp(e2)^" else "^string_of_exp(e3)
  | ELet(x,Some typ, e1, e2) -> "let "^x^":"^string_of_typ(typ)^" = "^string_of_exp(e1)^" in "^string_of_exp(e2)
  | ELet(x,None, e1, e2) -> "let "^x^" = "^string_of_exp(e1)^" in "^string_of_exp(e2)
  | EPair(e1,e2) -> "("^string_of_exp(e1)^" , "^string_of_exp(e2)^")"
  | ELetPair (x,y,e1,e2) -> "let ("^x^" , "^y^") = "^string_of_exp(e1)^" in "^string_of_exp(e2)
  | EPrjL e -> "["^string_of_exp(e)^"].0"
  | EPrjR e -> "["^string_of_exp(e)^"].1"
  | EInjL e -> "L["^string_of_exp(e)^"]"
  | EInjR e -> "R["^string_of_exp(e)^"]"
  | ECase (e1, x, e2, y, e3) -> "case "^string_of_exp(e1)^" of L["^x^"] -> "^string_of_exp(e2)^"else R["^y^"] -> "^string_of_exp(e3)
;;

let print_exp(exp: Exp.t) = Printf.printf "EXP:  %s\n" (string_of_exp exp)
;;

let rec print_cons(constraints: Constraints.t) = 
  match constraints with
  | [] -> ();
  | hd::tl -> (
    let (typ1,typ2) = hd in Printf.printf "%s\n" (string_of_typ(typ1)^" == "^ string_of_typ(typ2));
    print_cons(tl);
  )
;;

let rec print_ctx(ctx: Ctx.t) =
  match ctx with
  | [] -> ();
  | hd::tl -> (
    let (id,typ) = hd in
    Printf.printf "%s\n" (id^" : "^ string_of_typ(typ));
    print_ctx(tl);
  )
;;

let rec update_type_variable (ctx: Ctx.t) (e: Exp.t): unit =
  match e with
  | EVar x ->(
    match Ctx.lookup ctx x with
    | None -> ();
    | Some(typ) -> Typ.load_type_variable typ;
    )
  | ELam (_, exp) -> update_type_variable ctx exp;
  | ELamAnn (_, ty_in, exp) -> (
    Typ.load_type_variable(ty_in);
    update_type_variable ctx exp;
  )
  | EBinOp (e1, _, e2) -> (
    update_type_variable ctx e1;
    update_type_variable ctx e2;
  )
  | ENumLiteral _ 
  | EBoolLiteral _ -> ();
  | EAsc (exp, typ) -> (
    Typ.load_type_variable(typ);
    update_type_variable ctx exp;
  )
  | EEmptyHole _
  | EExpHole _ -> ();
  | EIf(e1,e2,e3) -> (
    update_type_variable ctx e1;
    update_type_variable ctx e2;
    update_type_variable ctx e3;
  )
  | ELet(_,Some typ, e1, e2) -> (
    Typ.load_type_variable(typ);
    update_type_variable ctx e1;
    update_type_variable ctx e2;
  )
  | ELet(_,None, e1, e2) 
  | EPair(e1,e2) 
  | ELetPair (_,_,e1,e2) -> (
    update_type_variable ctx e1;
    update_type_variable ctx e2;
  )
  | EPrjL e 
  | EPrjR e 
  | EInjL e 
  | EInjR e ->(
    update_type_variable ctx e;
  )
  | ECase (e1, _, e2, _, e3) -> (
    update_type_variable ctx e1;
    update_type_variable ctx e2;
    update_type_variable ctx e3;
  )
;;
let solve (ctx: Ctx.t) (e: Exp.t) = 
  update_type_variable ctx e;
  match Impl.syn ctx e with
  | None -> Printf.printf "%s" "ERROR\n: syn/ana error"
  | Some (typ,cons) -> (
    Printf.printf "+ syn/ana result typ:\n %s\n" (string_of_typ typ);
    Printf.printf "\n+ constraints:\n";
    print_cons cons;
    Printf.printf "\n+ unify results: (<hole_id>) (<type>)\n";
    let gen_results = Impl.unify cons in 
    Printf.printf "%s" (string_of_gen_res gen_results);
    (*calls to new dfs code *)
    Printf.printf "depth first search simplified results\n";
    let solutions_given = Dfs.finalize_results gen_results in
    Printf.printf "%s" (string_of_solutions solutions_given);
  )
;;

(*
let y : ?9 = let x : ?1 = (1, true) in x.0 in y

matched prod will generate two type holes

let x : ?1 = (1, true) in x

(1, true) ana ?1
?1 == ?2 * ?3

1 ana ?2
?2 == Num

true ana ?3
?3 == Bool

^these are keys in gen_results
*)