open Syntax

let rec string_of_typ(typ:Typ.t) =
  match typ with
  | THole var ->  "THole["^string_of_int(var)^"]"
  | TNum -> "TNum"
  | TArrow (t1,t2) -> string_of_typ(t1) ^ "->"^ string_of_typ(t2)
;;

let rec print_subs(subs: Typ.subs) =
  match subs with
  | [] -> Printf.printf "%s\n" " "
  | hd::tl -> 
    let (var,typ) = hd in
    Printf.printf "%s\n" ("(" ^ string_of_int(var) ^ ") ("^ string_of_typ(typ) ^ ")");
    print_subs(tl);
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
  | EAsc (exp,typ) -> string_of_exp(exp)^":"^string_of_typ(typ)
  | EEmptyHole hole_id -> "(|["^string_of_int(hole_id)^"]|)"
  | EExpHole (hole_id, exp)->"(|["^string_of_int(hole_id)^"]"^string_of_exp(exp)^"|)"
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

let solve (ctx: Ctx.t) (e: Exp.t) = 
  match Impl.syn ctx e with
  | None -> Printf.printf "%s" "ERROR\n: syn/ana error"
  | Some (typ,cons) -> (
    Printf.printf "+ syn/ana result typ:\n %s\n" (string_of_typ typ);
    Printf.printf "\n+ constraints:\n";
    print_cons cons;
    Printf.printf "\n+ unify results: (<hole_id>) (<type>)\n";
    match Impl.unify cons with
    | None -> Printf.printf "%s\n" "@@@ ERROR: unify error @@@"
    | Some subs -> ( 
      print_subs subs;
      let new_typ = Impl.apply subs typ in
      Printf.printf "+ final result of infer typ:\n %s\n" (string_of_typ new_typ);
    )
  )
;;