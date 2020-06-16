exception Impossible

module Identifier = struct
  type t = string
end

module TypeInferenceVar = struct
  type t = int
  let recent (var_1:t) (var_2:t) = max var_1 var_2;; 
end

module Typ = struct
  type t =
    | THole of TypeInferenceVar.t
    | TNum
    | TArrow of t * t

  type subs = (TypeInferenceVar.t * t) list
  let type_variable = ref (0)

  (* generates a new unique type variable *)
  let gen_new_type_var () =
      let var = !type_variable in
      incr type_variable; var
    ;;
  
  let rec load_type_variable (t: t) =
    match t with
    | THole id -> type_variable:= TypeInferenceVar.recent id !type_variable
    | TNum -> ()
    | TArrow (ty1,ty2)-> (
      load_type_variable(ty1);
      load_type_variable(ty2);
    )
end


module Exp = struct

  type hole_id = int

  type binop = OpAp | OpPlus

  type t =
    | EVar of Identifier.t
    | ELam of Identifier.t * t
    | ELamAnn of Identifier.t * Typ.t * t
    | EBinOp of t * binop * t
    | ENumLiteral of int
    | EAsc of t * Typ.t
    | EEmptyHole of hole_id
    | EExpHole of hole_id * t
end

module Constraints = struct
  type consistent = Typ.t * Typ.t

  type t = consistent list

  let empty : t = []
end

module Ctx = struct
  type assumption = Identifier.t * Typ.t

  type t = assumption list

  let empty : t = []

  let lookup (ctx : t) (id : Identifier.t) : Typ.t option =
    List.fold_left
      (fun found (i, v) ->
        match found with
        | Some _ -> found
        | None -> if i = id then Some v else None)
      None ctx

  let extend (ctx : t) (e : assumption) : t =
    let id, vl = e in
    match lookup ctx id with
    | None -> e :: ctx
    | Some _ ->
        List.fold_right
          (fun (i, v) new_ctx ->
            if id = i then (i, vl) :: new_ctx else (i, v) :: new_ctx)
          ctx empty
end

let get_match_arrow_typ (t: Typ.t): (Typ.t * Constraints.t) option = 
  match t with
  | THole _ -> (
    let var_in = Typ.gen_new_type_var() in 
    let var_out = Typ.gen_new_type_var() in
    let arrow_typ = Typ.TArrow (THole(var_in),THole(var_out)) in
    Some (arrow_typ,[(t,arrow_typ)])
    )
  | TArrow (_,_) -> Some (t, [])
  | _ -> None
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
  | ENumLiteral _ -> ();
  | EAsc (exp, typ) -> (
    Typ.load_type_variable(typ);
    update_type_variable ctx exp;
  )
  | EEmptyHole _
  | EExpHole _ -> ();
;;

let rec syn (ctx: Ctx.t) (e: Exp.t): (Typ.t * Constraints.t) option =
  update_type_variable ctx e;
  match e with
  | EVar x -> (
    match Ctx.lookup ctx x with
    | None -> None
    | Some(typ) -> Some (typ, [])
  )
  | ELam (_, _) -> None
  | ELamAnn (x, ty1, e2) -> (
      match syn (Ctx.extend ctx (x, ty1)) e2 with
      | None -> None
      | Some (ty2, cons) -> Some (TArrow (ty1, ty2),cons) )
  | EBinOp (e1, OpPlus, e2) -> (
      match (ana ctx e1 Typ.TNum, ana ctx e2 Typ.TNum) with
      | (None, _) 
      | (_, None) -> None
      | (Some cons1, Some cons2) -> Some (TNum, cons1@cons2) )
  | EBinOp (e1, OpAp, e2) -> (
      match (syn ctx e1) with
      | None -> None
      | Some (typ_e1, cons1) -> (
          match get_match_arrow_typ typ_e1 with
          | None -> None
          | Some ((TArrow (ty_in, ty_out)), cons2) -> (
            match ana ctx e2 ty_in with
            | None -> None
            | Some cons3 -> Some (ty_out, cons1@cons2@cons3)
          )
          | _ -> raise Impossible
        )
    )
  | ENumLiteral _ -> Some (TNum, [])
  | EAsc (exp, typ) -> (
      match ana ctx exp typ with
      | None -> None
      | Some cons -> Some (typ, cons)
  )
  | EEmptyHole _ -> Some (THole (Typ.gen_new_type_var()),[])
  | EExpHole (_, e2) -> (
    match syn ctx e2 with
    | None -> None
    | Some (_, cons) -> Some (THole (Typ.gen_new_type_var()),cons)
  )
and ana (ctx: Ctx.t) (e: Exp.t) (ty: Typ.t): Constraints.t option =
  match e with
  | ELam (x, exp) -> (
    match get_match_arrow_typ ty with
    | None -> None
    | Some (TArrow (ty_in, ty_out), cons1) -> (
      match ana (Ctx.extend ctx (x, ty_in)) exp ty_out with
      | None -> None
      | Some cons2 -> Some (cons1@cons2)
    )
    | _ -> raise Impossible
  ) 
  | ELamAnn (x, ty_in', exp) -> (
    match get_match_arrow_typ ty with
    | None -> None
    | Some (TArrow (ty_in, ty_out), cons1) -> (
      match ana (Ctx.extend ctx (x, ty_in')) exp ty_out with
      | None -> None
      | Some cons2 -> Some (cons1@cons2@[(ty_in,ty_in')])
    )
    | _ -> raise Impossible
  ) 
  | EVar _
  | EBinOp _ 
  | ENumLiteral _
  | EAsc _
  | EEmptyHole _
  | EExpHole _ ->
    (* subsumption *)
      (match syn ctx e with
        | None -> None
        | Some (ty', cons) -> Some (cons@[(ty,ty')])
      )
;;

let rec substitute (u: Typ.t) (x: TypeInferenceVar.t) (t: Typ.t) : Typ.t =
  match t with
  | TNum -> t
  | THole v -> if v = x then u else t
  | TArrow(t1, t2) -> TArrow(substitute u x t1, substitute u x t2)
;;

let apply (subs: Typ.subs) (t: Typ.t) : Typ.t =
  List.fold_right (fun (x, u) t -> substitute u x t) subs t
;;

let rec unify (constraints: Constraints.t) : Typ.subs option =
  match constraints with
  | [] -> Some []
  | (x, y) :: xs ->
    match unify xs with
    | None -> None
    | Some subs1 -> (
      match unify_one (apply subs1 x) (apply subs1 y) with
      | None -> None
      | Some subs2 -> Some (subs1@subs2)
    )
and unify_one (t1: Typ.t) (t2: Typ.t) : Typ.subs option =
    match (t1, t2) with
    | (TNum, TNum) -> Some []
    | (THole x, z) | (z, THole x) -> Some [(x, z)]
    | (TArrow(a, b), TArrow(x, y)) -> unify [(a, x); (b, y)]
    | _ -> None
  ;;

let rec string_of_typ(typ:Typ.t) =
  match typ with
  | THole var ->  "THole["^string_of_int(var)^"]"
  | TNum -> "TNum"
  | TArrow (t1,t2) -> "TArrow:" ^ string_of_typ(t1) ^ "->"^ string_of_typ(t2)
;;

let rec print_subs(subs: Typ.subs) =
  match subs with
  | [] -> Printf.printf "%s\n" "*** Empty subs ***"
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
    | OpAp -> string_of_exp(exp1)^"__"^string_of_exp(exp2)
    | OpPlus -> string_of_exp(exp1)^" + "^string_of_exp(exp2)
  )
  | ENumLiteral num -> string_of_int(num)
  | EAsc (exp,typ) -> string_of_exp(exp)^":"^string_of_typ(typ)
  | EEmptyHole hole_id -> "(|["^string_of_int(hole_id)^"]|)"
  | EExpHole (hole_id, exp)->"(|["^string_of_int(hole_id)^"]"^string_of_exp(exp)^"|)"
;;

let print_exp(exp: Exp.t) = Printf.printf "EXP:  %s\n" (string_of_exp exp)
;;

let solve (e: Exp.t) = 
  match syn [] e with
  | None -> Printf.printf "%s" "ERROR\n: syn/ana error"
  | Some (typ,cons) -> (
    Printf.printf "exp infer typ: %s\n" (string_of_typ typ);
    match unify cons with
    | None -> Printf.printf "%s\n" "ERROR: unify error"
    | Some subs -> print_subs subs
  )

