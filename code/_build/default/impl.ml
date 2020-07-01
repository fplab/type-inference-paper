(*  *)
exception Impossible
open Syntax

let rec typ_to_subtyp (t: Typ.t): SubTyp.t = 
  match t with
  | THole var -> Primitive (STHole var)
  | TNum -> Primitive STNum
  | TArrow(t1, t2) -> Primitive (STArrow(typ_to_subtyp t1, typ_to_subtyp t2))
;;

let rec subtyp_to_typ (t: SubTyp.t): Typ.t = 
  match t with 
  | HoleSubs (_, typ)
  | Primitive typ -> (
    match typ with
    | STHole var -> THole var
    | STNum -> TNum
    | STArrow (t1, t2) -> TArrow(subtyp_to_typ t1, subtyp_to_typ t2)
  )
;;
let get_match_arrow_typ (t: Typ.t): (Typ.t * Constraints.t) option = 
  match t with
  | THole _ -> (
    let var_in = Typ.gen_new_type_var() in 
    let var_out = Typ.gen_new_type_var() in
    let arrow_typ = Typ.TArrow (THole(var_in),THole(var_out)) in
    Some (arrow_typ,[(typ_to_subtyp t, typ_to_subtyp arrow_typ)])
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
      | Some cons2 -> Some (cons1@cons2@[(typ_to_subtyp ty_in,typ_to_subtyp ty_in')])
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
        | Some (ty', cons) -> Some (cons@[(typ_to_subtyp ty,typ_to_subtyp ty')])
      )
;;

let rec substitute (u: Typ.unify_result) (x: TypeInferenceVar.t) (t: SubTyp.t) : SubTyp.t =
  match u with 
  | UnSolved _ -> raise Impossible
  | Solved u' -> (
    match (typ_to_subtyp u',t) with 
    | (Primitive typ_u, HoleSubs(typvar_set_t, typ_t)) -> (
      match typ_t with
      | STNum -> t
      | STHole v -> 
        if v = x then 
          (HoleSubs(TypeInfVarSet.add v typvar_set_t, typ_u)) 
        else t
      | STArrow(t1, t2) -> 
        HoleSubs(typvar_set_t, STArrow(substitute u x t1, substitute u x t2))
    )
    | (Primitive typ_u, Primitive typ_t) -> (
      match typ_t with
      | STNum -> t
      | STHole v -> if v = x then (
        let typvarset = TypeInfVarSet.add v TypeInfVarSet.empty
        in HoleSubs(typvarset, typ_u)
      ) else t
      | STArrow(t1, t2) -> 
        Primitive (STArrow(substitute u x t1, substitute u x t2))
    )
    | _ -> raise Impossible
  )
;;

let apply (unify_results: Typ.unify_results) (t: SubTyp.t) : SubTyp.t =
  List.fold_right (fun (x, u) t -> substitute u x t) unify_results t
;;

type result =
  | Success of Typ.unify_results
  | Failure of Typ.unify_results

let rec to_solution_ls (typvar_set: TypeInferenceVar.t list) (typ_ls: Typ.t list): Typ.unify_results = 
  match typvar_set with
  | [] -> []
  | hd::tl -> [(hd, Typ.UnSolved typ_ls)] @ (to_solution_ls tl typ_ls)
;;

let rec unify (constraints: Constraints.t) : result =
  match constraints with
  | [] -> Success []
  | (x, y) :: xs ->
    match unify xs with
    | Failure unify_results -> Failure unify_results
    | Success unify_results1 -> (
      match unify_one (apply unify_results1 x) (apply unify_results1 y) with
      | Failure unify_results2 -> Failure unify_results2
      | Success unify_results2 -> Success (unify_results1@unify_results2)
    )
and unify_one (t1: SubTyp.t) (t2: SubTyp.t) : result =
    match (t1, t2) with
    | (Primitive typ_1, Primitive typ_2) -> (
      match (typ_1, typ_2) with
      | (STNum, STNum) -> Success []
      | (STHole x, _) -> Success [(x, Solved (subtyp_to_typ t2))]
      | (_, STHole x) -> Success [(x, Solved (subtyp_to_typ t1))]
      | (STArrow(a, b), STArrow(x, y)) -> unify [(a, x); (b, y)]
      | _ -> Failure []
    )
    | (Primitive typ_2, HoleSubs(typvar_set, typ_1))
    | (HoleSubs(typvar_set, typ_1), Primitive typ_2) -> (
      match (typ_1, typ_2) with
      | (STNum, STNum) -> Success []
      | (STHole x, _) -> Success [(x, Solved (subtyp_to_typ t2))]
      | (_, STHole x) -> Success [(x, Solved (subtyp_to_typ t1))]
      | (STArrow(a, b), STArrow(x, y)) -> unify [(a, x); (b, y)]
      | _ -> (
        let typ_ls = [(subtyp_to_typ t1); (subtyp_to_typ t2)] in
        let typvar_ls = TypeInfVarSet.elements typvar_set in
        Failure (to_solution_ls typvar_ls typ_ls)
      )
    )
    | (HoleSubs(typvar_set_1, typ_1), HoleSubs(typvar_set_2, typ_2)) -> (
      match (typ_1, typ_2) with
      | (STNum, STNum) -> Success []
      | (STHole x, _) -> Success [(x, Solved (subtyp_to_typ t2))]
      | (_, STHole x) -> Success [(x, Solved (subtyp_to_typ t1))]
      | (STArrow(a, b), STArrow(x, y)) -> unify [(a, x); (b, y)]
      | _ -> ( 
        let typ_ls = [(subtyp_to_typ t1); (subtyp_to_typ t2)] in
        let typvar_ls = TypeInfVarSet.elements (TypeInfVarSet.inter typvar_set_1 typvar_set_2) in
        Failure (to_solution_ls typvar_ls typ_ls)
      )
    )
  ;;
