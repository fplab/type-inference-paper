(*  *)
exception Impossible
open Syntax


let get_match_arrow_typ (t: Typ.t): (Typ.t * Constraints.t) option = 
  match t with
  | THole _ -> (
    let var_in = Typ.gen_new_type_var() in 
    let var_out = Typ.gen_new_type_var() in
    let arrow_typ = Typ.TArrow (THole(var_in),THole(var_out)) in
    Some (arrow_typ,[(t, arrow_typ)])
    )
  | TArrow (_,_) -> Some (t, [])
  | _ -> None
;;

let rec consistent (t1: Typ.t) (t2: Typ.t) : bool = 
  match (t1,t2) with
  | (THole _ , _)
  | (_ , THole _)
  | (TNum, TNum)
  | (TBool, TBool) -> true
  | (TArrow (t1, t2), TArrow (t3, t4))
  | (TProd (t1, t2), TProd (t3, t4))
  | (TSum (t1, t2), TSum (t3, t4)) -> (consistent t1 t3) && (consistent t2 t4)
  | _ -> false
;;

let rec syn (ctx: Ctx.t) (e: Exp.t): (Typ.t * Constraints.t) option =
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
  | EBoolLiteral _ -> Some (TBool, [])
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
  | EIf (e1, e2, e3) -> (
    match ana ctx e1 TBool with
    | None -> None
    | Some cons1 -> (
      match syn ctx e2 with
      | None -> None
      | Some (typ2, cons2) -> (
        match syn ctx e3 with
        | None -> None
        | Some (typ3, cons3) -> Some (typ2, cons1 @ cons2 @ cons3 @[(typ2, typ3)])
      )
    )
  )
  | ELet (x, None, e1, e2) -> (
    match syn ctx e1 with
    | None -> None
    | Some (typ1, cons1) -> (
      match syn (Ctx.extend ctx (x, typ1)) e2 with
      | None -> None
      | Some (typ2, cons2) -> Some (typ2, cons1 @ cons2)
    )
  )
  | ELet (x, Some typ, e1, e2) -> (
    match ana ctx e1 typ with
    | None -> None
    | Some cons1 -> (
      match syn (Ctx.extend ctx (x, typ)) e2 with
      | None -> None
      | Some (typ2, cons2) -> Some (typ2, cons1 @ cons2)
    )
  )
  | EPair (e1, e2) -> (
    match syn ctx e1 with
    | None -> None
    | Some (typ1, cons1) -> (
      match syn ctx e2 with
      | None -> None
      | Some (typ2, cons2) -> Some (TProd(typ1, typ2), cons1 @ cons2)
    )
  )
  | ELetPair (x, y, e1, e2) -> (
    match syn ctx e1 with
    | Some(TProd(typ1, typ2), cons1) -> (
      match syn (Ctx.extend (Ctx.extend ctx (x, typ1)) (y, typ2)) e2 with
      | None -> None
      | Some (typ, cons2) -> Some (typ, cons1 @ cons2)
    )
    | _ -> None
  )
  | EPrjL e -> (
    match syn ctx e with
    | Some(TProd(typ1, _), cons) ->  Some (typ1, cons)
    | _ -> None
  )
  | EPrjR e -> (
    match syn ctx e with
    | Some(TProd(_, typ2), cons) ->  Some (typ2, cons)
    | _ -> None
  )
  | ECase (e, x, e1, y, e2) -> (
    match syn ctx e with
    | Some(TSum(typ1, typ2), cons1) ->  (
      match syn (Ctx.extend ctx (x, typ1)) e1 with
      | None -> None
      | Some (typ_x, cons2) -> (
        match syn (Ctx.extend ctx (y, typ2)) e2 with
        | None -> None
        | Some (typ_y, cons3) -> Some(typ_x, cons1@cons2@cons3@[(typ_x, typ_y)])
      )
    )
    | _ -> None
  )
  | EInjL _
  | EInjR _ -> None
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
      | Some cons2 -> Some (cons1@cons2@[(ty_in, ty_in')])
    )
    | _ -> raise Impossible
  ) 
  | EIf (e1, e2, e3) -> (
    match ana ctx e1 TBool with
    | None -> None
    | Some cons1 -> (
      match ana ctx e2 ty with
      | None -> None
      | Some cons2 -> (
        match ana ctx e3 ty with
        | None -> None
        | Some cons3 -> Some (cons1 @ cons2 @ cons3)
      )
    )
  )
  | ELet (x, None, e1, e2) -> (
    match syn ctx e1 with
    | None -> None
    | Some (typ1, cons1) -> (
      match ana (Ctx.extend ctx (x, typ1)) e2 ty with
      | None -> None
      | Some cons2 -> Some (cons1 @ cons2)
    )
  )
  | ELet (x, Some typ, e1, e2) -> (
    match ana ctx e1 typ with
    | None -> None
    | Some cons1 -> (
      match ana (Ctx.extend ctx (x, typ)) e2 ty with
      | None -> None
      | Some cons2 -> Some (cons1 @ cons2)
    )
  )
  | EPair (e1, e2) -> (
    match ty with
    | TProd(typ1, typ2) ->(
      match ana ctx e1 typ1 with
      | None -> None
      | Some cons1 -> (
        match ana ctx e2 typ2 with
        | None -> None
        | Some cons2 -> Some (cons1 @ cons2)
      )
    )
    | _ -> None
  )
  | ELetPair (x, y, e1, e2) -> (
    match syn ctx e1 with
    | Some(TProd(typ1, typ2), cons1) -> (
      match ana (Ctx.extend (Ctx.extend ctx (x, typ1)) (y, typ2)) e2 ty with
      | None -> None
      | Some cons2 -> Some (cons1 @ cons2)
    )
    | _ -> None
  )
  | EInjL e -> (
    match ty with
    | TSum (typ1, _) -> (
      ana ctx e typ1
    )
    | _ -> None
  )
  | EInjR e -> (
    match ty with
    | TSum (_, typ2) -> (
      ana ctx e typ2
    )
    | _ -> None
  )
  | ECase (e, x, e1, y, e2) -> (
    match syn ctx e with
    | Some(TSum(typ1, typ2), cons1) ->  (
      match ana (Ctx.extend ctx (x, typ1)) e1 ty with
      | None -> None
      | Some (cons2) -> (
        match ana (Ctx.extend ctx (y, typ2)) e2 ty with
        | None -> None
        | Some (cons3) -> Some(cons1@cons2@cons3)
      )
    )
    | _ -> None
  )
  | EVar _
  | EBinOp _ 
  | ENumLiteral _
  | EBoolLiteral _
  | EAsc _
  | EEmptyHole _
  | EExpHole _ 
  | EPrjL _
  | EPrjR _ ->
    (* subsumption *)
      (match syn ctx e with
        | None -> None
        | Some (ty', cons) -> 
        if (consistent ty' ty) then Some (cons@[(ty, ty')])
        else None
      )
;;


let rec is_in_dom (v: TypeInferenceVar.t) (t: Typ.t) : bool =
  match t with
    | THole v' -> v' == v 
    | TNum 
    | TBool -> false
    | TArrow (t1, t2) 
    | TProd (t1, t2)
    | TSum (t1, t2) -> (is_in_dom v t1) || (is_in_dom v t2) 
;;

let rec substitute (u: Typ.unify_result) (x: TypeInferenceVar.t) (t: Typ.t) : Typ.t =
  match u with
  | Solved u_typ ->(
    match t with
    | TNum 
    | TBool -> t
    | THole v -> if v = x then u_typ else t
    | TArrow(t1, t2) -> TArrow(substitute u x t1, substitute u x t2)
    | TProd (t1, t2) -> TProd(substitute u x t1, substitute u x t2)
    | TSum (t1, t2) -> TSum(substitute u x t1, substitute u x t2)
  )
  | UnSolved _ -> t
;;

let apply (subs: Typ.unify_results) (t: Typ.t) : Typ.t =
  List.fold_right (fun (x, u) t -> substitute u x t) subs t
;;


let rec add_result (new_result: TypeInferenceVar.t*Typ.unify_result) (old_results: Typ.unify_results): Typ.unify_results =
  match old_results with
  | [] -> new_result::[]
  | (hd_var, hd_typ)::tl -> (
    let (new_var, new_typ) = new_result in
    if hd_var == new_var then (
      match (hd_typ, new_typ) with
      | (Solved _, Solved _)
      | (Solved _, UnSolved _) -> (hd_var, new_typ)::tl
      | (UnSolved ls_old, UnSolved ls_new) -> (hd_var, UnSolved (Typ.merge_typ_lst ls_old ls_new))::tl
      | (UnSolved ls_old, Solved typ) -> (hd_var, UnSolved (Typ.add_to_typ_lst typ ls_old))::tl
    )
    else (hd_var, hd_typ)::(add_result new_result tl)
  )
;;

let rec merge_results (new_results: Typ.unify_results) (old_results: Typ.unify_results): Typ.unify_results =
  match new_results with
  | [] -> old_results
  | hd::tl -> merge_results tl (add_result hd old_results)
;;

(*     hole3 
    hole1 num -> hole3
    hole2 num -> bool // [num,bool] // [num -> bool, num -> float] //hole3 -> bool
    hole1 ~ hole2
    1 [num->hole3, hole2]
    --> hole1 ~ [num->num, hole2]     [num->hole3,hole2]
    --> hole1 ~ [num, hole2], hole2 ~ [bool] *)


    hole 0 : num
                  hole 0 = solved [num]
    hole 1 ~ hole 0
                  hole 0 = solved [num]
                  hole 1 = solved [num]
    hole2 ~ hole 1
    hole 0 ~ bool
                  hole 0 = Unsolved [num, bool]
                  hole 1 = solved [hole 0]
    hole3 ~ hole 0 
                hole 3 = solved [hole 0]
    hole 2 ~ hole 1
                  hole 0 = Unsolved [num, bool]
                  hole 1 = solved [hole 0]
                  hole 2 = solved [hole 1]
    hole 2 ~ bool 
                  hole 0 = Unsolved [num, bool]
                  hole 1 = solved [hole 0]
                  hole 2 = solved [hole 1]

    hole 0 : num
    hole 1 ~ hole 0
    hole 2 : num -> hole0       /num
    hole 3 : num -> bool
    hole 2 ~ hole 3 
                hole 0 : unsolved [num, bool]
                hole 2 : [num -> hole 0]
                hole 3 : solved [num -> bool]
    hole 4: num -> hole 2
    hole 4 ~ hole 1

let rec unify (constraints: Constraints.t)
  :  bool*Typ.unify_results =
  match constraints with
  | [] -> (true, [])
  | (x, y) :: xs ->
    (* generate substitutions of the rest of the list *)
    let (suc2, r2) = unify xs in
    (* resolve the LHS and RHS of the constraints from the previous substitutions *)
    let (suc1, r1) = unify_one x y r2 in 
    (suc2 && suc1, merge_results r1 r2)
and unify_one (t1: Typ.t) (t2: Typ.t) (partial_results: Typ.unify_results)
  : bool * Typ.unify_results  =
    match ((t1, t2)) with
    | (TNum, TNum) ->  (true, [])
    | (TArrow (ty1, ty2), TArrow (ty3, ty4)) 
    | (TProd (ty1, ty2), TProd (ty3,ty4)) 
    | (TSum (ty1, ty2), TSum (ty3,ty4))-> (
      unify [(ty1,ty3);(ty2,ty4)]
    )
    | (THole v, t) | (t, THole v) -> 
      let subs_v = apply partial_results (THole v) in
      let typ = apply partial_results t in
        (* detect recursive case *)
        if (is_in_dom v typ) then (false, [(v, UnSolved [typ; THole v])])
        else (
          match subs_v with
          | THole _ -> (true, [(v, Solved typ)])
          | _ -> (
            match (unify_one subs_v typ partial_results) with
            | (true, result) ->  (true, add_result (v, Typ.Solved typ) result)
            | (false, result) -> (false, add_result (v, Typ.UnSolved([//subs_v; t //typ])) result)
          )
        )
    | (_, _) -> 
      (false, [])
  ;;

(* let  generate_sol (constraints: Constraints.t): Typ.unify_results =
  let (_, results) = unify constraints in
  let rec subs_results (results: Typ.unify_results): Typ.unify_results = (
    match results with
    | [] -> []
    | (hd_var, Solved hd_typ)::tl -> (
      (hd_var, Solved (apply results hd_typ))::(subs_results tl)
    )
    | (hd_var, UnSolved hd_typ_ls)::tl -> (
      (hd_var, UnSolved (List.map (apply results) hd_typ_ls))::(subs_results tl)
    )
  ) in (subs_results results)
;;
 *)
