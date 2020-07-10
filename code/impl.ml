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
      | Some cons2 -> Some (cons1@cons2@[(ty_in, ty_in')])
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
        | Some (ty', cons) -> Some (cons@[(ty, ty')])
      )
;;


let rec is_in_dom (v: TypeInferenceVar.t) (t: Typ.t) : bool =
  match t with
    | THole v' -> v' == v 
    | TNum -> false
    | TArrow (t1, t2) -> (is_in_dom v t1) || (is_in_dom v t2) 
;;

let rec substitute (u: Typ.unify_result) (x: TypeInferenceVar.t) (t: Typ.t) : Typ.t =
  match u with
  | Solved u_typ ->(
    match t with
    | TNum -> t
    | THole v -> if v = x then u_typ else t
    | TArrow(t1, t2) -> TArrow(substitute u x t1, substitute u x t2)
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

let rec unify (constraints: Constraints.t)
  : bool*Typ.unify_results =
  match constraints with
  | [] -> (true, [])
  | (x, y) :: xs ->
    (* generate substitutions of the rest of the list *)
    let (suc2,r2) = unify xs in
    (* resolve the LHS and RHS of the constraints from the previous substitutions *)
    let (sol,r1) = unify_one x y r2 in 
    match sol with
    | Solved _-> (suc2, merge_results r1 r2)
    | UnSolved _-> (false, merge_results r1 r2)
and unify_one (t1: Typ.t) (t2: Typ.t) (partial_results: Typ.unify_results)
  : Typ.unify_result * Typ.unify_results =
    match ((t1, t2)) with
    | (TNum, TNum) ->(Solved TNum, [])
    | (TArrow (ta1, ta2), TArrow (ta3, ta4)) -> (
      let ta1' = apply partial_results ta1 in
      let ta2' = apply partial_results ta2 in
      let ta3' = apply partial_results ta3 in
      let ta4' = apply partial_results ta4 in
      let (suc, results) = unify [(ta1',ta3');(ta2',ta4')] in
      let result' = merge_results results partial_results in
          if suc then (
            let typ' = apply result' t1 in
            (Solved typ', results)
          ) else (
            let typ_1 = apply result' t1 in
            let typ_2 = apply result' t2 in
            (UnSolved ([typ_1; typ_2]), results)
          )
    )
    | (THole v, t) | (t, THole v)-> 
      let subs_v = apply partial_results (THole v) in
      let typ = apply partial_results t in
        if (is_in_dom v typ) then (Solved (THole v), [(v, UnSolved [typ; THole v])])
        else (
          match subs_v with
          | THole _ -> (Solved typ, [(v, Solved typ)])
          | _ -> (
            match (unify_one subs_v typ partial_results) with
            | (Solved typ', result) -> (Solved typ', add_result (v, Typ.Solved typ') result)
            | (UnSolved typ_ls, result) -> (Solved (THole v), add_result (v, Typ.UnSolved typ_ls) result)
          )
        )
    | (typ_1, typ_2) -> 
      let typ_1' = apply partial_results typ_1 in
      let typ_2' = apply partial_results typ_2 in
      (UnSolved [typ_1'; typ_2'], [])
  ;;
