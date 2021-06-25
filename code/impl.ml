(*  *)
exception Impossible
exception InvalidUse of string
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

let get_match_prod_typ (t: Typ.t): (Typ.t * Constraints.t) option = 
  match t with
  | THole _ -> (
    let var_in = Typ.gen_new_type_var() in 
    let var_out = Typ.gen_new_type_var() in
    let prod_typ = Typ.TProd (THole(var_in),THole(var_out)) in
    Some (prod_typ,[(t, prod_typ)])
    )
  | TProd (_,_) -> Some (t, [])
  | _ -> None
;;

let get_match_sum_typ (t: Typ.t): (Typ.t * Constraints.t) option = 
  match t with
  | THole _ -> (
    let var_in = Typ.gen_new_type_var() in 
    let var_out = Typ.gen_new_type_var() in
    let sum_typ = Typ.TSum (THole(var_in),THole(var_out)) in
    Some (sum_typ,[(t, sum_typ)])
    )
  | TSum (_,_) -> Some (t, [])
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

(* Appends the item to the list only if the item is inconsistent with any item in the list *)
let cat_if_unequal_for_all (target_list: Typ.t list) (item: Typ.t)
    : Typ.t list =
    let is_eq (elt: Typ.t): bool = (elt = item) in
    if (List.exists is_eq target_list) then (
        target_list
    ) else (
        item::target_list
    )
;;

(* Combines a pair of lists by adding elements from l2 only if they are inconsistent with those currently added/in l1 *)
let smallest_unequal_pair (l1: Typ.t list) (l2: Typ.t list)
    : Typ.t list =
    List.fold_left cat_if_unequal_for_all l1 l2
;;

(* A generalized version of smallest_inconsistent_pair that simply concatenates the tail of a list set to be used in pair *)
let smallest_unequal_set (list_set: (Typ.t list) list)
    : Typ.t list =
    match list_set with
    | [] -> []
    | hd::tl -> 
        let tl = List.fold_left (@) [] tl in
        smallest_unequal_pair hd tl
;;

let rec contains_hole (typ: Typ.t): bool =
  match typ with
  | TNum
  | TBool -> false
  | THole _ -> true
  | TArrow(ty1, ty2)
  | TProd(ty1, ty2)
  | TSum(ty1, ty2) -> (contains_hole ty1) || (contains_hole ty2)
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

(*
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

(*Does fold right apply last of list of subs first or first last *)
let apply (subs: Typ.unify_results) (t: Typ.t) : Typ.t =
  List.fold_right (fun (x, u) t -> substitute u x t) subs t
;;
*)

(*
Zoe's old ver------------
if hd_var == new_var then (
      match (hd_res, new_res) with
      | (Solved _, Solved _)
      | (Solved _, UnSolved _) -> (hd_var, new_res)::tl
      (*if two unsolved results are generated, the variable is associated with the conflicts of both; merge the type lists of both for its type *)
      | (UnSolved ls_old, UnSolved ls_new) -> (hd_var, UnSolved (Typ.merge_typ_lst ls_old ls_new))::tl
      (*if it was unsolved previously and found to be solved in another instance, it must still be unsolved. add the type solved to the list
      of conflicting types in the variable's list of unsolved*)
      | (UnSolved ls_old, Solved typ) -> (hd_var, UnSolved (Typ.add_to_typ_lst typ ls_old))::tl
    )
    else (hd_var, hd_res)::(add_result new_result tl)*)
(*intended use: during unify to add results and manage inconsistencies; thus, no value should be solved of a hole
or some derived sided hole. raises InvalidUse is such an occurrence is found*)
let rec add_unify_result (new_result: TypeInferenceVar.t*Typ.unify_result) (old_results: Typ.unify_results)
  : Typ.unify_results =
  match old_results with
  | [] -> new_result::[]
  | (hd_var, hd_res)::tl -> (
    let (new_var, new_res) = new_result in
    if hd_var == new_var then (
      match (hd_res, new_res) with
      | ((Solved old_typ), (Solved new_typ)) -> (
        match (old_typ, new_typ) with
        | (THole _, _)
        | (_, THole _) -> raise (InvalidUse "a variable was solved as a hole in add_result")
        | _ -> (
          if (consistent old_typ new_typ) then (
            (hd_var, hd_res)::tl
          ) else (
            (hd_var, Typ.UnSolved [old_typ; new_typ])::tl
          )
        )
      )
      | ((Ambiguous (ty_op, holes)), (Solved basic_ty))
      | ((Solved basic_ty), (Ambiguous (ty_op, holes))) -> (
        match (basic_ty) with
        | (THole _) -> raise (InvalidUse "a variable was solved as a hole in add_result")
        | _ -> (
          match (ty_op) with
          | (Some ty) -> (
            match ty with
            | THole _ -> raise (InvalidUse "a variable was ambiguously solved as a hole in add_result")
            | _ -> (
              if (consistent ty basic_ty) then (
                (hd_var, Typ.Ambiguous ((Some ty), holes))::tl
              )
              else (
                (hd_var, Typ.UnSolved ([ty; basic_ty] @ holes))::tl
              )
            )
          )
          | None -> (
            if (List.for_all (consistent basic_ty) holes) then (
              (hd_var, Typ.Ambiguous ((Some basic_ty), holes))::tl
            ) else (
              (hd_var, Typ.UnSolved [basic_ty; holes])::tl
            )
          )
        )
      )
      | ((Ambiguous (ty_op1, holes1)), (Ambiguous (ty_op2, holes2))) -> (
        match (ty_op1, ty_op2) with
        | ((Some ty1), (Some ty2)) -> (
          match (ty1, ty2) with
          | ((THole _), _)
          | (_, (THole _)) -> raise (InvalidUse "a variable was ambiguously solved as a hole in add_result")
          | _ -> (
            if (consistent ty1 ty2) then (
              (hd_var, Typ.Ambiguous ((Some ty1), (smallest_unequal_pair holes1 holes2)))::tl
            ) else (
              (hd_var, Typ.UnSolved (smallest_unequal_set [holes1; holes2; ty1::ty2::[]]))::tl
            )
          )
        )
        | (None, (Some ty)) -> (
          match ty with
          | THole _ -> raise (InvalidUse "a variable was ambiguously solved as a hole in add_result")
          | _ -> (
            if (List.for_all (consistent ty) holes1) then (
              (hd_var, Typ.Ambiguous ((Some ty), (smallest_unequal_pair holes1 holes2)))::tl
            ) else (
              (hd_var, Typ.UnSolved (ty::(smallest_unequal_pair holes1 holes2)))::tl
            )
          )
        )
        | ((Some ty), None) -> (
          match ty with
          | THole _ -> raise (InvalidUse "a variable was ambiguously solved as a hole in add_result")
          | _ -> (
            if (List.for_all (consistent ty) holes2) then (
              (hd_var, Typ.Ambiguous ((Some ty), (smallest_unequal_pair holes1 holes2)))::tl
            ) else (
              (hd_var, Typ.UnSolved (ty::(smallest_unequal_pair holes1 holes2)))::tl
            )
          )
        )
        | (None, None) -> (
          (hd_var, Typ.Ambiguous (None, (smallest_unequal_pair holes1 holes2)))::tl
        )
      )
      | ((UnSolved ls), (Ambiguous (ty_op, holes)))
      | ((Ambiguous (ty_op, holes)), (UnSolved ls)) -> (
        match ty_op with
        | (Some ty) -> (
          match ty with
          | THole _ -> raise (InvalidUse "a variable was ambiguously solved as a hole in add_result")
          | _ -> (hd_var, Typ.UnSolved (smallest_unequal_pair (ty::holes) ls))::tl
        )
        | None -> (hd_var, Typ.UnSolved (smallest_unequal_pair holes ls))::tl
      )
      | ((UnSolved ls), (Solved basic_ty))
      | ((Solved basic_ty), (UnSolved ls)) -> (
        match basic_ty with
        | THole _ -> raise (InvalidUse "a variable was solved as a hole in add_result")
        | _ -> (hd_var, Typ.UnSolved (basic_ty::ls))::tl
      )
      | ((UnSolved ls1), (UnSolved ls2)) -> (
        (hd_var, Typ.UnSolved (smallest_unequal_pair ls1 ls2))::tl
      )
    )
    else (hd_var, hd_res)::(add_unify_result new_result tl)
  )
;;

let rec add_rec_unify_result (new_result: Typ.t*Typ.rec_unify_result) (old_results: Typ.rec_unify_results)
  : Typ.rec_unify_results =
  if hd_var == new_var then (
      match (hd_res, new_res) with
      | (Solved _, Solved _)
      | (Solved _, UnSolved _) -> (hd_var, new_res)::tl
      (*if two unsolved results are generated, the variable is associated with the conflicts of both; merge the type lists of both for its type *)
      | (UnSolved ls_old, UnSolved ls_new) -> (hd_var, UnSolved (Typ.merge_typ_lst ls_old ls_new))::tl
      (*if it was unsolved previously and found to be solved in another instance, it must still be unsolved. add the type solved to the list
      of conflicting types in the variable's list of unsolved*)
      | (UnSolved ls_old, Solved typ) -> (hd_var, UnSolved (Typ.add_to_typ_lst typ ls_old))::tl
    )
    else (hd_var, hd_res)::(add_result new_result tl)
;;

let rec merge_unify_results (new_results: Typ.unify_results) (old_results: Typ.unify_results): Typ.unify_results =
  match new_results with
  | [] -> old_results
  | hd::tl -> merge_results tl (add_result hd old_results)
;;

(*
(*Requires var be a THole type *)
let rec expand_until_matchable (hvar: Typ.t) (to_match: Typ.t)
  : Constraints.t = 
  match to_match with
  | TNum -> [(hvar, Typ.TNum);]
  | TBool -> [(hvar, Typ.TBool);]
  | THole id -> [(hvar, Typ.THole id);]
  | TArrow (ty1, ty2) -> (
    let (ty_in, ty_out, ctrs) = 
      match get_match_arrow_typ (hvar) with
      | Some (TArrow (ma1, ma2), ctrs_out) -> (ma1, ma2, ctrs_out)
      | _ -> raise Impossible
    in
    List.rev_append (ctrs @ (expand_until_matchable ty_in ty1)) (expand_until_matchable ty_out ty2)
  )
  | TProd (ty1, ty2) -> (
    let (ty_in, ty_out, ctrs) = 
      match get_match_prod_typ (hvar) with
      | Some (TProd (ma1, ma2), ctrs_out) -> (ma1, ma2, ctrs_out)
      | _ -> raise Impossible
    in
    List.rev_append (ctrs @ (expand_until_matchable ty_in ty1)) (expand_until_matchable ty_out ty2)
  )
  | TSum (ty1, ty2) -> (
    let (ty_in, ty_out, ctrs) = 
      match get_match_sum_typ (hvar) with
      | Some (TSum (ma1, ma2), ctrs_out) -> (ma1, ma2, ctrs_out)
      | _ -> raise Impossible
    in
    List.rev_append (ctrs @ (expand_until_matchable ty_in ty1)) (expand_until_matchable ty_out ty2)
  )
;;
*)

(*
let rec solve_rec_as_hole (t_rec: Typ.t) (t_hole: Typ.utyp): (Typ.unify_results) =
  match t_rec with
  | TNum
  | TBool -> []
  | THole id -> (id, Ambiguous (None, t_hole::[]))::[]
  | TArrow (ty1, ty2) -> (
    List.rev_append 
      (solve_rec_as_hole
        (ty1) 
        (Typ.SidedHole (t_hole, (Arrow (L))))
      )
      (solve_rec_as_hole 
        (ty2) 
        (Typ.SidedHole (t_hole, (Arrow (R))))
      )
  )
  | TProd (ty1, ty2) -> (
    List.rev_append 
      (solve_rec_as_hole
        (ty1) 
        (Typ.SidedHole (t_hole, (Prod (L))))
      )
      (solve_rec_as_hole 
        (ty2) 
        (Typ.SidedHole (t_hole, (Prod (R))))
      )
  )
  | TSum (ty1, ty2) -> (
    List.rev_append 
      (solve_rec_as_hole
        (ty1) 
        (Typ.SidedHole (t_hole, (Sum (L))))
      )
      (solve_rec_as_hole 
        (ty2) 
        (Typ.SidedHole (t_hole, (Sum (R))))
      )
  )
;;*)

let rec unify (constraints: Constraints.t)
  :  bool*Typ.unify_results*Typ.rec_unify_results =
  match constraints with
  | [] -> (true, [], [])
  | (x, y) :: xs ->
    (* generate substitutions of the rest of the list *)
    let (suc2, u_res2, r_rec2) = unify xs in
    (* resolve the LHS and RHS of the constraints from the previous substitutions *)
    let (suc1, u_res1, r_res1) = unify_one x y in 
    (suc2 && suc1, 
    merge_unify_results u_res1 u_res2, 
    merge_rec_unify_results r_res1 r_res2)
and unify_one (t1: Typ.t) (t2: Typ.t)
  : bool * Typ.unify_results * Typ.rec_unify_results  =
    match ((t1, t2)) with
    | (TNum, TNum) 
    | (TBool, TBool) ->  (true, [], [])
    | (TArrow (ty1, ty2), TArrow (ty3, ty4)) 
    | (TProd (ty1, ty2), TProd (ty3,ty4)) 
    | (TSum (ty1, ty2), TSum (ty3,ty4))-> (
      unify [(ty1,ty3);(ty2,ty4)]
    )
    | (THole v, t) | (t, THole v) ->
      (*occurs check *)
      if (is_in_dom v t) then (
        (false, [(v, UnSolved [t; (THole v)])], [])
      ) else (
        match t with
        | THole t_id -> (
          (*to ensure dependencies are captures, add both as solved of each other *)
          (true,
          [
            (v, Typ.Ambiguous (None, t::[])); 
            (t_id, Typ.Ambiguous (None, (THole v)::[]))
          ],
          []
          )
        )
        | _ -> (
          (*if a recursive structure containing holes *)
          if (contains_hole t) then (
            (true,
            [(v, Typ.Ambiguous (None, t::[]))],
            [(t, Typ.Ambiguous (None, (THole v)::[]))])
          ) else (
            (*otherwise, the hole is simply solved of the base type *)
            (true, [(v, Typ.Solved t)], [])
          )
        )
      )
    | (_, _) -> 
      (false, [], [])
    (*
    | (THole v, t) | (t, THole v) -> 
      (*the reason we can't just sub in the value
      constrained to is it enforces the constraint for all
        if it were not unifiable, then the whole thing would fail
        we want partial resultsS *)
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
            | (false, result) -> (false, add_result (v, Typ.UnSolved([subs_v; typ])) result)
          )
        )
    *)
  ;;
