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

(*greatest lower bound; requires both types be consistent *)
let rec glb (t1: Typ.t) (t2: Typ.t): Typ.t =
  match (t1, t2) with
  | (THole _, THole _) -> t1
  | (_, THole var)
  | (THole var, _) -> THole var
  | (TArrow(typ1, typ2), TArrow(typ1', typ2')) -> TArrow ((glb typ1 typ1'), (glb typ2 typ2'))
  | (TProd(typ1, typ2), TProd(typ1', typ2')) -> TProd ((glb typ1 typ1'), (glb typ2 typ2'))
  | (TSum(typ1, typ2), TSum(typ1', typ2')) -> TSum ((glb typ1 typ1'), (glb typ2 typ2'))
  | _ -> t1
;;

(* Appends the item to the list only if the item is unequal with all items in the list *)
let cat_if_unequal_for_all (target_list: Typ.t list) (item: Typ.t)
    : Typ.t list =
    let is_eq (elt: Typ.t): bool = (elt = item) in
    if (List.exists is_eq target_list) then (
        target_list
    ) else (
        item::target_list
    )
;;

(* Combines a pair of lists by adding elements from l2 only if they are unequal with those currently added/in l1 *)
let smallest_unequal_pair (l1: Typ.t list) (l2: Typ.t list)
    : Typ.t list =
    List.fold_left cat_if_unequal_for_all l1 l2
;;

(* A generalized version of above that simply concatenates the tail of a list set to be used in pair *)
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
        | Some (typ3, cons3) ->
          (*will need to make helper to order literals after holes and use here *)
          if Typ.consistent typ2 typ3 then Some (typ2, cons1 @ cons2 @ cons3 @ [(typ2, typ3)])
          else None
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
    | Some(typ_out, cons1) -> (
      match (get_match_prod_typ typ_out) with
      | Some(TProd(typ1, typ2), cons2) -> (
        match syn (Ctx.extend (Ctx.extend ctx (x, typ1)) (y, typ2)) e2 with
        | None -> None
        | Some (typ, cons3) -> Some (typ, cons1 @ cons2 @ cons3)
      )
      | _ -> None
    )
    | _ -> None
  )
  | EPrjL e -> (
    match syn ctx e with
    | Some(typ_out, cons1) -> (
      match (get_match_prod_typ typ_out) with
      | Some(TProd(typ1, _), cons2) -> Some (typ1, cons1 @ cons2)
      | _ -> None
    )
    | _ -> None
  )
  | EPrjR e -> (
    match syn ctx e with
    | Some(typ_out, cons1) -> (
      match (get_match_prod_typ typ_out) with
      | Some(TProd(_, typ2), cons2) -> Some (typ2, cons1 @ cons2)
      | _ -> None
    )
    | _ -> None
  )
  | ECase (e, x, e1, y, e2) -> (
    match syn ctx e with
    | Some(typ_out, cons1) -> (
      match (get_match_sum_typ typ_out) with
      | Some(TSum(typ1, typ2), cons2) -> (
        match syn (Ctx.extend ctx (x, typ1)) e1 with
        | None -> None
        | Some (typ_x, cons3) -> (
          match syn (Ctx.extend ctx (y, typ2)) e2 with
          | None -> None
          | Some (typ_y, cons4) -> (
            if Typ.consistent typ_x typ_y then Some((glb typ_x typ_y), cons1@cons2@cons3@cons4@[(typ_x, typ_y)])
            else None
            )
        )
      )
      | _ -> None
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
      | Some cons2 -> 
      (*will need to make helper to order literals after holes and use here *)
      if Typ.consistent ty_in ty_in' then Some (cons1@cons2@[(ty_in', ty_in)])
      else None
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
    match (get_match_prod_typ ty) with
    | Some(TProd(typ1, typ2), cons1) ->(
      match ana ctx e1 typ1 with
      | None -> None
      | Some cons2 -> (
        match ana ctx e2 typ2 with
        | None -> None
        | Some cons3 -> Some (cons1 @ cons2 @ cons3)
      )
    )
    | _ -> None
  )
  | ELetPair (x, y, e1, e2) -> (
    match syn ctx e1 with
    | Some(typ_out, cons1) -> (
      match (get_match_prod_typ typ_out) with
      | Some(TProd(typ1, typ2), cons2) -> (
        match ana (Ctx.extend (Ctx.extend ctx (x, typ1)) (y, typ2)) e2 ty with
        | None -> None
        | Some cons3 -> Some (cons1 @ cons2 @ cons3)
      )
      | _ -> None
    )
    | _ -> None
  )
  | EInjL e -> (
    match (get_match_sum_typ ty) with
    | Some (TSum (typ1, _), cons1) -> (
      match (ana ctx e typ1) with
      | Some cons2 -> Some (cons1 @ cons2)
      | None -> None
    )
    | _ -> None
  )
  | EInjR e -> (
    match (get_match_sum_typ ty) with
    | Some (TSum (_, typ2), cons1) -> (
      match (ana ctx e typ2) with
      | Some cons2 -> Some (cons1 @ cons2)
      | None -> None
    )
    | _ -> None
  )
  | ECase (e, x, e1, y, e2) -> (
    match syn ctx e with
    | Some(typ_out, cons1) -> (
      match (get_match_sum_typ typ_out) with
      | Some(TSum(typ1, typ2), cons2) -> (
        match ana (Ctx.extend ctx (x, typ1)) e1 ty with
        | None -> None
        | Some (cons3) -> (
          match ana (Ctx.extend ctx (y, typ2)) e2 ty with
          | None -> None
          | Some (cons4) -> Some(cons1@cons2@cons3@cons4)
        )
      )
      | _ -> None
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
        (*will need to make helper to order literals after holes and use here *)
        if (Typ.consistent ty' ty) then Some (cons@[(ty', ty)])
        else None
      )
;;


let rec is_in_dom (v: TypeInferenceVar.t) (t: Typ.t) : bool =
  match t with
    | THole v' -> v' = v 
    | TNum 
    | TBool -> false
    | TArrow (t1, t2) 
    | TProd (t1, t2)
    | TSum (t1, t2) -> (is_in_dom v t1) || (is_in_dom v t2) 
;;

(*intended use: during unify as a helper for add results to inconsistencies; 
thus, no value should be solved of a hole or some derived sided hole. 
raises InvalidUse if such an occurrence is found*)
let combine_results (result1: Typ.unify_result) (result2: Typ.unify_result)
  : Typ.unify_result = 
  match (result1, result2) with
  | ((Solved typ1), (Solved typ2)) -> (
    match (typ1, typ2) with
    | (THole _, _)
    | (_, THole _) -> raise (InvalidUse "a variable was solved as a hole in add_result")
    | _ -> (
      if (Typ.consistent typ1 typ2) then (
        result1
      ) else (
        Typ.UnSolved [typ1; typ2]
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
          if (Typ.consistent ty basic_ty) then (
            Typ.Ambiguous ((Some ty), holes)
          )
          else (
            Typ.UnSolved ([ty; basic_ty] @ holes)
          )
        )
      )
      | None -> (
        if (List.for_all (Typ.consistent basic_ty) holes) then (
          Typ.Ambiguous ((Some basic_ty), holes)
        ) else (
          Typ.UnSolved (basic_ty::holes)
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
        if (Typ.consistent ty1 ty2) then (
          Typ.Ambiguous ((Some ty1), (smallest_unequal_pair holes1 holes2))
        ) else (
          Typ.UnSolved (ty1::ty2::(smallest_unequal_pair holes1 holes2))
        )
      )
    )
    | (None, (Some ty)) -> (
      match ty with
      | THole _ -> raise (InvalidUse "a variable was ambiguously solved as a hole in add_result")
      | _ -> (
        if (List.for_all (Typ.consistent ty) holes1) then (
          Typ.Ambiguous ((Some ty), (smallest_unequal_pair holes1 holes2))
        ) else (
          Typ.UnSolved (ty::(smallest_unequal_pair holes1 holes2))
        )
      )
    )
    | ((Some ty), None) -> (
      match ty with
      | THole _ -> raise (InvalidUse "a variable was ambiguously solved as a hole in add_result")
      | _ -> (
        if (List.for_all (Typ.consistent ty) holes2) then (
          Typ.Ambiguous ((Some ty), (smallest_unequal_pair holes1 holes2))
        ) else (
          Typ.UnSolved (ty::(smallest_unequal_pair holes1 holes2))
        )
      )
    )
    | (None, None) -> (
      Typ.Ambiguous (None, (smallest_unequal_pair holes1 holes2))
    )
  )
  | ((UnSolved ls), (Ambiguous (ty_op, holes)))
  | ((Ambiguous (ty_op, holes)), (UnSolved ls)) -> (
    match ty_op with
    | (Some ty) -> (
      match ty with
      | THole _ -> raise (InvalidUse "a variable was ambiguously solved as a hole in add_result")
      | _ -> Typ.UnSolved (ty::(smallest_unequal_pair holes ls))
    )
    | None -> Typ.UnSolved (smallest_unequal_pair holes ls)
  )
  | ((UnSolved ls), (Solved basic_ty))
  | ((Solved basic_ty), (UnSolved ls)) -> (
    match basic_ty with
    | THole _ -> raise (InvalidUse "a variable was solved as a hole in add_result")
    | _ -> Typ.UnSolved (basic_ty::ls)
  )
  | ((UnSolved ls1), (UnSolved ls2)) -> (
    Typ.UnSolved (smallest_unequal_pair ls1 ls2)
  )
;;

(*performs logic necessary to add a new unify_result to a list of results *)
let rec add_unify_result (new_result: TypeInferenceVar.t*Typ.unify_result) (old_results: Typ.unify_results)
  : Typ.unify_results =
  match old_results with
  | [] -> new_result::[]
  | (hd_var, hd_res)::tl -> (
    let (new_var, new_res) = new_result in
    if hd_var = new_var then (
      (*in theory: we should we able to replace combine results with extend_with_gens *)
      (hd_var, (combine_results new_res hd_res))::tl
    )
    else (hd_var, hd_res)::(add_unify_result new_result tl)
  )
;;

(*performs logic necessary to add a new rec_unify_result to a list of results *)
let rec add_rec_unify_result (new_result: Typ.t*Typ.unify_result) (old_results: Typ.rec_unify_results)
  : Typ.rec_unify_results =
  match old_results with
  | [] -> new_result::[]
  | (hd_typ, hd_res)::tl -> (
    let (new_typ, new_res) = new_result in
    if hd_typ = new_typ then (
      (hd_typ, (combine_results new_res hd_res))::tl
    )
    else (hd_typ, hd_res)::(add_rec_unify_result new_result tl)
  )
;;

(*merges two sets of unify results *)
let rec merge_unify_results (new_results: Typ.unify_results) (old_results: Typ.unify_results)
  : Typ.unify_results =
  match new_results with
  | [] -> old_results
  | hd::tl -> merge_unify_results tl (add_unify_result hd old_results)
;;

(*merges two sets of rec unify results *)
let rec merge_rec_unify_results (new_results: Typ.rec_unify_results) (old_results: Typ.rec_unify_results)
  : Typ.rec_unify_results = 
  match new_results with
  | [] -> old_results
  | hd::tl -> merge_rec_unify_results tl (add_rec_unify_result hd old_results)
;;

(*
  TODO: Phase out unify results and rec unify results to instead use TypGenRes.t
  (currently, unify results and their kin are only used in unify and immediately
  converted to typgenres before actually being used
  unify results have statused denoting current solution statuses. TypGenRes.t avoids
  claiming anything is solved or unsolved until actually finishing dfs and resolve.
  Currently, TypGenRes converts from unify results to its t by literally scraping
  all types out, totally ignoring concluded solution status, and compiling types
  in a typgen
  Potential approach: change all usages of unify results to genres
  Replace all moments where the current result is 
  )
*)

(*
let rec unify (constraints: Constraints.t)
  :  bool*Typ.unify_results*Typ.rec_unify_results =
  match constraints with
  | [] -> (true, [], [])
  | (x, y) :: xs ->
    (* generate substitutions of the rest of the list *)
    let (suc2, u_res2, r_res2) = unify xs in
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
          (*to ensure dependencies are captured, add both as solved of each other *)
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
  ;;
*)

  (*effectively generates a basic representation of a constraint tree from which dfs can kick off *)
let rec unify (constraints: Constraints.t):  TypGenRes.results =
  match constraints with
  | [] -> []
  | (x, y) :: xs ->
    (* generate substitutions of the rest of the list *)
    let gen_res_tl = unify xs in
    (* resolve the LHS and RHS of the constraints from the previous substitutions *)
    let gen_res_hd = unify_one x y in 
    TypGenRes.gen_results_set_add_many gen_res_hd gen_res_tl
and unify_one (t1: Typ.t) (t2: Typ.t): TypGenRes.results  =
    match ((t1, t2)) with
    | (TArrow (ty1, ty2), TArrow (ty3, ty4)) 
    | (TProd (ty1, ty2), TProd (ty3,ty4)) 
    | (TSum (ty1, ty2), TSum (ty3,ty4))-> (
      unify [(ty1,ty3);(ty2,ty4)]
    )
    | (((THole _) as hole), t) | (t, ((THole _) as hole)) ->
      (* If a hole is equal to a type with no holes, it suffices to link the nodes in one direction 
        (results are useless for fully defined types with no holes)
        Otherwise, link in both directions to ensure symmetricity of equality is reflected *)
      if (contains_hole t) then (
        [(hole, [(TypGen.typ_to_typ_gen t)])]
      ) else (
        [
          (hole, [(TypGen.typ_to_typ_gen t)]);
          (t, [(TypGen.typ_to_typ_gen hole)]);
        ]
      )
      
    | (TNum, TNum) 
    | (TBool, TBool) (* No reason to return axiomatically known results relating literals *)
    | (_, _) -> []  (* No reason to return inconsistencies between literals or compounds of literals (static checking suffices) *)
  ;;
