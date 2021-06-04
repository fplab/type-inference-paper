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
          if Typ.consistent typ2 typ3 then Some (typ2, cons1 @ cons2 @ cons3 @[(typ2, typ3)])
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
        | Some (typ_y, cons3) -> (
          if Typ.consistent typ_x typ_y then Some(typ_x, cons1@cons2@cons3@[(typ_x, typ_y)])
          else None
          )
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
      | Some cons2 -> 
      if Typ.consistent ty_in ty_in' then Some (cons1@cons2@[(ty_in, ty_in')])
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
        if (Typ.consistent ty' ty) then Some (cons@[(ty, ty')])
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


(*Discuss this and maybe why it works as it does in context of Zoe maybe shifting away from this to the Solver update method *)
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
      (*for sake of clarity, a recomparison to the TAPL unify formulation
      rest is identical save for the hole case. In tapl, if two type variables are posited equal
      then you assert that the variable is equivalent to the other value (variable or literal)
      and update your constraint set by substituting this assertion (replacing all instances of the variable with the other value) 
      and composing the resultant substitution with the equivalnce you used in updating. In other words, endeavor to solve
      the mgu for the current constraint set where all constraints relating to the hole variable v are substituted with the type t
      and compose the resultant mgu with (v, t) consistency equivalence.*)
      
      (*Zoe's version:
      applies current results to both the variable and compared type. 
      if the variable remains a hole, it is consistent; return the new result
      if the variable is anything else, then attempt to unify the substituted type with the constraint typ t
        if this succeeds, with whatever list of generated consistencies, add the result that the hole v is consistent with typ
        if this fails, add the result that this hole failed to be consistent with the attempted consistency in the unsolved list
          zoe's commenting out instead was placing the substituted type that resulted in the inconsistency. 
            Why? see discussion of possibilities below*)

      (* According to Siek: general version
      Literally just returns that the type variable has the other one substituted for it
      I imagine TAPL's extra stuff is for efficiency 
      It looks like Zoe might've followed the general formulation while simply adapting the logic from where it posits equality
      by substitution to incorporate more consistency logic so it doesn't pass invalid constraints on by substitution*)
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
            (*old ver: \\subs_v; t \\typ   maybe Zoe wanted to change the way unsolved accumulated things? 
            it would seem so based on the new-algs in this branch. i think she may have been phasing out add result
            in favor of using Solver.update_typ_in_hole_eq and then running solve_eqs after instead of 'solving' every update
            after all, if she meant to 'comment out' subs_v and typ for just t, maybe she wnted to add the type as is without processing
            to be assessed later. kinda like generating a list of things holes have to be equal to*)
            | (false, result) -> (false, add_result (v, Typ.UnSolved([subs_v; typ])) result)
          )
        )
    | (_, _) -> 
      (false, [])
  ;;

(*
let rec gen_hole_eqs (constraints: Constraints.t) (eqs: Solver.hole_eqs): Solver.hole_eqs =
  match constraints with
  | [] -> eqs
  | hd::tl -> (
    match hd with 
    | (Hole v, typ)
    | (typ, Hole v) -> gen_hole_eqs tl (Solver.update_typ_in_hole_eqs eqs v typ)
    | (TArrow (ty1, ty2), TArrow (ty3, ty4)) 
    | (TProd (ty1, ty2), TProd (ty3,ty4)) 
    | (TSum (ty1, ty2), TSum (ty3,ty4)) -> (
      gen_hole_eqs ([(ty1,ty3); (ty2, ty4)]@tl) eqs
    )
  )
*)

(*takes a list of TVars each with a list of of associated Typ.t's
and returns _________________?
The function is made but never used anywhere, even in a comment...
Ask Anand: to use our final unification result to generate type information, do we repeatedly apply our mgu
sub until the result matches the input? *)
(*
let rec solve_eqs (eqs: Solver.hole_eqs): Solver.hole_eqs =
  match eqs with
  | [] -> []
  | (hole_v, v_typ_ls)::tl -> (
    (*WIP it would seem; mutual rec seems similar to Hazel block->line->opseq->operand/operator model for rec *)
    []
  )
and check_consistent_ls (eqs: Solver.hole_eqs) (typls: Typ.t list): bool =
  match typls with
  | [] -> true
  | hd::tl -> check_consistent_with_ls eqs tl hd
(*if the head type is consistent with the rest of the list given the hole eqns? 
true if eqns are true for the every elt of the rest*)
and check_consistent_with_ls (eqs: Solver.hole_eqs) (typls: Typ.t list) (typ: Typ.t): bool =
  match typls with
  | [] -> true
  | hd::tl -> (consistent_in_eqs eqs typ hd) && (check_consistent_with_ls tl typ)
(* where two types are consistent in eqs if they have at least one hole where if both are holes consistency 
is checked for their list of associated types (and if both have a list, that's currently undefined :/) *)
and consistent_in_eqs (eqs: Solver.hole_eqs) (typ1: Typ.t) (typ2: Typ.t): bool =
  match (typ1, typ2) with
  | (THole v1 , THole v2) -> (
    match (Solver.lookup v1 eqs, Solver.lookup v2 eqs) with 
    | (None, None) -> true
    | (None, Some ls)
    | (Some ls, None) -> check_consistent_ls ls
    | (Some ls, Some ls) ->
  )
  | (THole v , typ)
  | (typ , THole v)
  | (TNum, TNum)
  | (TBool, TBool) -> true
  (*why do all of these chart to false? *)
  | (TArrow (t1, t2), TArrow (t3, t4))
  | (TProd (t1, t2), TProd (t3, t4))
  | (TSum (t1, t2), TSum (t3, t4)) 
  | _ -> false
*)

(*this appears to be a function that generates the mgu then substitutes them in; should it continuously sub till equal? 
  see case 22, 27 in test output*)

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
