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


(* type result =
  | Success of Typ.unify_results
  | Failure of Typ.unify_results *)

let rec to_unsolved_ls (typvar_set: TypeInferenceVar.t list) (typ_ls: Typ.t list): Typ.unify_results = 
  match typvar_set with
  | [] -> []
  | hd::tl -> [(hd, Typ.UnSolved typ_ls)] @ (to_unsolved_ls tl typ_ls)
;;

(* let rec is_in_dom (v: TypeInferenceVar.t) (t: Typ.t): bool =
  match t with
  | HoleSubs (_, typ)
  | Primitive typ -> (
    match typ with
    | STHole v' -> v' == v
    | STNum -> false
    | STArrow (t1, t2) -> (is_in_dom v t1) || (is_in_dom v t2)
  )
;; *)


let rec unify (constraints: Constraints.t) (holes_repl_set: TypeInferenceVar.holes_repl_set) 
  : Typ.unify_results =
  match constraints with
  | [] -> []
  | (x, y) :: xs ->
    (* generate substitutions of the rest of the list *)
    let r2 = unify xs holes_repl_set in
    (* resolve the LHS and RHS of the constraints from the previous substitutions *)
    unify_one x y r2 holes_repl_set
and unify_one (t1: Typ.t) (t2: Typ.t) (partial_results: Typ.unify_results) (holes_repl_set: TypeInferenceVar.holes_repl_set)
  : Typ.unify_results =
    match ((t1, t2)) with
    | (TNum, TNum) -> partial_results
    | (THole v1, THole v2) -> (
      match (Typ.find_result v1 partial_results, Typ.find_result v2 partial_results) with
      | (None, None) -> 
        TypeInferenceVar.union holes_repl_set v1 v2; 
        partial_results
      | (Some Solved typ, None) -> 
        TypeInferenceVar.union holes_repl_set v1 v2; 
        [(v2, Typ.Solved typ)]@ partial_results
      | (None, Some Solved typ) -> 
        TypeInferenceVar.union holes_repl_set v1 v2; 
        [(v1, Typ.Solved typ)]@ partial_results
      | (Some UnSolved ls, None) -> 
        [(v2, Typ.UnSolved ls)]@ partial_results
      | (None, Some UnSolved ls) -> 
        [(v1, Typ.UnSolved ls)]@ partial_results
      | (Some typ1, Some typ2) -> (
        match (typ1, typ2) with
        | (UnSolved ls, Solved typ) -> 
          Typ.merge_unsolved_ls v1 ls v2 [typ] partial_results
        | (Solved typ, UnSolved ls) -> 
          Typ.merge_unsolved_ls v1 [typ] v2 ls partial_results
        | (UnSolved ls1, UnSolved ls2) -> 
          Typ.merge_unsolved_ls v1 ls1 v2 ls2 partial_results
        | (Solved TNum, Solved TNum) -> 
          TypeInferenceVar.union holes_repl_set v1 v2;
          partial_results
        | (Solved TArrow (ta1, ta2), Solved TArrow (ta3, ta4)) -> 
          TypeInferenceVar.union holes_repl_set v1 v2;
          unify [(ta1, ta3); (ta2, ta4)] holes_repl_set
        | (Solved THole _, _) | (_, Solved THole _) -> raise Impossible
        | (Solved typ1, Solved typ2)-> 
          let group1 = TypeInferenceVar.get_group holes_repl_set v1 in
          let group2 = TypeInferenceVar.get_group holes_repl_set v2 in
          let invalid_holes_ls = TypeInferenceVar.group_inter group1 group2 in
          let partial_results' =  Typ.erase_results v1 v2 partial_results in
          TypeInferenceVar.disconnect_ls holes_repl_set invalid_holes_ls;
          (to_unsolved_ls invalid_holes_ls [typ1;typ2])@ partial_results'
      )
    )
    | (TArrow (ta1, ta2), TArrow (ta3, ta4)) -> unify [(ta1, ta3); (ta2, ta4)] holes_repl_set
    | (THole v, typ) | (typ, THole v)->
        [(v, Typ.Solved typ)]@ partial_results
    | _ -> raise Impossible;
  ;;
