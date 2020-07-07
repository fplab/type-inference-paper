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

let rec is_in_dom (v: TypeInferenceVar.t) (t: Typ.t) : bool =
  match t with
    | THole v' -> v' == v 
    | TNum -> false
    | TArrow (t1, t2) -> (is_in_dom v t1) || (is_in_dom v t2) 
;;

let typ' = substitute typ partial_results in
if (is_in_dom v2 typ') then (false,[(v1, Typ.UnSolved [typ', t2]); (v2, Typ.UnSolved [typ', t2])])
else (true,[(v1, Typ.Solved typ'); (v2, Typ.Solved typ')])

let rec unify (constraints: Constraints.t) (holes_repl_set: TypeInferenceVar.holes_repl_set) 
  : bool*Typ.unify_results =
  match constraints with
  | [] -> []
  | (x, y) :: xs ->
    (* generate substitutions of the rest of the list *)
    let (suc2,r2) = unify xs holes_repl_set in
    (* resolve the LHS and RHS of the constraints from the previous substitutions *)
    let (suc1,r1) = unify_one x y r2 holes_repl_set in 
    (suc2 && suc1, r1 @ r2)
and unify_one (t1: Typ.t) (t2: Typ.t) (partial_results: Typ.unify_results) (holes_repl_set: TypeInferenceVar.holes_repl_set)
  : Typ.unify_result option * Typ.unify_results =
    match ((t1, t2)) with
    | (TNum, TNum) ->(Solved TNum, [])
    | (THole v1, THole v2) -> (
      TypeInferenceVar.union holes_repl_set v1 v2;
      match (Typ.find_result v1 partial_results, Typ.find_result v2 partial_results) with
      | (None, None) -> 
        if v1<v2 then (Solved t2,[(v1, Typ.Solved t2)])
        else if v1>v2 then (Solved t1,[(v2, Typ.Solved t1)])
        else (Solved t1,[])
      | (Some Solved typ, None) -> (
        match (unify_one typ t2 partial_results holes_repl_set) with
        | (Solved typ', result) -> (Solved typ', [(v1, Typ.Solved typ')]@result)
        | (UnSolved typ_ls, result) -> (UnSolved typ_ls, [(v1, Typ.UnSolved typ_ls)]@result)
        )
      | (None, Some Solved typ) -> (
        match (unify_one typ t1 partial_results holes_repl_set) with
        | (Solved typ', result) -> (Solved typ', [(v2, Typ.Solved typ')]@result)
        | (UnSolved typ_ls, result) -> (UnSolved typ_ls, [(v2, Typ.UnSolved typ_ls)]@result)
        )
      | (Some UnSolved ls, None) -> (UnSolved ls, [(v2, Typ.UnSolved ls)])
      | (None, Some UnSolved ls) -> (UnSolved ls, [(v1, Typ.UnSolved ls)])
      | (Some typ1, Some typ2) -> (
        match (typ1, typ2) with
        | (UnSolved ls, Solved typ) | (Solved typ, UnSolved ls) -> 
          let result = UnSolved (Typ.merge_typ_lst ls [typ]) in
          (Unsloved result, [(v1, result); (v2, result)])
        | (UnSolved ls1, UnSolved ls2) -> 
          let result = UnSolved (Typ.merge_typ_lst ls1 ls2) in
          (Unsloved result, [(v1, result); (v2, result)])
        | (Solved typ1', Solved typ2') -> (
          match (typ1', typ2') with
          | (TNum, TNum) -> (Solved TNum, [])
          | (TArrow _, TArrow _) -> (
            match (unify_one typ1' typ2' partial_results holes_repl_set) with
            | (Solved typ', result) -> (Solved typ', [(v1, Typ.Solved typ'), (v2, Typ.Solved typ')]@result)
            | (UnSolved typ_ls, result) -> (UnSolved typ_ls, [(v1, Typ.UnSolved typ_ls), (v2, Typ.UnSolved typ_ls)]@result)
          )
          | (THole v, typ) | (typ, THole v) -> (
            match (unify_one (THole v) typ partial_results holes_repl_set) with
            | (Solved typ', result) -> (Solved typ', [(v1, Typ.Solved typ'), (v2, Typ.Solved typ')]@result)
            | (UnSolved typ_ls, result) -> (UnSolved typ_ls, [(v1, Typ.UnSolved typ_ls), (v2, Typ.UnSolved typ_ls)]@result)
          )
          | _ -> (
            let invalid_holes_ls = TypeInferenceVar.get_group holes_repl_set v1 in
            let typ_1 = substitute typ1' partial_results in
            let typ_2 = substitute typ2' partial_results in
            TypeInferenceVar.disconnect_ls holes_repl_set invalid_holes_ls;
            (UnSolved [typ_1;typ_2], to_unsolved_ls invalid_holes_ls [typ_1;typ_2])
          )
        )
      )
    )
    | (TArrow (ta1, ta2), TArrow (ta3, ta4)) -> (
      let (suc, result) = unify [(ta1,ta3);(ta2,ta4)] holes_repl_set in
          if suc then (
            let typ' = substitute t1 (partial_results@result) in
            (Solved typ', result)
          ) else (
            let typ_1 = substitute t1 (partial_results@result) in
            let typ_2 = substitute t2 (partial_results@result) in
            let result_typ = Unsolved [typ_1, typ_2] in
            (result_typ, result)
          )
    )
    | (THole v, typ) | (typ, THole v)-> 
      if (is_in_dom v typ) then [(v, UnSolved [(substitute typ partial_results)])]
      else (
        match (Typ.find_result v partial_results) with
        | (Some Solved typ1) -> 
          match unify_one typ1 typ partial_results with
          | (Solved typ', result) -> (Solved typ', [(v, Solved typ')] @ result)
          | (UnSolved typ_ls, result) -> (UnSolved typ_ls, [(v, UnSolved typ_ls)] @ result)
        | (Some UnSolved ls) -> 
          [(v, UnSolved (Typ.merge_typ_lst ls [(substitute typ partial_results)]));]
        | (None) -> let typ' = substitute typ partial_results in (Solved typ', [(v, Solved typ')])
      )
    | _ -> raise Impossible;
  ;;
