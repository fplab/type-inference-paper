open Syntax
open Impl

module ResTrack = struct
    type t = Typ.t list

    (*gets rid of a typ from the list *)
    let remove_typ (typ: Typ.t) (ls: t): t =
        let pred (elt: Typ.t): bool =
            elt <> typ
        in
        List.filter pred ls
    ;;

    (*generates a list of the types involved in (r) unify results. recursive results first *)
    let results_to_t (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results): t =
        let u_results_to_t (u_results: Typ.unify_results): t =
            let extend_by_u_res (acc: t) (u_res: TypeInferenceVar.t * Typ.unify_result): t =
                let (u_var, _) = u_res in
                (Typ.THole u_var)::acc
            in
            List.fold_left extend_by_u_res [] u_results
        in
        let r_results_to_t (r_results: Typ.rec_unify_results): t =
            let extend_by_r_res (acc: t) (r_res: Typ.t * Typ.unify_result): t =
                let (r_typ, _) = r_res in
                r_typ::acc
            in
            List.fold_left extend_by_r_res [] r_results
        in
        let ls_u = u_results_to_t u_results in
        let ls_r = r_results_to_t r_results in
        List.rev_append ls_r ls_u
    ;;
end

module CycleTrack = struct
    type t = Typ.t list

    let empty : t = [];;

    let track_typ (typ: Typ.t) (typs: t): t =
        typ::typs
    ;;

    let is_tracked (typ: Typ.t) (typs: t): bool =
        let is_typ (scrut: Typ.t): bool =
            typ = scrut
        in
        List.exists is_typ typs
    ;;
end

(*a sub result is some updated set of unify_results after resolving dependencies to simplest form and the result associated 
with the root called upon *)
type result_update = Typ.unify_results * Typ.rec_unify_results * Typ.unify_result

let rec string_of_typ (typ:Typ.t) =
    match typ with
    | THole var ->  "THole["^string_of_int(var)^"]"
    | TNum -> "TNum"
    | TBool -> "TBool"
    | TArrow (t1,t2) -> string_of_typ(t1) ^ "->"^ string_of_typ(t2)
    | TSum (t1,t2) -> string_of_typ(t1) ^ "+"^ string_of_typ(t2)
    | TProd (t1,t2) -> string_of_typ(t1) ^ "*"^ string_of_typ(t2)
;;

let rec string_of_typ_ls (typ_ls:Typ.t list) =
    match typ_ls with
    | [] -> " "
    | hd::tl -> 
        (string_of_typ hd)^ ", " ^ (string_of_typ_ls tl);
;;

let rec string_of_u_results (results: Typ.unify_results) =
    match results with
    | [] -> "\n"
    | hd::tl -> (
        let (var,typ) = hd in
        (
        match typ with 
        | Solved typ' -> ("solved: (" ^ string_of_int(var) ^ ") ("^ string_of_typ(typ') ^ ")\n");
        | Ambiguous (typ_op, typ_ls) -> (
            match typ_op with
            | Some typ -> 
            ("ambiguous: (" ^ string_of_int(var) ^ ") (" ^ string_of_typ(typ) ^ "; "
                ^ string_of_typ_ls(typ_ls) ^ ")\n");
            | None -> ("ambiguous: (" ^ string_of_int(var) ^ ") (None; "^ string_of_typ_ls(typ_ls) ^ ")\n");
        )
        | UnSolved typ_ls -> 
            ("unsolved: (" ^ string_of_int(var) ^ ") ("^ string_of_typ_ls(typ_ls) ^ ")\n");
        ) ^ string_of_u_results(tl);
    )
;;

let rec string_of_r_results (results: Typ.rec_unify_results) =
    match results with
    | [] -> "\n"
    | hd::tl -> (
        let (typ,res) = hd in
        (
        match res with 
        | Solved res' -> ("solved: (" ^ string_of_typ(typ) ^ ") ("^ string_of_typ(res') ^ ")\n");
        | Ambiguous (res_op, res_ls) -> (
            match res_op with
            | Some res' -> 
            ("ambiguous: (" ^ string_of_typ(typ) ^ ") (" ^ 
                string_of_typ(res') ^ "; " ^ string_of_typ_ls(res_ls) ^ ")\n");
            | None -> ("ambiguous: (" ^ string_of_typ(typ) ^ ") (None; "^ string_of_typ_ls(res_ls) ^ ")\n");
        )
        | UnSolved res_ls -> 
            ("unsolved: (" ^ string_of_typ(typ) ^ ") ("^ string_of_typ_ls(res_ls) ^ ")\n");
        ) ^ string_of_r_results(tl);
    )
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

let rec remove_ids (ty: Typ.t): Typ.t =
    match ty with
    | TNum -> TNum
    | TBool -> TBool
    | THole _ -> THole 0
    | TArrow (ty1, ty2) -> TArrow ((remove_ids ty1), (remove_ids ty2))
    | TProd (ty1, ty2) -> TProd ((remove_ids ty1), (remove_ids ty2))
    | TSum (ty1, ty2) -> TSum ((remove_ids ty1), (remove_ids ty2))
;;

let struc_eq_ignoring_ids (ty1: Typ.t) (ty2: Typ.t): bool =
    let ty1 = remove_ids ty1 in
    let ty2 = remove_ids ty2 in
    ty1 = ty2
;;

let cat_if_unequal_no_id_all (target_list: Typ.t list) (item: Typ.t): Typ.t list =
    let is_eq' (elt: Typ.t): bool = 
        struc_eq_ignoring_ids item elt
    in
    if (List.exists is_eq' target_list) then (
        target_list
    ) else (
        item::target_list
    )
;;

let smallest_unequal_no_id_pair (l1: Typ.t list) (l2: Typ.t list)
    : Typ.t list =
    List.fold_left cat_if_unequal_no_id_all l1 l2
;;

(* retrieve's an inference variables associated solution in the results list (if present) *)
let rec retrieve_result_for_inf_var (var: TypeInferenceVar.t) (results: Typ.unify_results)
    : Typ.unify_result option =
    match results with
    | [] -> None
    | (ty_var, result)::tl -> (
        if (ty_var = var) then (Some result) else retrieve_result_for_inf_var var tl
    )
;;

let rec retrieve_result_for_rec_typ (typ: Typ.t) (results: Typ.rec_unify_results)
    : Typ.unify_result option =
    match results with
    | [] -> None
    | (hd_typ, hd_result)::tl -> (
        if (typ = hd_typ) then (Some hd_result) else retrieve_result_for_rec_typ typ tl
    )
;;

let rec contains_literal (typ: Typ.t): bool = 
    match typ with
    | TNum
    | TBool -> true
    | THole _ -> false
    | TArrow (ty1, ty2)
    | TProd (ty1, ty2)
    | TSum (ty1, ty2) -> contains_literal ty1 || contains_literal ty2
;;

let condense (typs: Typ.t list): Typ.unify_result =
    match typs with
    | [] -> UnSolved []
    | hd::_ -> (
        let all_cons_with_typ (typs: Typ.t list) (typ: Typ.t): bool = 
            List.for_all (Typ.consistent typ) typs 
        in
        let all_cons = List.for_all (all_cons_with_typ typs) typs in
        if (all_cons) then (
            if (List.for_all is_fully_literal typs) then (
                Solved hd
            ) else (
                let literal_opt = List.find_opt is_fully_literal typs in
                let not_literal (typ: Typ.t): bool = Bool.not (is_fully_literal typ) in
                match literal_opt with
                | Some literal -> Ambiguous ((Some literal), (smallest_unequal_pair [] (List.filter not_literal typs)))
                | None -> Ambiguous (None, (smallest_unequal_pair [] typs))
            )
        )
        else (
            UnSolved (smallest_unequal_pair [] typs)
        )
    )
;;

let ty_to_res_id (typ: Typ.t): TypeInferenceVar.t option * Typ.t option = 
    match typ with
    | TNum
    | TBool -> (None, None)
    | THole var -> ((Some var), None)
    | TArrow _ 
    | TProd _ 
    | TSum _ -> (None, (Some typ))
;;

let split (typ: Typ.t): (Typ.t * Typ.t) option = 
    match typ with
    | TArrow (ty1, ty2)
    | TProd (ty1, ty2)
    | TSum (ty1, ty2) -> Some (ty1, ty2)
    | _ -> None
;;

let split_ls (ls: Typ.t list): (Typ.t list) * (Typ.t list) = 
    let acc_splits (acc: (Typ.t list) * (Typ.t list)) (typ: Typ.t)
        : (Typ.t list) * (Typ.t list) =
        let acc_lhs, acc_rhs = acc in
        match (split typ) with
        | Some (ty1, ty2) -> (ty1::acc_lhs, ty2::acc_rhs)
        | None -> acc
    in
    List.fold_left acc_splits ([], []) ls
;;

let all_of_ctr (ctr: Typ.t -> Typ.t -> Typ.t) (ls: Typ.t list): bool * (Typ.t list) =
    let of_ctr (aps: bool * bool * bool) (acc: bool * (Typ.t list)) (typ: Typ.t)
        : (bool * (Typ.t list)) =
        let (arrow, prod, sum) = aps in
        let acc_bool, acc_ls = acc in
        match typ with
        | TNum
        | TBool -> (false, typ::acc_ls)
        | THole _ -> (acc_bool, acc_ls)
        | TArrow _ -> if (arrow) then (acc_bool, acc_ls) else (false, typ::acc_ls)
        | TProd _ -> if (prod) then (acc_bool, acc_ls) else (false, typ::acc_ls)
        | TSum _ -> if (sum) then (acc_bool, acc_ls) else (false, typ::acc_ls)
    in
    let aps =
        match ctr TNum TNum with
        | TArrow _ -> (true, false, false)
        | TProd _ -> (false, true, false)
        | TSum _ -> (false, false, true)
        | _ -> raise Impossible
    in
    List.fold_left (of_ctr aps) (true, []) ls
;;

let split_as_ctr (ctr: Typ.t -> Typ.t -> Typ.t) (res: Typ.unify_result)
    : (Typ.unify_result * Typ.unify_result) =
    let ty_ls = 
        match res with
        | Solved ty -> [ty]
        | Ambiguous ((Some ty), tys) -> ty::tys
        | Ambiguous (None, tys)
        | UnSolved tys -> tys
    in
    let is_of_struc, _ = all_of_ctr ctr ty_ls in
    let lhs_tys, rhs_tys = split_ls ty_ls in
    if (is_of_struc) then (
        ((condense lhs_tys), (condense rhs_tys))
    ) else (
        (*NOTE! Currently, this will not note why things are unsolved if fitting in this case
            ex: Num used as arrow, sum used as arrow, etc
        For now, outliers aren't added as they can represent equivalences we don't want to follow in resolution. 
        later, we can add error statuses*)
        ((UnSolved lhs_tys), (UnSolved rhs_tys))
    )
;;

(*performs logic necessary to add a new unify_result to a list of results *)
let rec replace_unify_result (new_result: TypeInferenceVar.t * Typ.unify_result) (old_results: Typ.unify_results)
    : Typ.unify_results =
    match old_results with
    | [] -> new_result::[]
    | (hd_var, hd_res)::tl -> (
        let (new_var, new_res) = new_result in
        if hd_var = new_var then (
            (hd_var, new_res)::tl
        )
        else (hd_var, hd_res)::(replace_unify_result new_result tl)
    )
;;

(*performs logic necessary to add a new rec_unify_result to a list of results *)
let rec replace_rec_unify_result (new_result: Typ.t * Typ.unify_result) (old_results: Typ.rec_unify_results)
    : Typ.rec_unify_results =
    match old_results with
    | [] -> new_result::[]
    | (hd_typ, hd_res)::tl -> (
        let (new_typ, new_res) = new_result in
        if hd_typ = new_typ then (
            (hd_typ, new_res)::tl
        )
        else (hd_typ, hd_res)::(replace_rec_unify_result new_result tl)
    )
;;

let add_all_refs_as_results (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results)
    : Typ.unify_results * Typ.rec_unify_results =
    (*extends u results to include all holes contained within r results
    logic: if in an r result, it technically is truly used as a hole with some potential result
            and needs to be able to be referenced.
    why all r_results in u_results need not have results: they already will; r results are only added
            in concert with a link to a u_result. but an equivalence to an r result can be generated
            without adding the types contained in the r result*)
    (*accumulates all referenced holes in the recursive types *)
    let rec acc_rec_holes (acc: TypeInferenceVar.t list) (typ: Typ.t): TypeInferenceVar.t list =
        match typ with
        | TNum
        | TBool -> acc
        | THole var -> var::acc
        | TArrow (ty1, ty2)
        | TProd (ty1, ty2)
        | TSum (ty1, ty2) ->  (
            let acc = acc_rec_holes acc ty1 in
            acc_rec_holes acc ty2
        )
    in
    (*converts the list of unify results to recursive types*)
    let r_res_to_typ (acc: Typ.t list) (res: Typ.t * Typ.unify_result): Typ.t list =
        let (r_typ, _) = res in
        r_typ::acc
    in
    let r_typs = List.fold_left r_res_to_typ [] r_results in
    let var_ls = List.fold_left acc_rec_holes [] r_typs in
    let extend_u_results (acc: Typ.unify_results) (var: TypeInferenceVar.t): Typ.unify_results =
        Impl.add_unify_result (var, (Typ.Ambiguous (None, [(Typ.THole var)]))) acc
    in
    (List.fold_left extend_u_results u_results var_ls), r_results
;;

(*a method that dfs's on a type to accumulate all known types it is cyclic with. returns a boolean denoting
if an occurs check was failed due to the results and a list of all types *)
let rec dfs_typs (root: Typ.t) (gens: TypGenRes.results) (tracked: CycleTrack.t) (unseen_results: ResTrack.t) (ctr_exp: bool)
    : bool * (TypGen.typ_gens) * CycleTrack.t * ResTrack.t = 
    let tracked = CycleTrack.track_typ root tracked in
    let unseen_results = ResTrack.remove_typ root unseen_results in
    let by_ctr_exp (ctr_exp: bool) (ctr: TypGen.ctr) (ty1: Typ.t) (ty2: Typ.t)
        : bool * (Typ.t list) * CycleTrack.t * ResTrack.t =
        if (ctr_exp) then (
            dfs_typs_of_ctr ctr ty1 ty2 gens tracked unseen_results
        ) else (
            match (TypGenRes.retrieve_gen_for_typ root gens) with
            | Some gen -> dfs_typs_res gen gens tracked unseen_results false
            | None -> (true, [], tracked, unseen_results)
        )
    in
    let (occ, dfs_all, tracked, unseen_results) = 
        match root with
        | TNum -> (true, [], tracked, unseen_results)
        | TBool -> (true, [], tracked, unseen_results)
        | TArrow (ty1, ty2) -> (by_ctr_exp ctr_exp TypGen.Arrow ty1 ty2)
        | TProd (ty1, ty2) -> (by_ctr_exp ctr_exp TypGen.Prod ty1 ty2)
        | TSum (ty1, ty2) -> (by_ctr_exp ctr_exp TypGen.Sum ty1 ty2)
        | THole _ -> (
            match (TypGen.retrieve_gen_for_typ root gens) with
            | Some gen -> (dfs_typs_gen gen gens tracked unseen_results ctr_exp)
            | None -> (true, [], tracked, unseen_results)
        )
    in
    (*Printf.printf "DEBUG:\n";
    Printf.printf "%s\n" ((string_of_typ root) ^ " {:} " ^ (string_of_typ_ls dfs_all));*)
    (occ, (TypGen.extend_with_typ dfs_all root), tracked, unseen_results)
and dfs_typs_of_ctr (ctr: TypGen.ctr) (ty1: Typ.t) (ty2: Typ.t) (gens: TypGenRes.results) (tracked: CycleTrack.t) (unseen_results: ResTrack.t)
    : bool * (TypGen.typ_gens) * CycleTrack.t * ResTrack.t =
    let rec_ty = ((TypGen.get_mk_of_ctr ctr) ty1 ty2) in
    let (_, tys_u, _, _) =
        match (TypGen.retrieve_gen_for_typ rec_ty gens) with
        | Some gen -> dfs_typs_res gen gens tracked unseen_results false
        | None -> (true, [], [], [])
    in
    let (lhs_tys, rhs_tys) = TypGen.split ctr tys_u in
    let gens = TypGenRes.link_typ_to_gen ty1 lhs_tys gens in
    let gens = TypGenRes.link_typ_to_gen ty2 rhs_tys gens in
    let (occ1, ty1_gen, _, unseen_results) = 
        dfs_typs ty1 gens CycleTrack.empty unseen_results true
    in
    let (occ2, ty2_gen, _, unseen_results) = 
        dfs_typs ty2 gens CycleTrack.empty unseen_results true
    in
    let rec_tys_gen = TypGen.fuse ctr ty1_gen ty2_gen in
    let (dfs_occ, dfs_tys, tracked, unseen_results) = 
        match (TypGenRes.retrieve_gen_for_typ rec_ty r_results) with
        | Some gen -> dfs_typs_gen gen gens tracked unseen_results true
        | None -> (true, [], tracked, unseen_results)
    in
    (*Printf.printf "DEBUG:\n";
    Printf.printf "%s\n" ((string_of_typ (ctr ty1 ty2)) ^ " {:} "^ (string_of_typ_ls final_tys));*)
    (occ1 && occ2 && dfs_occ, (TypGen.extend_with_typ_gen dfs_tys rec_tys_gen), tracked, unseen_results)
and dfs_typs_gen (gen: TypGen.typ_gens) (gens: TypGenRes.results) (tracked: CycleTrack.t) (unseen_results: ResTrack.t) (ctr_exp: bool)
    : bool * (TypGen.typ_gens) * CycleTrack.t * ResTrack.t =
    let destinations = TypGen.explorable_list gen gens in
    let in_domain_and_unequal (list_elt: Typ.t) (tracked_elt: Typ.t): bool =
        (tracked_elt <> list_elt) && (Typ.contains_typ tracked_elt list_elt)
    in
    let traverse_if_valid (acc: bool * (TypGen.typ_gens) * CycleTrack.t * ResTrack.t) (list_elt: Typ.t)
        : bool * (TypGen.typ_gens) * CycleTrack.t * ResTrack.t =
        let (acc_b, acc_typs, tracked, unseen_results) = acc in
        (*if invalid *)
        if (List.exists (in_domain_and_unequal list_elt) tracked) then (
            (false, acc_typs, tracked, unseen_results)
        ) else (
            (*if already traversed *)
            if (CycleTrack.is_tracked list_elt tracked) then (
                (acc_b, acc_typs, tracked, unseen_results)
            ) else (
                let (occ_all, dfs_all, tracked, unseen_results) = 
                    dfs_typs list_elt gens tracked unseen_results ctr_exp
                in
                (acc_b && occ_all, 
                (TypGen.combine acc_typs dfs_all),
                tracked,
                unseen_results)
            )
        )
    in
    List.fold_left traverse_if_valid (true, [], tracked, unseen_results) ty_ls
;;

(*since the final solution contains all references, there is technically no need to dfs; you could just 
replace the solution for all members of the list and call recursive protocol for any recursive types in it
wouldn't be a hard change. just remove calls to resolve_res and wrap calls to the other two in a standard
recursive matching on a list generated from the solution *)
let rec resolve (root: Typ.t) (solution: TypGen.typ_gens) (sol_occ: bool) (gens: TypGenRes.results) (tracked: CycleTrack.t)
    : TypGenRes.results * CycleTrack.t =
    let tracked = CycleTrack.track_typ root tracked in
    match root with
    | TNum
    | TBool -> (gens, tracked)
    | TArrow (ty1, ty2) -> resolve_of_ctr TypGen.Arrow ty1 ty2 solution sol_occ gens tracked
    | TProd (ty1, ty2) -> resolve_of_ctr TypGen.Prod ty1 ty2 solution sol_occ gens tracked
    | TSum (ty1, ty2) -> resolve_of_ctr TypGen.Sum ty1 ty2 solution sol_occ gens tracked
    | THole _ -> (
        let gens = TypGenRes.replace_gen_and_occ_of_typ root solution sol_occ gens in
        resolve_typ_gens solution gens tracked
    )
and resolve_of_ctr (ctr: TypGen.ctr) (ty1: Typ.t) (ty2: Typ.t) (solution: TypGen.typ_gens) (sol_occ: bool) (gens: TypGenRes.results) 
    (tracked: CycleTrack.t): TypGenRes.results * CycleTrack.t =
    let (lhs_tys, rhs_tys) = TypGen.split ctr solution in
    (*no need to generate new type results since dfs should already have traversed this and constructed the necessary ones *)
    (*update results with information for children *)
    let gens = TypGenRes.replace_gen_and_occ_of_typ ty1 lhs_tys sol_occ gens in
    let (gens, tracked) = resolve_typ_gens lhs_tys sol_occ gens tracked in
    let gens = TypGenRes.replace_gen_and_occ_of_typ ty2 rhs_tys sol_occ gens in
    let (gens, tracked) = resolve_typ_gens rhs_tys sol_occ gens tracked in
    match (TypGenRes.retrieve_gen_for_typ ((TypGen.get_mk_of_ctr ctr) ty1 ty2) r_results) with
    | Some _ -> (
        let gens  = 
            TypGenRes.replace_gen_and_occ_of_typ ((TypGen.get_mk_of_ctr ctr) ty1 ty2) solution sol_occ gens
        in
        resolve_typ_gens solution sol_occ gens tracked
    )
    | None -> (gens, tracked)
(*already following a replaced value; just dfs so other funcs can replace *)
and resolve_typ_gens (solution: TypGen.typ_gens) (sol_occ: bool) (gens: TypGenRes.results) (tracked: CycleTrack.t)
    : TypGenRes.results * CycleTrack.t =
    let ty_ls = TypGen.explorable_list solution in
    let traverse_if_valid (acc: TypGenRes.results * CycleTrack.t) (list_elt: Typ.t)
        : TypGenRes.results * CycleTrack.t =
        let (acc_res, tracked) = acc in
        if (CycleTrack.is_tracked list_elt tracked) then (
            (acc_res, tracked)
        ) else (
            resolve list_elt solution sol_occ acc_res tracked
        )
    in
    List.fold_left traverse_if_valid (gens, tracked) ty_ls
;;

(*converts all ambiguous statuses to a fully simplified non ambiguous solution status *)
let disambiguate_u (u_result: TypeInferenceVar.t * Typ.unify_result) (unseen_results: ResTrack.t)
    (old_r_results: Typ.rec_unify_results)
    : Typ.unify_results * Typ.rec_unify_results * ResTrack.t = 
    let (id, res) = u_result in
    match res with
    | Solved _ -> [u_result], [], (ResTrack.remove_typ (Typ.THole id) unseen_results)
    | Ambiguous (_, children)
    | UnSolved children -> (
        let res' = 
            match res with
            | Ambiguous (ty_op, _) -> (
                match ty_op with
                | Some ty -> (Typ.Solved ty)
                | None -> (
                    match (find_representative children) with
                    | Some ub -> Typ.Solved ub
                    | None -> Typ.Solved (Typ.THole id)
                )
            )
            | _ -> (Typ.UnSolved (smallest_unequal_no_id_pair [] (List.filter contains_literal children)))
        in
        let add_res_and_track (acc: Typ.unify_results * Typ.rec_unify_results * ResTrack.t) (child: Typ.t)
            : Typ.unify_results * Typ.rec_unify_results * ResTrack.t =
            let acc_ls_u, acc_ls_r, unseen_results = acc in
            match (List.find_opt (fun elt -> (elt = child)) unseen_results) with
            | Some _ -> (
                let unseen_results = ResTrack.remove_typ child unseen_results in
                match child with
                | TNum
                | TBool -> acc
                | THole var -> ((var, res')::acc_ls_u, acc_ls_r, unseen_results)
                | TArrow _
                | TProd _
                | TSum _ -> (
                    match (retrieve_result_for_rec_typ child old_r_results) with
                    | Some _ -> (acc_ls_u, (child, res')::acc_ls_r, unseen_results)
                    | _ -> acc
                )
            )
            | None -> acc
        in
        List.fold_left add_res_and_track ([], [], unseen_results) ((Typ.THole id)::children)
    )
;;

let disambiguate_r (r_result: Typ.t * Typ.unify_result) (unseen_results: ResTrack.t) 
    (old_r_results: Typ.rec_unify_results)
    : Typ.unify_results * Typ.rec_unify_results * ResTrack.t = 
    let (r_typ, res) = r_result in
    match res with
    | Solved _ -> ([], [r_result], (ResTrack.remove_typ r_typ unseen_results))
    | Ambiguous (_, children)
    | UnSolved children -> (
        let res' =
            match res with
            | Ambiguous (ty_op, _) -> (
                match ty_op with
                | Some ty -> (Typ.Solved ty)
                | None -> (
                    match (find_representative children) with
                    | Some ub -> Typ.Solved ub
                    | None -> Typ.Solved r_typ
                )
            )   
            | _ -> (Typ.UnSolved (smallest_unequal_no_id_pair [] (List.filter contains_literal children)))
        in
        let add_res_and_track (acc: Typ.unify_results * Typ.rec_unify_results * ResTrack.t) (child: Typ.t)
            : Typ.unify_results * Typ.rec_unify_results * ResTrack.t =
            let acc_ls_u, acc_ls_r, unseen_results = acc in
            match (List.find_opt (fun elt -> (elt = child)) unseen_results) with
            | Some _ -> (
                let unseen_results = ResTrack.remove_typ child unseen_results in
                match child with
                | TNum
                | TBool -> acc
                | THole var -> ((var, res')::acc_ls_u, acc_ls_r, unseen_results)
                | TArrow _
                | TProd _
                | TSum _ -> (
                    match (retrieve_result_for_rec_typ child old_r_results) with
                    | Some _ -> (acc_ls_u, (child, res')::acc_ls_r, unseen_results)
                    | _ -> acc
                )
            )
            | None -> acc
        in
        List.fold_left add_res_and_track ([], [], unseen_results) (r_typ::children)
    )
;;

let disambiguate (old_u_results: Typ.unify_results) (old_r_results: Typ.rec_unify_results) (unseen_results: ResTrack.t)
    : Typ.unify_results * Typ.rec_unify_results =
    let acc_u_res (acc: Typ.unify_results * Typ.rec_unify_results * ResTrack.t) (res: TypeInferenceVar.t * Typ.unify_result)
        : Typ.unify_results * Typ.rec_unify_results * ResTrack.t =
        let (acc_u, acc_r, unseen_results) = acc in
        let (upd_u, upd_r, unseen_results) = disambiguate_u res unseen_results old_r_results in
        let u_res = List.rev_append upd_u acc_u in
        let r_res = List.rev_append upd_r acc_r in
        (u_res, r_res, unseen_results)
    in
    let acc_r_res (acc: Typ.unify_results * Typ.rec_unify_results * ResTrack.t) (res: Typ.t * Typ.unify_result)
        : Typ.unify_results * Typ.rec_unify_results * ResTrack.t =
        let (acc_u, acc_r, unseen_results) = acc in
        let (upd_u, upd_r, unseen_results) = disambiguate_r res unseen_results old_r_results in
        let u_res = List.rev_append upd_u acc_u in
        let r_res = List.rev_append upd_r acc_r in
        (u_res, r_res, unseen_results)
    in
    let rec over_restrack (new_u: Typ.unify_results) (new_r: Typ.rec_unify_results) (unseen_results: ResTrack.t)
        : Typ.unify_results * Typ.rec_unify_results * ResTrack.t =
        match unseen_results with
        | [] -> (new_u, new_r, [])
        | hd::_ -> (
            let (new_u, new_r, unseen_results) =
                match hd with
                | TNum
                | TBool -> raise Impossible
                | THole var -> (
                    match (retrieve_result_for_inf_var var old_u_results) with
                    | Some unif_res -> (acc_u_res (new_u, new_r, unseen_results) (var, unif_res))
                    | None -> raise Impossible
                )
                | _ -> (
                    match (retrieve_result_for_rec_typ hd old_r_results) with
                    | Some unif_res -> (acc_r_res (new_u, new_r, unseen_results) (hd, unif_res))
                    | None -> raise Impossible
                )
            in
            over_restrack new_u new_r unseen_results
        )
    in
    let (new_u, new_r, _) = over_restrack [] [] unseen_results in
    (new_u, new_r)
;;

let rec fix_tracked_results (results_to_fix: ResTrack.t) (gens: TypGenRes.results)
    : ResTrack.t * TypGenRes.results =
    match results_to_fix with
    | [] -> results_to_fix, u_results, r_results
    | hd::_ -> (
        let (occ, dfs_tys, _, results_to_fix) = dfs_typs hd u_results r_results CycleTrack.empty results_to_fix true in
        (*Printf.printf "debug\n";
        Printf.printf "%s\n" (string_of_u_results ((-1, cycle_res)::[]));*)
        let (gens, _) = resolve hd dfs_tys occ gens CycleTrack.empty in
        fix_tracked_results results_to_fix gens
    )
;;

let finalize_results (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results)
    : Typ.unify_results * Typ.rec_unify_results = 
    let (u_results, r_results) = 
        add_all_refs_as_results u_results r_results
    in
    let gens = TypGenRes.unif_results_to_gen_results u_results r_results in
    let results_to_fix = ResTrack.results_to_t u_results r_results in
    let (_, gens) = 
        fix_tracked_results results_to_fix gens
    in
    (*Printf.printf "%s\n" (string_of_u_results u_results);
    Printf.printf "%s\n" (string_of_r_results r_results);*)
    let comp_u_res (res1: TypeInferenceVar.t * Typ.unify_result) (res2: TypeInferenceVar.t * Typ.unify_result)
        : int =
        let (var1, _) = res1 in
        let (var2, _) = res2 in
        Stdlib.compare var1 var2
    in
    let rec extract_leftmost (typ: Typ.t): int =
        match typ with
        | TNum
        | TBool -> -1
        | THole var -> var
        | TArrow (ty1, ty2)
        | TProd (ty1, ty2)
        | TSum (ty1, ty2) -> (
            let lhs = extract_leftmost ty1 in
            let rhs = extract_leftmost ty2 in
            match (lhs, rhs) with
            | (-1, -1) -> -1
            | (-1, _) -> rhs
            | _ -> lhs
        )
    in
    let comp_r_res (res1: Typ.t * Typ.unify_result) (res2: Typ.t * Typ.unify_result)
        : int =
        let (ty1, _) = res1 in
        let (ty2, _) = res2 in
        let id1 = extract_leftmost ty1 in
        let id2 = extract_leftmost ty2 in
        Stdlib.compare id1 id2
    in
    let (u_results, r_results) = disambiguate u_results r_results results_to_fix in
    (List.fast_sort comp_u_res u_results), (List.fast_sort comp_r_res r_results)
;; 