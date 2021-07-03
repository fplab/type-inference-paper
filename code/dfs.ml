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

    let u_results_to_t (u_results: Typ.unify_results): t =
        let extend_by_u_res (acc: t) (u_res: TypeInferenceVar.t * unify_result): t =
            let (u_var, _) = u_res in
            (Typ.THole u_var)::acc
        in
        List.fold_left extend_by_u_res [] u_results
    ;;

    let r_results_to_t (r_results: Typ.rec_unify_results): t =
        let extend_by_r_res (acc: t) (r_res: Typ.t * unify_result): t =
            let (r_typ, _) = r_res in
            r_typ::acc
        in
        List.fold_left extend_by_r_res [] r_results
    ;;

    (*generates a list of the types involved in (r) unify results. recursive results first *)
    let results_to_t (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results): t =
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
            typ == scrut
        in
        List.exists is_typ typs
    ;;
end

(*a sub result is some updated set of unify_results after resolving dependencies to simplest form and the result associated 
with the root called upon *)
type result_update = Typ.unify_results * Typ.rec_unify_results * Typ.unify_result

(* retrieve's an inference variables associated solution in the results list (if present) *)
let rec retrieve_result_for_inf_var (var: TypeInferenceVar.t) (results: Typ.unify_results)
    : Typ.unify_result option =
    match results with
    | [] -> None
    | (ty_var, result)::tl -> (
        if (ty_var == var) then (Some result) else retrieve_result_for_inf_var var tl
    )
;;

let rec retrieve_result_for_rec_typ (typ: Typ.t) (results: Typ.rec_unify_results)
    : Typ.unify_result option =
    match results with
    | [] -> None
    | (hd_typ, hd_result)::tl -> (
        if (typ = hd_typ) then (Some hd_result) else retrieve_result_for_inf_var typ tl
    )
;;

let is_literal (typ: Typ.t): bool = (hd = TNum || hd = TBool) ;;

let rec find_literal (typs: Typ.t list): Typ.t option = 
    match typs with
    | [] -> None
    | hd::tl -> if (is_literal hd) then (Some hd) else (find_literal tl)
;;

let condense (typs: Typ.t list): Typ.unify_result =
    match typs with
    | [] -> UnSolved []
    | hd::_ -> (
        let all_cons_with_typ (typs: Typ.t list) (typ: Typ.t): bool = 
            List.for_all (Typ.consistent typ) typs 
        in
        let all_cons = List.forall (all_cons_with_typ typs) typs in
        let hole_present = List.exists contains_hole typs in
        if (all_cons) then (
            if (hole_present) then (
                match (find_literal typs) with
                | Some ty -> Ambiguous ((Some ty), (List.filter (Bool.not is_literal) typs))
                | None -> Ambiguous (None, typs)
            ) else (
                Solved hd
            )
        ) else (
            UnSolved typs
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
    | TSum (ty1, ty2) -> Some (ty1 * ty2)
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
        | THole -> (acc_bool, acc_ls)
        | TArrow _ -> if (arrow) then (acc_bool, acc_ls) else (false, typ::acc_ls)
        | TProd _ -> if (prod) then (acc_bool, acc_ls) else (false, typ::acc_ls)
        | TSum _ -> if (sum) then (acc_bool, acc_ls) else (false, typ::acc_ls)
    in
    let aps =
        match ctr TNum TNum with
        | TArrow _ -> (true, false, false)
        | TProd _ -> (false, true, false)
        | TSum _ -> (false, false, true)
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

let mk_ctr_types (ctr: Typ.t -> Typ.t -> Typ.t) (const: Typ.t) (const_is_left: bool) (acc: Typ.t list) (variant: Typ.t)
    : Typ.t list =
    if (const_is_left) then (ctr const variant)::acc else (ctr variant const)::acc
;;

let fuse_lists (ctr: Typ.t -> Typ.t -> Typ.t) (ty1_ls: Typ.t list) (ty2_ls: Typ.t list)
    : Typ.t list = 
    let acc_mk_ctr_types (acc: Typ.t list) (const_of_left: Typ.t): Typ.t list = 
        List.fold_left (mk_ctr_types ctr const_of_left true) acc (ty2_ls)
    in
    List.fold_left acc_mk_ctr_types [] ty1_ls
;;

(*performs logic necessary to add a new unify_result to a list of results *)
let rec replace_unify_result (new_result: TypeInferenceVar.t * Typ.unify_result) (old_results: Typ.unify_results)
    : Typ.unify_results =
    match old_results with
    | [] -> new_result::[]
    | (hd_var, _)::tl -> (
        let (new_var, new_res) = new_result in
        if hd_var == new_var then (
            (hd_var, new_res)::tl
        )
        else (hd_var, hd_res)::(add_unify_result new_result tl)
    )
;;

(*performs logic necessary to add a new rec_unify_result to a list of results *)
let rec replace_rec_unify_result (new_result: Typ.t * Typ.unify_result) (old_results: Typ.rec_unify_results)
    : Typ.rec_unify_results =
    match old_results with
    | [] -> new_result::[]
    | (hd_typ, _)::tl -> (
        let (new_typ, new_res) = new_result in
        if hd_typ = new_typ then (
            (hd_typ, new_res)::tl
        )
        else (hd_typ, hd_res)::(add_rec_unify_result new_result tl)
    )
;;

(*a method that dfs's on a type to accumulate all known types it is cyclic with. returns a boolean denoting
if an occurs check was failed due to the results and a list of all types *)
let rec dfs_typs (root: Typ.t) (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results) (tracked: CycleTrack.t)
    (unseen_results: ResTrack.t): bool * (Typ.t list) * ResTrack.t = 
    let tracked = CycleTrack.track_typ root tracked in
    let unseen_results = ResTrack.remove_typ root in
    match root with
    | TNum -> (true, [TNum])
    | TBool -> (true, [TBool])
    | TArrow (ty1, ty2) -> (dfs_typs_of_ctr mk_arrow ty1 ty2 u_results r_results tracked unseen_results)
    | TProd (ty1, ty2) -> (dfs_typs_of_ctr mk_prod ty1 ty2 u_results r_results tracked unseen_results)
    | TSum (ty1, ty2) -> (dfs_typs_of_ctr mk_sum ty1 ty2 u_results r_results tracked unseen_results)
    | THole var -> (
        match (retrieve_result_for_inf_var var u_results) with
        | Some unif_res -> (dfs_typs_res unif_res tracked unseen_results)
        | None -> (true, [])
    )
and dfs_typs_of_ctr (ctr: Typ.t -> Typ.t -> Typ.t) (ty1: Typ.t) (ty2: Typ.t) (u_results: Typ.unify_results) 
    (r_results: Typ.rec_unify_results) (tracked: CycleTrack.t) (unseen_results: ResTrack.t)
    : bool * (Typ.t list) * ResTrack.t =
    let (occ1, ty1_ls) = dfs_typs ty1 u_results r_results CycleTrack.empty unseen_results in
    let (occ2, ty2_ls) = dfs_typs ty2 u_results r_results CycleTrack.empty unseen_results in
    let rec_tys = fuse_lists ty1_ls ty2_ls in
    let (dfs_occ, dfs_tys) = 
        match (retrieve_result_for_rec_typ (ctr ty1 ty2) r_results) with
        | Some unif_res -> dfs_typs_res unif_res tracked unseen_results
        | None -> (true, [])
    in
    (occ1 && occ2 && dfs_occ, (List.rev_append rec_tys dfs_tys))
and dfs_typs_res (unif_res: Typ.unify_result) (tracked: CycleTrack.t) (unseen_results: ResTrack.t)
    : bool * (Typ.t list) * ResTrack.t =
    match unif_res with
    | Solved ty -> (true, [ty])
    | Ambiguous (ty_op, ty_ls)
    | UnSolved ty_ls -> (
        let new_hd = 
            match unify_res with
            | Ambiguous ((Some ty), _) -> [ty]
            | _ -> []
        in
        let in_domain_and_unequal (list_elt: Typ.t) (tracked_elt: CycleTrack.t): bool =
            (tracked_elt <> list_elt) && (Typ.contains_typ tracked_elt list_elt)
        in
        let traverse_if_valid (acc: bool * (Typ.t list) * CycleTrack.t) (list_elt: Typ.t)
            : bool * (Typ.t list) =
            let (acc_b, acc_typs, tracked) = acc in
            (*if invalid *)
            if (List.exists (in_domain_and_unequal list_elt) tracked) then (
                (false, acc_typs)
            ) else (
                (*if already traversed *)
                if (CycleTrack.is_tracked list_elt tracked) then (
                    (acc_b, acc_typs)
                ) else (
                    (acc_b, 
                    (List.rev_append (dfs_typs list_elt u_results r_results tracked unseen_results) acc_typs))
                )
            )
        in
        let (status, dfs_out, _) = 
            List.fold_left (true, [], tracked) traverse_if_valid ty_ls
        in
        (status, new_hd @ dfs_out)
    )
;;

(*since the final solution contains all references, there is technically no need to dfs; you could just 
replace the solution for all members of the list and call recursive protocol for any recursive types in it
wouldn't be a hard change. just remove calls to resolve_res and wrap calls to the other two in a standard
recursive matching on a list generated from the solution *)
let rec resolve (root: Typ.t) (solution: Typ.unify_result) (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results)
    (tracked: CycleTrack.t): Typ.unify_results * Typ.rec_unify_results =
    let tracked = CycleTrack.track_typ root tracked in
    match root with
    | TNum
    | TBool -> (u_results, r_results)
    | TArrow (ty1, ty2) -> resolve_of_ctr mk_arrow ty1 ty2 solution u_results r_results tracked
    | TProd (ty1, ty2) -> resolve_of_ctr mk_prod ty1 ty2 solution u_results r_results tracked
    | TSum (ty1, ty2) -> resolve_of_ctr mk_sum ty1 ty2 solution u_results r_results tracked
    | THole var -> (
        let u_results = replace_unify_result (var, solution) u_results in
        resolve_res solution
    )
and resolve_of_ctr (ctr: Typ.t -> Typ.t -> Typ.t) (ty1: Typ.t) (ty2: Typ.t) (solution: Typ.unify_result)
    (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results) (tracked: CycleTrack.t)
    : Typ.unify_results * Typ.rec_unify_results =
    let (lhs_res, rhs_res) = split_as_ctr ctr solution in
    let id1 = ty_to_res_id ty1 in
    let id2 = ty_to_res_id ty2 in
    let update_results_by_id (id: TypeInferenceVar.t option * Typ.t option) (res: Typ.unify_result)
        : Typ.unify_results * Typ.rec_unify_results =
        match id with
        | None, None -> (u_results, r_results)
        | (Some var), None -> ((replace_unify_result (var, res) u_results), r_results)
        | None, (Some typ) -> (u_results, (replace_rec_unify_result (typ, res) r_results))
        | _ -> raise Impossible
    in
    (*update results with information for children *)
    let u_results, r_results = update_results_by_id id1 lhs_res in
    let u_results, r_results = resolve_res lhs_res in
    let u_results, r_results = update_results_by_id id2 rhs_res in
    let u_results, r_results = resolve_res rhs_res in
    match (retrieve_result_for_rec_typ root r_results) with
    | Some unif_res -> (
        let r_results = 
            Impl.replace_rec_unify_result ((ctr ty1 ty2), solution) r_results 
        in
        resolve_res solution
    )
    | None -> (u_results, r_results)
(*already following a replaced value; just dfs so other funcs can replace *)
and resolve_res (solution: Typ.unify_result): Typ.unify_results * Typ.rec_unify_results =
    match unif_res with
    (*no holes are present at all *)
    | Solved ty -> (u_results, r_results)
    (*holes present *)
    | Ambiguous (ty_op, ty_ls)
    | UnSolved ty_ls -> (
        let ty_ls = 
            match unify_res with
            | Ambiguous ((Some ty), _) -> ty::ty_ls
            | _ -> ty_ls
        in
        let traverse_if_valid (acc: Typ.unify_results * Typ.rec_unify_results * CycleTrack.t) (list_elt: Typ.t)
            : Typ.unify_results * Typ.rec_unify_results * CycleTrack.t =
            let (acc_u, acc_r, tracked) = acc in
            if (CycleTrack.is_tracked list_elt tracked) then (
                (acc_u, acc_r, tracked)
            ) else (
                resolve list_elt solution u_results r_results tracked
            )
        in
        let (u_results, r_results, _) = 
            List.fold_left (u_results, r_results, tracked) traverse_if_valid ty_ls
        in
        (u_results, r_results)
    )
;;

(* Appends the item to the list only if the item is not consistent with any items in the list *)
let cat_if_inconsistent_for_all (target_list: Typ.t list) (item: Typ.t)
    : Typ.t list =
    if (List.exists (Typ.consistent item) target_list) then (
        target_list
    ) else (
        item::target_list
    )
;;

(* Combines a pair of lists by adding elements from l2 only if they are inconsistent with those currently added/in l1 *)
let smallest_inconsistent_pair (l1: Typ.t list) (l2: Typ.t list)
    : Typ.t list =
    List.fold_left cat_if_inconsistent_for_all l1 l2
;;

let disambiguate (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results)
    : Typ.unify_results * Typ.rec_unify_results =
    let new_u_results = [] in
    let new_r_results = [] in

;;

(*converts all ambiguous statuses to a fully simplified non ambiguous solution status *)
let disambiguate_res (res: Typ.unify_result) (unseen_results: ResTrack.t)
    : Typ.unify_results * Typ.rec_unify_results * ResTrack.t =
;;
let disambiguate_u (u_result: TypeInferenceVar.t * Typ.unify_result) (unseen_results: ResTrack.t)
    : Typ.unify_results * Typ.rec_unify_results * ResTrack.t = 
    let (id, res) = u_result in
    match res with
    | Solved _ -> [u_result], [], (ResTrack.remove_typ (Typ.THole id) unseen_results)
    | Ambiguous (ty_op, children) -> (
        let res' = 
            match ty_op with
            | Some ty -> (Typ.Solved ty)
            | None -> (Typ.Solved THole id)
        in
        let add_res_and_track (acc: Typ.unify_results * ResTrack) (child: Typ.t)
            : Typ.unify_results * Typ.rec_unify_results * ResTrack.t =
            let acc_ls_u, acc_ls_r, unseen_results = acc in
            let unseen_results = ResTrack.remove_typ child unseen_results in
            match child with
            | TNum
            | TBool -> acc
            | THole var -> ((var, res')::acc_ls_u, acc_ls_r, unseen_results)
            | TArrow _
            | TProd _
            | TSum _ -> (acc_ls_u, (child, res')::acc_ls_r, unseen_results)
        in
        List.fold_left add_res_and_track ([], [], unseen_results) (Typ.THole id)::children
    )
    | UnSolved tys -> (
        ([(id, (Typ.UnSolved (smallest_inconsistent_pair [] tys)))], 
        [], 
        (ResTrack.remove_typ (Typ.THole id) unseen_results))
    )
;;

let disambiguate_r (r_result: Typ.t * Typ.unify_result) (unseen_results: ResTrack.t)
    : Typ.unify_results * Typ.rec_unify_results * ResTrack.t = 
    let (r_typ, res) = r_result in
    match res with
    | Solved _ -> [], [r_result], (ResTrack.remove_typ typ unseen_results)
    | Ambiguous (ty_op, children) -> (
        let res' = 
            match ty_op with
            | Some ty -> (Typ.Solved ty)
            | None -> (Typ.Solved r_typ)
        in
        let add_res_and_track (acc: Typ.unify_results * ResTrack) (child: Typ.t)
            : Typ.unify_results * Typ.rec_unify_results * ResTrack.t =
            let acc_ls_u, acc_ls_r, unseen_results = acc in
            let unseen_results = ResTrack.remove_typ child unseen_results in
            match child with
            | TNum
            | TBool -> acc
            | THole var -> ((var, res')::acc_ls_u, acc_ls_r, unseen_results)
            | TArrow _
            | TProd _
            | TSum _ -> (acc_ls_u, (child, res')::acc_ls_r, unseen_results)
        in
        List.fold_left add_res_and_track ([], [], unseen_results) r_typ::children
    )
    | UnSolved tys -> (
        ([], 
        [(r_typ, (Typ.UnSolved (smallest_inconsistent_pair [] tys)))], 
        (ResTrack.remove_typ r_typ unseen_results))
    )
;;

let rec fix_tracked_results (results_to_fix: ResTrack.t) (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results)
    : ResTrack.t * Typ.unify_results * Typ.rec_unify_results =
    match results_to_fix with
    | [] -> results_to_fix, u_results, r_results
    | hd::tl -> (
        let occ, dfs_tys, results_to_fix = dfs_typs hd acc_u acc_r CycleTrack.empty results_to_fix in
        let cycle_res = condense dfs_tys in
        let u_results, r_results = resolve hd cycle_res u_results r_results CycleTrack.empty in
        fix_tracked_results results_to_fix u_results r_results
    )
;;

let finalize_results (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results)
    : Typ.unify_results * Typ.rec_unify_results = 
    let results_to_fix = ResTrack.results_to_t u_results r_results in
    let (_, u_results, r_results) = 
        fix_tracked_results results_to_fix u_results r_results 
    in
    disambiguate u_results r_results
;; 