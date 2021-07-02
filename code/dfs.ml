open Syntax

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

let rec contains_hole (typ: Typ.t): bool =
    match typ with
    | TNum
    | TBool -> false
    | THole _ -> true
    | TArrow(ty1, ty2)
    | TProd(ty1, ty2)
    | TSum(ty1, ty2) -> (contains_hole ty1) || (contains_hole ty2)
;;

let is_literal (typ: Typ.t): bool = (hd = TNum || hd = TBool) ;;

let rec find_literal (typs: Typ.t list): Typ.t option = 
    match typs with
    | [] -> None
    | hd::tl -> if (is_literal hd) then (Some hd) else (find_literal tl)
;;

let simplify (typs: Typ.t list): Typ.unify_result =
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

let fuse_results (ctr: Typ.t -> Typ.t -> Typ.t) (result_ty1: Typ.unify_result) (result_ty2: Typ.unify_result)
    : Typ.unify_result = 
    let mk_ctr_types (ctr: Typ.t -> Typ.t -> Typ.t) (const: Typ.t) (const_is_left: bool) (acc: Typ.t list) (variant: Typ.t)
        : Typ.t list =
        if (const_is_left) then (ctr const variant)::acc else (ctr variant const)::acc
    in
    match (result_ty1, result_ty2) with
    | ((Solved resolved_ty1), (Solved resolved_ty2)) -> Solved (ctr resolved_ty1 resolved_ty2)
    | ((UnSolved tys), (Solved resolved_ty2)) -> UnSolved (List.fold_left (mk_ctr_types ctr resolved_ty2 false) [] tys)
    | ((Solved resolved_ty1), (UnSolved tys)) -> UnSolved (List.fold_left (mk_ctr_types ctr resolved_ty1 true) [] tys)
    | ((UnSolved tys1), (UnSolved tys2)) -> (
        let acc_mk_ctr_types (acc: Typ.t list) (const_of_left: Typ.t): Typ.t list = 
            List.fold_left (mk_ctr_types ctr const_of_left true) acc tys2
        in
        UnSolved (List.fold_left acc_mk_ctr_types [] tys1)
    )
    | ((Solved resolved_ty1), (Ambiguous (ty_op2, ty_ls2))) -> (
        let amb_op = 
            match ty_op2 with
            | Some ty2 -> ctr resolved_ty1 ty2
            | None -> None
        in
        Ambiguous (amb_op, (List.fold_left (mk_ctr_types ctr resolved_ty1 true) [] ty_ls2))
    )
    | ((Ambiguous (ty_op1, ty_ls1)), (Solved resolved_ty2)) -> (
        let amb_op = 
            match ty_op1 with
            | Some ty1 -> ctr ty1 resolved_ty2
            | None -> None
        in
        Ambiguous (amb_op, (List.fold_left (mk_ctr_types ctr resolved_ty2 false) [] ty_ls1))
    )
    | ((UnSolved tys1), (Ambiguous (ty_op2, ty_ls2))) -> (
        let amb_ls = 
            match ty_op2 with
            | Some ty2 -> [ty2]
            | None -> []
        in
        let acc_mk_ctr_types (acc: Typ.t list) (const_of_left: Typ.t): Typ.t list = 
            List.fold_left (mk_ctr_types ctr const_of_left true) acc (amb_ls @ ty_ls2)
        in
        UnSolved (List.fold_left acc_mk_ctr_types [] tys1)
    )
    | ((Ambiguous (ty_op1, ty_ls1)), (UnSolved tys2)) -> (
        let amb_ls = 
            match ty_op1 with
            | Some ty1 -> [ty1]
            | None -> []
        in
        let acc_mk_ctr_types (acc: Typ.t list) (const_of_left: Typ.t): Typ.t list = 
            List.fold_left (mk_ctr_types ctr const_of_left true) acc tys2
        in
        UnSolved (List.fold_left acc_mk_ctr_types [] (amb_ls @ ty_ls1))
    )
    | ((Ambiguous (ty_op1, ty_ls1)), (Ambiguous (ty_op2, ty_ls2))) -> (
        let amb_op = 
            match (ty_op1, ty_op2) with
            | ((Some ty1), (Some ty2)) -> Some (ctr ty1 ty2)
            | _ -> None
        in
        let acc_mk_ctr_types (acc: Typ.t list) (const_of_left: Typ.t): Typ.t list = 
            List.fold_left (mk_ctr_types ctr const_of_left true) acc ty_ls1
        in
        Ambiguous (amb_op, (List.fold_left acc_mk_ctr_types [] ty_ls2))
    )
;;

(*If anything is ambiguous, there is guaranteed to be a cycle. Begin DFS protocol.
    NON REC:
    1) Collect all apparent types and hole structures in the cycle
    2) As you DFS by checking paths not tracked, be sure to also assess if curr_val is
        in domain of tracked vars -> if so, immediate unsolved
    3) Assess them all to generate the status
    4 When generating final solved value, recurse again and update all below with found value
        DO NOT remove and references to holes or rec types. these will be resolved later in case
        the currently assessed cycle is part of a recursive type that could attempt to impose
        further restrictions on it later
    REC:
    1) Evaluate children
    2) Generate resultant type
    3) Recurse on any paths in the rec_unify_results (if present, guaranteed cyclic)
    4) Use returned type to assess additional incurred types for children and generate a modified status
    5) Use other subroutine to update children and their dependencies with the new status
    6) Return final type
    *)
(*New methods needed:
    0) Simplify --> to generate a single type representative of a list or the smallest set thereof
    1) Simplify_and_update --> to change ambiguous statuses to solved and bring all equal hole references to one id
    2) Accumulate cycle types --> to DFS out types in a first pass in ambig/unsolved cases
    3) Adjust status and dependencies --> for updating children of a recursive type *)
let rec dfs_types (root: Typ.t) (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results) 
    (tracked: CycleTrack.t): bool * (Typ.t list) = 
    match root with
    | TNum -> [TNum]
    | TBool -> [TBool]
    | TArrow (ty1, ty2)
    | TProd (ty1, ty2)
    | TSum (ty1, ty2) -> (
        
    )
    | THole var -> (
        match (retrieve_result_for_inf_var var u_results) with
        | Some unif_res -> (
            dfs_res unif_res
        )
        | None -> (
            
        )
    )
and dfs_res (unif_res: Typ.unify_result): bool * (Typ.t list)=
    match unif_res with
    | Solved ty -> (true, [ty])
    | Ambiguous (ty_op, ty_ls)
    | UnSolved ty_ls -> (
        let new_hd = 
            match unify_res with
            | Ambiguous ((Some ty), _) -> [ty]
            | _ -> []
        in
        let tracked = CycleTrack.track root tracked in
        let in_domain_and_unequal (list_elt: Typ.t) (tracked_elt: CycleTrack.t): bool =
            ((Typ.THole tracked_elt) <> list_elt) && (Typ.contains_var tracked_elt list_elt)
        in
        let traverse_if_valid (acc: bool * (Typ.t list) * CycleTrack.t) (list_elt: Typ.t)
            : bool*(Typ.t list) =
            let (acc_b, acc_typs, tracked) = acc in
            if (List.exists (in_domain_and_unequal list_elt) tracked) then (
                (false, acc_typs)
            ) else (
                if (CycleTrack.is_tracked list_elt tracked) then (
                    (acc_b, acc_typs)
                ) else (
                    (acc_b, 
                    (List.rev_append (dfs_types list_elt u_results r_results tracked) acc_typs))
                )
            )
        in
        let (status, dfs_out, _) = 
            List.fold_left (true, [], tracked) traverse_if_valid ty_holes
        in
        (status, new_hd @ dfs_out)
    )
and dfs_two_of_ctr (ctr: Typ.t -> Typ.t -> Typ.t) (ty1: Typ.t) (ty2: Typ.t) 
    (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results) (tracked: CycleTrack.t)
    : bool * (Typ.t list) =
    (*
    1) Evaluate children
    2) Generate resultant type
    3) Recurse on any paths in the rec_unify_results (if present, guaranteed cyclic)
    4) Use returned type to assess additional incurred types for children and generate a modified status
    5) Use other subroutine to update children and their dependencies with the new status
    6) Return final type
    or just like not and this instead:
    3) Recurse on any paths in the rec_unify_results (if present, guaranteed cyclic)
    4) Use returned type to assess additional incurred types for children
    5) solve the children while enforcing that they match they required types
    *)
    let (occ1, ty1_res) = dfs_types ty1 u_results r_results in
    let (occ2, ty2_res) = dfs_types ty2 u_results r_results in
    let (ty1_res, ty2_res) = ((simplify ty1_res), (simplify ty2_res)) in
    
    match (retrieve_result_for_rec_typ root r_results) with
    | Some unif_res -> (
        let occ, dfs_ls = dfs_res unif_res in
        let new_res = simplify dfs_ls in
        let (lhs_res, rhs_res) = split_as_ctr ctr new_res in
        let (u_results, r_results) = 
        (*match on children's types and add the new results as applicable *)
        (*remerge types according to semantics above*)
    )
    | None -> (

    )
and enforce_res (typ: Typ.t) (res: Typ.unify_result) (u_results: Typ.unify_results) 
    (r_results: Typ.rec_unify_results): bool * result_update =

;;

let rec enforce_res (res: Typ.unify_result) (typ: Typ.t) (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results)
    : result_update =
    match typ with
    | TNum
    | TBool -> if (typ )
    | THole
    | TArrow
    | TProd
    | TSum ->
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
    let is_of_struc, outliers = all_of_ctr ctr ty_ls in
    let lhs_tys, rhs_tys = split_ls ty_ls in
    if (is_of_struc) then (
        ((simplify lhs_tys), (simplify rhs_tys))
    ) else (
        (*NOTE! Currently, this will not note why things are unsolved if fitting in this case
            ex: Num used as arrow, sum used as arrow, etc
        For now, it will simply be written as unsolved of a set of potentially consistent types. 
        later, we can add error statuses*)
        let lhs_tys, rhs_tys = 
            (List.rev_append outliers lhs_tys), (List.rev_append outliers rhs_tys)
        in
        ((UnSolved lhs_tys), (UnSolved rhs_tys))
    )
;;