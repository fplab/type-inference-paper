open Syntax

(* Restrack serves as a means to track which types have been dfsed and resolved.  
    the dep_list feature acts to maintain a path compressed set of dependencies
    so that if an update to some child, its uppermost dependency is flagged for reevaluation
    by reinsertion to the restrack*)
module ResTrack = struct
    type t = Typ.t list

    (* types, their most known dependent, and whether they've already been re-added *)
    type dep_list = (Typ.t * (Typ.t list) * bool) list

    (*gets rid of a typ from the list *)
    let rec remove_typ (typ: Typ.t) (ls: t): t =
        match ls with
        | [] -> []
        | hd::tl -> if (hd = typ) then (tl) else (hd::(remove_typ typ tl))
    ;;

    let rec add_dep (deps: Typ.t list) (dep: Typ.t): Typ.t list =
        match deps with
        | [] -> [dep]
        | hd::tl -> if (hd = dep) then deps else (hd::(add_dep tl dep))
    ;;

    let add_typ_with_deps (typ: Typ.t) (deps: Typ.t list) (ls: dep_list): dep_list =
        let rec update_or_insert (ls: dep_list): dep_list =
            match ls with
            | [] -> [(typ, deps, false)]
            | hd::tl -> (
                let (key, ls, _) = hd in
                if (key = typ) then 
                    ((typ, (List.fold_left add_dep ls deps), false)::tl) 
                else 
                    (hd::(update_or_insert tl))
            )
        in
        update_or_insert ls
    ;;

    (*generates a list of the types involved in unify results. recursive results first *)
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

    let r_results_to_dep_list (r_results: Typ.rec_unify_results): dep_list =
        let r_results_to_t (r_results: Typ.rec_unify_results): Typ.t list =
            let extend_by_r_res (acc: t) (r_res: Typ.t * Typ.unify_result): Typ.t list =
                let (r_typ, _) = r_res in
                r_typ::acc
            in
            List.fold_left extend_by_r_res [] r_results
        in
        let ls_r = r_results_to_t r_results in
        let rec acc_deps (acc: dep_list) (typ: Typ.t): dep_list =
            match typ with
            | TArrow (ty1, ty2)
            | TProd (ty1, ty2)
            | TSum (ty1, ty2) -> (
                let acc = add_typ_with_deps ty1 [typ] acc in
                let acc = add_typ_with_deps ty2 [typ] acc in
                let acc = acc_deps acc ty1 in
                acc_deps acc ty2
            )
            | _ -> acc
        in
        List.fold_left acc_deps [] ls_r
    ;;

    let rec remove_and_inform (pred: 'a -> bool) (ls: 'a list): ('a option) * 'a list =
        match ls with
        | [] -> (None, [])
        | hd::tl -> (
            if (pred hd) then ((Some hd), tl) 
            else (
                let (ext, tl) = remove_and_inform pred tl in
                (ext, hd::tl)
            )
        ) 
    ;;

    let rec find_uppermost_dep (key: Typ.t) (deps: dep_list): dep_list * (Typ.t list) * bool =
        let (removed, deps) = remove_and_inform (fun (x,_, _) -> (x = key)) deps in
        (*if nothing was removed, return self *)
        match removed with
        | None -> (deps, [key], true)
        | Some (_, rvalues, already_reseen) -> (
            (*follow the types and accumulate the updates deps lists and returned types; *)
            let follow (acc: dep_list * (Typ.t list) * bool) (ty: Typ.t): dep_list * (Typ.t list) * bool =
                let (acc_deps, acc_tys, acc_bool) = acc in
                let (new_deps, uppers, upper_already_reseen) =
                    find_uppermost_dep ty acc_deps
                in
                (new_deps, (List.rev_append uppers acc_tys), already_reseen && acc_bool && upper_already_reseen)
            in
            let (new_deps, new_tys, reseen_done) =
                List.fold_left follow (deps, [], true) rvalues
            in
            ((key, new_tys, true)::new_deps, new_tys, reseen_done)
        )
    ;;

    let update_unseens_after_typ (typ: Typ.t) (deps: dep_list) (unseen_results: t)
        : dep_list * t =
        let (new_deps, to_be_reseen, already_reseen) = find_uppermost_dep typ deps in
        let updated_unseens = 
            if (already_reseen) then unseen_results else (unseen_results @ to_be_reseen)
        in
        (new_deps, updated_unseens)
    ;;
end

(*  In general, cycletrack serves as a basic tracker for things found while dfsing; this can be to prevent loops,
as in the case of 'tracked' in dfs, or to keep a list of the current equivalence class in the cycle, in eq_class of dfs.
Notably, the two uses mentioned above are different due to recursive type handling. *)
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

(******************************************************)
(*  UTILITIES FOR DEBUGGING COPIED FROM UTIL.ML START *)
(******************************************************)

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

let rec string_of_typ_gens (gen: TypGen.typ_gens) =
    match gen with
    | [] -> "\n"
    | hd::[] -> (string_of_typ_gen hd);
    | hd::tl -> (
        let hd_str = string_of_typ_gen hd in
        (hd_str ^ "//" ^ (string_of_typ_gens tl));
    )
and string_of_typ_gen (gen_elt: TypGen.typ_gen) =
    match gen_elt with
    | Base btyp -> (string_of_typ (TypGen.base_typ_to_typ btyp));
    | Compound (ctr, gens1, gens2) -> (
        let str1 = string_of_typ_gens gens1 in
        let str2 = string_of_typ_gens gens2 in
        let ctr_str = 
            match ctr with
            | Arrow -> "Arrow"
            | Prod -> "Prod"
            | Sum -> "Sum"
        in
        ("(" ^ ctr_str ^ " ({" ^ str1 ^ "}, " ^ "{" ^ str2 ^ "}))");
    )
;;

let rec string_of_gen_res (gen_results: TypGenRes.results) =
    match gen_results with
    | [] -> "\n";
    | hd::tl -> (
        let (key, res) = hd in
        let hd_str = 
            (string_of_typ key) ^ " ls: " ^ (string_of_typ_gens res) ^ "\n"
        in
        hd_str ^ (string_of_gen_res tl)
    )
;;

let rec string_of_solutions (sol: Status.solution list) =
    match sol with
    | [] -> "\n";
    | hd::tl -> (
        let (key, res) = hd in
        let hd_str =
            match res with
            | Solved typ -> ("solved: (" ^ string_of_typ(key) ^ ") - " ^ string_of_typ(typ) ^ "\n");
            | UnSolved gens -> (
            ("unsolved: (" ^ string_of_typ(key) ^ ") - " ^ string_of_typ_gens(gens) ^ "\n");
            )
        in
        hd_str ^ (string_of_solutions tl)
    )
;;


let rec string_of_blist (blist: Blacklist.t) = 
    match blist with
    | [] -> "\n";
    | hd::tl -> (
        let (key, err) = hd in
        let err_str =
            match err with
            | Invalid -> "INVALID"
            | Occurs -> "OCCURS"
        in
        let hd_str =
            (string_of_typ key) ^ " with err " ^ err_str ^ ";\n"
        in
        hd_str ^ (string_of_blist tl)
    )
;;

let rec string_of_dep_list (deps: ResTrack.dep_list) = 
    match deps with
    | [] -> "\n";
    | hd::tl -> (
        let (key, ty_ls, seen) = hd in
        let hd_str = 
            (string_of_typ key) ^ " has deps: " ^ (string_of_typ_ls ty_ls) ^ 
           (if (seen) then "and HAS been reseen" else "and HASN'T been reseen") ^
            "\n"
        in
        hd_str ^ (string_of_dep_list tl)
    )

;;

(******************************************************)
(*  UTILITIES FOR DEBUGGING COPIED FROM UTIL.ML END *)
(******************************************************)

(*extends u results to include all holes contained within r results
    logic: if in an r result, it technically is truly used as a hole with some potential result
            and needs to be able to be referenced in later values and be made 'explorable'.
            see "TypGenRes.explorable_list" in syntax.ml*)
let add_all_refs_as_results (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results)
    : Typ.unify_results * Typ.rec_unify_results =
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

(* DOCUMENTATION *)
(* PURPOSE: a method that dfs's on a type to accumulate all known types it is cyclic with in gen_results*)
(* DETAILS:
    - root is the node from which dfsing will start
    - gen_results represents the tree to dfs
    - tracked acts as a means to track which branches have been explored. 
    - eq_class acts to track all values in equivalence class with the current dfs
    - unseen_results acts to track the currently uncompleted types
*)
(* RETURNS:
    - a typ_gens representing the dfs types
    - the currently tracked values passed in dfs
    - the currently known equivalence class of the root; technically redundany given the typ_gens
    - the values remaining in the supplied restrack that remain undfsed (thus being an ancestor or disjoint)
    - an updated gen_results tree, relinked as dfs_typs saw fit
among these, the only ones useful for programmers is the typ_gens return value; the rest are for recursive bookkeeping
*)
let rec dfs_typs (root: Typ.t) (gen_results: TypGenRes.results) (tracked: CycleTrack.t) (eq_class: CycleTrack.t) 
    (unseen_results: ResTrack.t) (deps: ResTrack.dep_list)
    : TypGen.typ_gens * CycleTrack.t * CycleTrack.t * ResTrack.t * Blacklist.t * TypGenRes.results *  ResTrack.dep_list =
    (*update the tracking mechanisms *)
    let tracked = CycleTrack.track_typ root tracked in
    let eq_class = CycleTrack.track_typ root eq_class in

    (*perform a dfs as necessitated by the shape of the root and store the updated parameters *)
    let (dfs_all, tracked, eq_class, unseen_results, blist, gen_results, deps) = 
        match root with
        | TNum -> ([], tracked, eq_class, unseen_results, [], gen_results, deps)
        | TBool -> ([], tracked, eq_class, unseen_results, [], gen_results, deps)
        | TArrow (ty1, ty2) -> dfs_typs_of_ctr Signature.Arrow ty1 ty2 gen_results tracked eq_class unseen_results deps
        | TProd (ty1, ty2) -> dfs_typs_of_ctr Signature.Prod ty1 ty2 gen_results tracked eq_class unseen_results deps
        | TSum (ty1, ty2) -> dfs_typs_of_ctr Signature.Sum ty1 ty2 gen_results tracked eq_class unseen_results deps
        | THole _ -> (
            match (TypGenRes.retrieve_gens_for_typ root gen_results) with
            | Some gens -> (dfs_typs_gen gens gen_results tracked eq_class unseen_results deps)
            | None -> ([], tracked, eq_class, unseen_results, [], gen_results, deps)
        )
    in
    
    (*return the previous parameters after updating the dfs types to inclue to root *)
    let (deps, unseen_results) = ResTrack.update_unseens_after_typ root deps unseen_results in
    let unseen_results = ResTrack.remove_typ root unseen_results in
    ((TypGen.extend_with_typ dfs_all root), tracked, eq_class, unseen_results, blist, gen_results, deps)

(* PURPOSE: Given a recursive type constructed via 'ctr' with lhs 'ty1' and rhs 'ty2', performs a dfs *)
and dfs_typs_of_ctr (ctr: Signature.ctr) (ty1: Typ.t) (ty2: Typ.t) (gen_results: TypGenRes.results) 
    (tracked: CycleTrack.t) (eq_class: CycleTrack.t) (unseen_results: ResTrack.t) (deps: ResTrack.dep_list)
    : TypGen.typ_gens * CycleTrack.t * CycleTrack.t * ResTrack.t * Blacklist.t * TypGenRes.results * ResTrack.dep_list =
    (* create the type represented by the arguments *)
    let rec_ty = ((Signature.get_mk_of_ctr ctr) ty1 ty2) in
    (*perform an incorrect dfs of the recursive type's equivalence class to generate a list of info to
    impart to children so that their dfs's will be as correct as possible *)
    let (tys_u, uptrack, _, _, _, gen_results, deps) =
        match (TypGenRes.retrieve_gens_for_typ rec_ty gen_results) with
        | Some gens -> dfs_typs_gen gens gen_results tracked eq_class unseen_results deps
        | None -> ([], [], [], [], [], gen_results, deps)
    in
    let (_, lhs_tys, rhs_tys) = TypGen.split ctr tys_u in
    let gen_results = TypGenRes.link_typ_to_gen ty1 lhs_tys gen_results in
    let gen_results = TypGenRes.link_typ_to_gen ty2 rhs_tys gen_results in
    let (_, _, _, unseen_results, _, gen_results, deps) = 
        dfs_typs ty1 gen_results uptrack [] unseen_results deps
    in
    let (ty2_gens, _, _, unseen_results, blist2, gen_results, deps) = 
        dfs_typs ty2 gen_results uptrack [] unseen_results deps
    in
    let (ty1_gens, _, _, unseen_results, blist1, gen_results, deps) = 
        dfs_typs ty1 gen_results uptrack [] unseen_results deps
    in
    let rec_tys_gen = TypGen.fuse ctr ty1_gens ty2_gens in
    let (dfs_tys, tracked, eq_class, unseen_results, blist3, gen_results, deps) = 
        match (TypGenRes.retrieve_gens_for_typ rec_ty gen_results) with
        | Some gens -> dfs_typs_gen gens gen_results tracked eq_class unseen_results deps
        | None -> ([], tracked, eq_class, unseen_results, [], gen_results, deps)
    in
    let new_gens = TypGen.extend_with_gen dfs_tys rec_tys_gen in
    let final_blist = Blacklist.merge_blists [blist1; blist2; blist3;] in
    (new_gens, tracked, eq_class, unseen_results, final_blist, gen_results, deps)
and dfs_typs_gen (gens: TypGen.typ_gens) (gen_results: TypGenRes.results) (tracked: CycleTrack.t) (eq_class: CycleTrack.t)
    (unseen_results: ResTrack.t) (deps: ResTrack.dep_list)
    : TypGen.typ_gens * CycleTrack.t * CycleTrack.t * ResTrack.t * Blacklist.t * TypGenRes.results * ResTrack.dep_list =
    let destinations = TypGenRes.explorable_list gens gen_results in
    let in_domain_and_unequal (list_elt: Typ.t) (eq_elt: Typ.t): bool =
        (eq_elt <> list_elt) && ((Typ.contains_typ eq_elt list_elt) || (Typ.contains_typ list_elt eq_elt))
    in
    let traverse_if_valid (acc: TypGen.typ_gens * CycleTrack.t * CycleTrack.t * ResTrack.t * Blacklist.t * TypGenRes.results * ResTrack.dep_list) 
        (list_elt: Typ.t)
        : TypGen.typ_gens * CycleTrack.t * CycleTrack.t * ResTrack.t * Blacklist.t * TypGenRes.results * ResTrack.dep_list =
        let (acc_typs, tracked, eq_class, unseen_results, acc_blist, acc_res, deps) = acc in
        (*if invalid *)
        let occ_fail_opt = List.find_opt (in_domain_and_unequal list_elt) eq_class in
        match occ_fail_opt with
        | Some occ_fail_elt -> (
            let acc_blist = Blacklist.add_elt acc_blist (occ_fail_elt, Occurs) in
            let acc_blist = Blacklist.add_elt acc_blist (list_elt, Occurs) in
            (acc_typs, tracked, eq_class, unseen_results, acc_blist, acc_res, deps)
        )
        | None -> (
            (*if already traversed *)
            if (CycleTrack.is_tracked list_elt tracked) then (
                (acc_typs, tracked, eq_class, unseen_results, acc_blist, acc_res, deps)
            ) else (
                let (dfs_all, tracked, eq_class, unseen_results, new_blist, acc_res, deps) = 
                    dfs_typs list_elt acc_res tracked eq_class unseen_results deps
                in
                let acc_blist = Blacklist.merge_blists [acc_blist; new_blist] in
                ((TypGen.extend_with_gens acc_typs dfs_all),
                tracked,
                eq_class,
                unseen_results,
                acc_blist,
                acc_res,
                deps)
            )
        )
    in
    let (typs, tracked, eq_class, unseen_results, blist, gen_results, deps) =
        List.fold_left traverse_if_valid ([], tracked, eq_class, unseen_results, [], gen_results, deps) destinations
    in
    (*combine explored results with those already known that weren't giving more info than present. *)
    let original_with_dfs_typs = 
        TypGen.extend_with_gens gens typs
    in
    (original_with_dfs_typs, tracked, eq_class, unseen_results, blist, gen_results, deps)
;;

(*since the final solution contains all references, there is technically no need to dfs; you could just 
replace the solution for all members of the list and call recursive protocol for any recursive types in it
wouldn't be a hard change. just remove calls to resolve_res and wrap calls to the other two in a standard
recursive matching on a list generated from the solution *)
(*
    the sol occ associated with the top would theoretically apply to all values in the loop; if ever a child were to have been involved
    in some occurs check issue, its implicit evaluation upon dfsing the parent should imbue the top sol_occ as false as well.
    thus, it cannot be that case that a child the parent depends on be sol_occ false without the parent being so too. 
    however, can a child be non sol_occ when its parent is so?
 *)
let rec resolve (root: Typ.t) (solution: TypGen.typ_gens) (gen_results: TypGenRes.results) (tracked: CycleTrack.t)
    : TypGenRes.results * CycleTrack.t * Blacklist.t =
    let tracked = CycleTrack.track_typ root tracked in
    match root with
    | TNum
    | TBool -> (gen_results, tracked, [])
    | TArrow (ty1, ty2) -> resolve_of_ctr Signature.Arrow ty1 ty2 solution gen_results tracked
    | TProd (ty1, ty2) -> resolve_of_ctr Signature.Prod ty1 ty2 solution gen_results tracked
    | TSum (ty1, ty2) -> resolve_of_ctr Signature.Sum ty1 ty2 solution gen_results tracked
    | THole _ -> (
        let (gen_results, tracked, blist) = resolve_typ_gens solution gen_results tracked in
        let gen_results = TypGenRes.replace_gens_of_typ root solution gen_results in
        (gen_results, tracked, blist)
    )
and resolve_of_ctr (ctr: Signature.ctr) (ty1: Typ.t) (ty2: Typ.t) (solution: TypGen.typ_gens) (gen_results: TypGenRes.results) 
    (tracked: CycleTrack.t): TypGenRes.results * CycleTrack.t * Blacklist.t =
    let (split_res, lhs_tys, rhs_tys) = TypGen.split ctr solution in
    let rec_ty = ((Signature.get_mk_of_ctr ctr) ty1 ty2) in
    let new_blist: Blacklist.t =
        match split_res with
        | Success -> []
        | Fail f_stat -> (
            (*if simply an inconsistency in ctrs, only the rec typ eq class is invalid; 
            if a use of a rec as a base type, then all elts of the rec are invalid *)
            match f_stat with
            | Ctr_fail -> [(rec_ty, Invalid);]
            | _ -> (
                let rec typ_to_typ_ls (typ: Typ.t): Typ.t list =
                    match typ with
                    | TArrow (ty1, ty2)
                    | TProd (ty1, ty2)
                    | TSum (ty1, ty2) -> (typ_to_typ_ls ty1) @ (typ_to_typ_ls ty2)
                    | _ -> [typ]
                in
                let ty_ls = typ_to_typ_ls rec_ty in
                List.rev_map (fun (x: Typ.t): (Typ.t * Blacklist.err)  -> (x, Invalid)) ty_ls
            )
        )
    in
    (*no need to generate new type results since dfs should already have traversed this and constructed the necessary ones *)
    (*update results with information for children *)
    let (gen_results, tracked, blist1) = resolve_typ_gens lhs_tys gen_results tracked in
    let gen_results = TypGenRes.replace_gens_of_typ ty1 lhs_tys gen_results in
    let (gen_results, tracked, blist2) = resolve_typ_gens rhs_tys gen_results tracked in
    let gen_results = TypGenRes.replace_gens_of_typ ty2 rhs_tys gen_results in
    match (TypGenRes.retrieve_gens_for_typ ((Signature.get_mk_of_ctr ctr) ty1 ty2) gen_results) with
    | Some _ -> (
        let (gen_results, tracked, blist3) = resolve_typ_gens solution gen_results tracked in
        let gen_results  = 
            TypGenRes.replace_gens_of_typ ((Signature.get_mk_of_ctr ctr) ty1 ty2) solution gen_results
        in
        let final_blist = Blacklist.merge_blists [blist1; blist2; blist3; new_blist;] in
        (gen_results, tracked, final_blist)
    )
    | None -> (gen_results, tracked, (Blacklist.merge_blists [blist1; blist2; new_blist;]))
(*already following a replaced value; just dfs so other funcs can replace *)
and resolve_typ_gens (solution: TypGen.typ_gens) (gen_results: TypGenRes.results) (tracked: CycleTrack.t)
    : TypGenRes.results * CycleTrack.t * Blacklist.t =
    let ty_ls = TypGenRes.explorable_list solution gen_results in
    let traverse_if_valid (acc: TypGenRes.results * CycleTrack.t * Blacklist.t) (list_elt: Typ.t)
        : TypGenRes.results * CycleTrack.t * Blacklist.t =
        let (acc_res, tracked, acc_blist) = acc in
        if (CycleTrack.is_tracked list_elt tracked) then (
            (acc_res, tracked, acc_blist)
        ) else (
            resolve list_elt solution acc_res tracked
        )
    in
    List.fold_left traverse_if_valid (gen_results, tracked, []) ty_ls
;;

let rec gen_to_status (gen_results: TypGenRes.results) (blist: Blacklist.t): Status.solution list =
    match gen_results with
    | [] -> []
    | hd::tl -> (
        let (hd_key, hd_val) = hd in
        let stat_of_key = Status.condense hd_val blist in
        (hd_key, stat_of_key)::(gen_to_status tl blist)
    )
;;

let rec fix_tracked_results (results_to_fix: ResTrack.t) (gen_results: TypGenRes.results) (blist: Blacklist.t) (deps: ResTrack.dep_list)
    : ResTrack.t * TypGenRes.results * Blacklist.t * ResTrack.dep_list =
    match results_to_fix with
    | [] -> results_to_fix, gen_results, blist, deps
    | hd::_ -> (
        let (dfs_tys, _, _, results_to_fix, blist_occ, gen_results, deps) = 
            dfs_typs hd gen_results CycleTrack.empty CycleTrack.empty results_to_fix deps
        in
        Printf.printf "%s\n" (string_of_typ_ls results_to_fix);
        Printf.printf "%s\n" (string_of_dep_list deps);
        let (gen_results, _, blist_shape) = resolve hd dfs_tys gen_results CycleTrack.empty in
        let merged_blist = (Blacklist.merge_blists [blist; blist_occ; blist_shape;]) in
        fix_tracked_results results_to_fix gen_results merged_blist deps
    )
;;

let finalize_results (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results)
    : Status.solution list = 
    let (u_results, r_results) = 
        add_all_refs_as_results u_results r_results
    in
    let gen_results = TypGenRes.unif_results_to_gen_results u_results r_results in
    let results_to_fix = ResTrack.results_to_t u_results r_results in
    let deps = ResTrack.r_results_to_dep_list r_results in
    let (_, gen_results, blacklist, _) = 
        fix_tracked_results results_to_fix gen_results [] deps
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
    let comp_status (stat1: Status.solution) (stat2: Status.solution)
        : int =
        let (ty1, _) = stat1 in
        let (ty2, _) = stat2 in
        let id1 = extract_leftmost ty1 in
        let id2 = extract_leftmost ty2 in
        Stdlib.compare id1 id2
    in
    let solutions = gen_to_status gen_results blacklist in
    List.fast_sort comp_status solutions
;; 