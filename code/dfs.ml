open Syntax

(* Restrack serves as a means to track which types have been dfsed and resolved.  
    the dep_list feature acts to maintain a path-compressed set of dependencies
    so that if an update to some child occurs, its uppermost dependency is flagged for reevaluation
    by reinsertion to the restrack if not already in the list of types to be evaluated
    
    a type need only be reevaluated once if done after all types initially in unseen results are evaluated.
    if a type is already inside unseen results, it is pending computation or currently being computed and thus
    need not be recomputed*)
module ResTrack = struct
    (*a type with a bool representing if it has been 'reseen' or not (which prevents excess recomputation) *)
    type t = (Typ.t * bool) list

    (* types, their most known dependent, and whether they've already been re-added *)
    type dep_list = (Typ.t * (Typ.t list) * bool) list

    (*gets rid of a typ from the list *)
    let rec remove_typ (typ: Typ.t) (ls: t): t =
        match ls with
        | [] -> []
        | (hd, c)::tl -> if (hd = typ) then (tl) else ((hd, c)::(remove_typ typ tl))
    ;;

    (*helper function to add a typ if not already present *)
    let rec add_dep (deps: Typ.t list) (dep: Typ.t): Typ.t list =
        match deps with
        | [] -> [dep]
        | hd::tl -> if (hd = dep) then deps else (hd::(add_dep tl dep))
    ;;

    (*adds typ with dependencies deps to the supplied dep_list *)
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
    (* let results_to_t (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results): t =
        let u_results_to_t (u_results: Typ.unify_results): t =
            let extend_by_u_res (acc: t) (u_res: TypeInferenceVar.t * Typ.unify_result): t =
                let (u_var, _) = u_res in
                ((Typ.THole u_var), true)::acc
            in
            List.fold_left extend_by_u_res [] u_results
        in
        let r_results_to_t (r_results: Typ.rec_unify_results): t =
            let extend_by_r_res (acc: t) (r_res: Typ.t * Typ.unify_result): t =
                let (r_typ, _) = r_res in
                (r_typ, true)::acc
            in
            List.fold_left extend_by_r_res [] r_results
        in
        let ls_u = u_results_to_t u_results in
        let ls_r = r_results_to_t r_results in
        List.rev_append ls_r ls_u
    ;; *)
    let results_to_t (gen_results: TypGenRes.results): t =
        let extend_by_gen_res (acc_t: t) ((key, _): TypGenRes.t): t =
            (key, true)::acc_t
        in
        List.fold_left extend_by_gen_res [] gen_results
    ;;

    (*generates a list of dependencies given rec unify results *)
    (* let r_results_to_dep_list (r_results: Typ.rec_unify_results): dep_list =
        let r_results_to_t (r_results: Typ.rec_unify_results): Typ.t list =
            let extend_by_r_res (acc: Typ.t list) (r_res: Typ.t * Typ.unify_result): Typ.t list =
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
                let acc = add_typ_with_deps typ [] acc in
                let acc = add_typ_with_deps ty1 [typ] acc in
                let acc = add_typ_with_deps ty2 [typ] acc in
                let acc = acc_deps acc ty1 in
                acc_deps acc ty2
            )
            | _ -> acc
        in
        List.fold_left acc_deps [] ls_r
    ;; *)

    let r_results_to_dep_list (gen_results: TypGenRes.results): dep_list =
        let r_results_to_t (gen_results: TypGenRes.results): Typ.t list =
            let extend_by_r_res (acc: Typ.t list) ((key, _): TypGenRes.t): Typ.t list =
                match key with
                | TArrow _
                | TProd _ 
                | TSum _ -> key::acc
                | _ -> acc
            in
            List.fold_left extend_by_r_res [] gen_results
        in
        let ls_r = r_results_to_t gen_results in
        let rec acc_deps (acc: dep_list) (typ: Typ.t): dep_list =
            match typ with
            | TArrow (ty1, ty2)
            | TProd (ty1, ty2)
            | TSum (ty1, ty2) -> (
                let acc = add_typ_with_deps typ [] acc in
                let acc = add_typ_with_deps ty1 [typ] acc in
                let acc = add_typ_with_deps ty2 [typ] acc in
                let acc = acc_deps acc ty1 in
                acc_deps acc ty2
            )
            | _ -> acc
        in
        List.fold_left acc_deps [] ls_r
    ;;

    (* removes the first element that satifies pred from the list and returns it along with the adjusted list
        if no such element exists, None is returned with the list *)
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

    (*a method to find the most dependent nodes associated with a key in a list of dependencies
        uses path compression- returned dep_list has been compressed
        the type list returned is the type list that must be reseen *)
    let rec find_uppermost_dep (key: Typ.t) (deps: dep_list): dep_list * (Typ.t list) =
        (* see if the inputted type has any dependencies *)
        let (removed, deps) = remove_and_inform (fun (x,_, _) -> (x = key)) deps in
        (* if nothing was removed, return self *)
        match removed with
        | None -> (deps, [])
        | Some (_, rvalues, already_reseen) -> (
            (*first, check if this node has already been evaluated; if so, no need to re-add its dependents *)
            if (already_reseen) then (
                ((key, rvalues, already_reseen)::deps, [])
            ) else (
                (*if not,  check if it has any known dependents to explore; if not, it is final and should be returned*)
                match rvalues with
                | [] -> ((key, [], already_reseen)::deps, [key])
                | _ -> (
                    (*if dependencies exist,
                    follow the types and accumulate the updates deps lists and returned types; *)
                    let follow (acc: dep_list * (Typ.t list)) (ty: Typ.t): dep_list * (Typ.t list) =
                        let (acc_deps, acc_tys) = acc in
                        let (new_deps, uppers) =
                            find_uppermost_dep ty acc_deps
                        in
                        (new_deps, (List.rev_append uppers acc_tys))
                    in
                    let (new_deps, new_tys) =
                        List.fold_left follow (deps, []) rvalues
                    in
                    (*compress the key's path and mark it as reseen; return associated types *)
                    ((key, new_tys, already_reseen)::new_deps, new_tys)
                )
            )
        )
    ;;

    (*based on the 'reseen' status of the result, updates unseen_results and updates reseen status *)
    let rec extend_unseen_with_rep (rep: Typ.t) (unseen_results: t) (deps: dep_list): dep_list * t =
        match deps with
        | [] -> [], unseen_results
        | hd::tl -> (
            let (hd_key, hd_vals, hd_reseen) = hd in
            if (hd_key = rep) then (
                (* If the hd has already been reseen, we don't need to extend; return as is*)
                if (hd_reseen) then (
                    deps, unseen_results
                ) else (
                    (* If it hasn't been reseen, add it to unseen results with an reseen status of false
                      to indicate it must be dfsed again *)
                    ((hd_key, hd_vals, true)::tl), (unseen_results @ [(rep, false)])
                )
            ) else (
                let (new_deps, unseens_results) = extend_unseen_with_rep rep unseen_results tl in
                hd::new_deps, unseens_results
            )
        )
    ;;

    (*updates the unseen results after the given type has been evaluated given deps *)
    let update_unseens_after_typ (typ: Typ.t) (deps: dep_list) (unseen_results: t)
        : dep_list * t =
        (*get representatives *)
        let (new_deps, representatives) = find_uppermost_dep typ deps in
        let assess_rep (acc_dep, acc_res: dep_list * t) (rep: Typ.t): dep_list * t =
            (*if it already exists as an unseen, there is no need to add it; status quo *)
            if (List.exists (fun (x, _) -> x = rep) unseen_results) then (
                (acc_dep, acc_res)
            ) else (
                (* if it doesn't exist already, extend unseen as appropriate given this representative's
                 previous 'reseen' history *)
                extend_unseen_with_rep rep acc_res acc_dep
            )
        in
        List.fold_left assess_rep (new_deps, unseen_results) representatives
    ;;
end

(*  In general, cycletrack serves as a basic tracker for things found while dfsing; this can be to prevent loops,
as in the case of 'tracked' in dfs, or to keep a list of the current equivalence class in the cycle, in eq_class of dfs.
Notably, the two uses mentioned above are different due to recursive type handling. *)
module CycleTrack = struct
    type t = Typ.t list

    let empty : t = [];;

    (*adds a type to the tracker *)
    let track_typ (typ: Typ.t) (typs: t): t =
        typ::typs
    ;;

    (*checks if a type is tracked within the tracker *)
    let is_tracked (typ: Typ.t) (typs: t): bool =
        let is_typ (scrut: Typ.t): bool =
            typ = scrut
        in
        List.exists is_typ typs
    ;;
end

(***********************************)
(*  UTILITIES FOR DEBUGGING START  *)
(***********************************)

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

let rec string_of_restrack (unseen: ResTrack.t) =
    match unseen with
    | [] -> " "
    | (hd, _)::tl -> 
        (string_of_typ hd)^ ", " ^ (string_of_restrack tl);
;;

(*********************************)
(*  UTILITIES FOR DEBUGGING END  *)
(*********************************)

(*extends u results to include all holes contained within r results
    logic: if in an r result, it technically is truly used as a hole with some potential result
            and needs to be able to be referenced in later values and be made 'explorable'.
            see "TypGenRes.explorable_list" in syntax.ml*)
let add_all_refs_as_results (gen_results: TypGenRes.results): TypGenRes.results =
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
    (*converts the list of gen results to recursive types*)
    let r_res_to_typ (acc: Typ.t list) (res: TypGenRes.t): Typ.t list =
        let (r_typ, _) = res in
        match r_typ with
        | TArrow _
        | TProd _
        | TSum _ -> r_typ::acc
        | _ -> acc
    in
    let keysOfRecTyps = List.fold_left r_res_to_typ [] gen_results in
    let var_ls = List.fold_left acc_rec_holes [] keysOfRecTyps in
    (*extends gen results with the accumulated types to be solved as self for referencing *)
    let extend_gen_results (acc_updated_results: TypGenRes.results) (var: TypeInferenceVar.t): TypGenRes.results =
        let assoc_typ_gens = TypGen.extend_with_typ [] (THole var) in
        TypGenRes.gen_results_set_add_one ((THole var), assoc_typ_gens) acc_updated_results
    in
    List.fold_left extend_gen_results gen_results var_ls
;;

(* DFS DOCUMENTATION *)
(* PURPOSE: a method that dfs's on a type to accumulate all known types it is cyclic with in gen_results*)
(* DETAILS:
    - root is the node from which dfsing will start
    - gen_results represents the tree to dfs
    - tracked acts as a means to track which branches have been explored. 
    - eq_class acts to track all values in equivalence class with the current dfs
    - unseen_results acts to track the currently uncompleted types
    - deps carries any dependencies between types necessary for some recomputation processes
    - updateable indicates if the unseen results should be extended by the current assessment
*)
(* RETURNS:
    - a typ_gens representing the dfs types
    - the currently tracked values passed in dfs
    - the currently known equivalence class of the root; technically redundany given the typ_gens
    - the values remaining in the supplied restrack that remain undfsed (thus being an ancestor or disjoint)
    - an updated gen_results tree, relinked as dfs_typs saw fit
    - and updated potentially "path compressed/reseen status updated" dep_list
among these, the only ones useful for programmers is the typ_gens return value; the rest are for recursive bookkeeping
the returned type generator has the following guarantee: all possible representable types implied by the constraint set
for the root are represented in the type generator
*)
let rec dfs_typs (root: Typ.t) (gen_results: TypGenRes.results) (tracked: CycleTrack.t) (eq_class: CycleTrack.t) 
    (unseen_results: ResTrack.t) (deps: ResTrack.dep_list) (updateable: bool)
    : TypGen.typ_gens * CycleTrack.t * CycleTrack.t * ResTrack.t * Blacklist.t * TypGenRes.results *  ResTrack.dep_list =
    (*Printf.printf "root begin: %s\n" (string_of_typ root);*)
    (*update the tracking mechanisms *)
    let tracked = CycleTrack.track_typ root tracked in
    let eq_class = CycleTrack.track_typ root eq_class in
    (*perform a dfs as necessitated by the shape of the root and store the updated parameters *)
    let (dfs_all, tracked, eq_class, unseen_results, blist, gen_results, deps) = 
        match root with
        | TNum -> ([], tracked, eq_class, unseen_results, [], gen_results, deps)
        | TBool -> ([], tracked, eq_class, unseen_results, [], gen_results, deps)
        | TArrow (ty1, ty2) -> dfs_typs_of_ctr Signature.Arrow ty1 ty2 gen_results tracked eq_class unseen_results deps updateable
        | TProd (ty1, ty2) -> dfs_typs_of_ctr Signature.Prod ty1 ty2 gen_results tracked eq_class unseen_results deps updateable
        | TSum (ty1, ty2) -> dfs_typs_of_ctr Signature.Sum ty1 ty2 gen_results tracked eq_class unseen_results deps updateable
        | THole _ -> (
            match (TypGenRes.retrieve_gens_for_typ root gen_results) with
            | Some gens -> (dfs_typs_gen gens gen_results tracked eq_class unseen_results deps updateable)
            | None -> ([], tracked, eq_class, unseen_results, [], gen_results, deps)
        )
    in
    (* based on updatable status, extend the unseen results as needed *)
    let (deps, unseen_results) = 
        if (updateable) then (
            ResTrack.update_unseens_after_typ root deps unseen_results
        ) else (deps, unseen_results)
    in
    (*Printf.printf "root end: %s\n" (string_of_typ root);
    Printf.printf "%s\n" (string_of_restrack unseen_results);*)
    (*updated root tracking *)
    let unseen_results = ResTrack.remove_typ root unseen_results in
    (*return the previous parameters after updating the dfs types to inclue to root *)
    ((TypGen.extend_with_typ dfs_all root), tracked, eq_class, unseen_results, blist, gen_results, deps)

(* PURPOSE: Given a recursive type constructed via 'ctr' with lhs 'ty1' and rhs 'ty2', performs a dfs *)
and dfs_typs_of_ctr (ctr: Signature.ctr) (ty1: Typ.t) (ty2: Typ.t) (gen_results: TypGenRes.results) 
    (tracked: CycleTrack.t) (eq_class: CycleTrack.t) (unseen_results: ResTrack.t) (deps: ResTrack.dep_list) (updateable: bool)
    : TypGen.typ_gens * CycleTrack.t * CycleTrack.t * ResTrack.t * Blacklist.t * TypGenRes.results * ResTrack.dep_list =
    (* create the type represented by the arguments *)
    let rec_ty = ((Signature.get_mk_of_ctr ctr) ty1 ty2) in
    (*perform an incorrect dfs of the recursive type's equivalence class to generate a list of info to
    impart to children so that their dfs's will be as correct as possible from this vantage*)
    let (tys_u, uptrack, _, unseen_results, _, gen_results, deps) =
        match (TypGenRes.retrieve_gens_for_typ rec_ty gen_results) with
        | Some gens -> dfs_typs_gen gens gen_results tracked eq_class unseen_results deps updateable
        | None -> ([], [], [], [], [], gen_results, deps)
    in
    (*split the information (ignoring the validity of said split; such checks can be better done in resolve) *)
    let (_, lhs_tys, rhs_tys) = TypGen.split ctr tys_u in
    (*relink the tree so that the children and the splitted types are bidirectionally linked *)
    let gen_results = TypGenRes.link_typ_to_gen ty1 lhs_tys gen_results in
    let gen_results = TypGenRes.link_typ_to_gen ty2 rhs_tys gen_results in
    (*perform a dfs of the lhs side (this is technically not a valid dfs- the rhs may relink more, invalidating this;
    this dfs is only done to ensure the rhs is fully informed) *)
    let (_, _, _, unseen_results, _, gen_results, deps) = 
        dfs_typs ty1 gen_results uptrack [] unseen_results deps updateable
    in
    (*complete rhs dfs *)
    let (ty2_gens, _, _, unseen_results, blist2, gen_results, deps) = 
        dfs_typs ty2 gen_results uptrack [] unseen_results deps updateable
    in
    (*complete a true lhs dfs *)
    let (ty1_gens, _, _, unseen_results, blist1, gen_results, deps) = 
        dfs_typs ty1 gen_results uptrack [] unseen_results deps updateable
    in
    (*fuse the types gleaned from lhs and rhs as needed *)
    let rec_tys_gen = TypGen.fuse ctr ty1_gens ty2_gens in
    (*do a final dfs of the recursive type's cycle now that children have been fully relinked and completed *)
    let (dfs_tys, tracked, eq_class, unseen_results, blist3, gen_results, deps) = 
        match (TypGenRes.retrieve_gens_for_typ rec_ty gen_results) with
        | Some gens -> dfs_typs_gen gens gen_results tracked eq_class unseen_results deps updateable
        | None -> ([], tracked, eq_class, unseen_results, [], gen_results, deps)
    in
    (*fuse the results from children and the recursive cycle *)
    let new_gens = TypGen.extend_with_gen dfs_tys rec_tys_gen in
    (*merge the blacklists accumulated across calls *)
    let final_blist = Blacklist.merge_blists [blist1; blist2; blist3;] in
    (new_gens, tracked, eq_class, unseen_results, final_blist, gen_results, deps)

(* explores all types with results contained in gens and returns the result *)
and dfs_typs_gen (gens: TypGen.typ_gens) (gen_results: TypGenRes.results) (tracked: CycleTrack.t) (eq_class: CycleTrack.t)
    (unseen_results: ResTrack.t) (deps: ResTrack.dep_list) (updateable: bool)
    : TypGen.typ_gens * CycleTrack.t * CycleTrack.t * ResTrack.t * Blacklist.t * TypGenRes.results * ResTrack.dep_list =
    (* generate a list of explorable destinations from the generator *)
    let destinations = TypGenRes.explorable_list gens gen_results in
    (* to be in domain and unequal denotes failure of the occurs check; this function thus acts as an occurs checker *)
    let in_domain_and_unequal (list_elt: Typ.t) (eq_elt: Typ.t): bool =
        (eq_elt <> list_elt) && ((Typ.contains_typ eq_elt list_elt) || (Typ.contains_typ list_elt eq_elt))
    in
    (*traverse all 'valid' (not occurs or already seen) elements *)
    let traverse_if_valid (acc: TypGen.typ_gens * CycleTrack.t * CycleTrack.t * ResTrack.t * Blacklist.t * TypGenRes.results * ResTrack.dep_list) 
        (list_elt: Typ.t)
        : TypGen.typ_gens * CycleTrack.t * CycleTrack.t * ResTrack.t * Blacklist.t * TypGenRes.results * ResTrack.dep_list =
        let (acc_typs, tracked, eq_class, unseen_results, acc_blist, acc_res, deps) = acc in
        (* search for anything that fails the occurs check with this element *)
        let occ_fails = List.filter (in_domain_and_unequal list_elt) eq_class in
        match occ_fails with
        | [] -> (
            (*if nothing failed
            if already traversed, skip *)
            if (CycleTrack.is_tracked list_elt tracked) then (
                (acc_typs, tracked, eq_class, unseen_results, acc_blist, acc_res, deps)
            ) else (
                (*otherwise, dfs the elt *)
                let (dfs_all, tracked, eq_class, unseen_results, new_blist, acc_res, deps) = 
                    dfs_typs list_elt acc_res tracked eq_class unseen_results deps updateable
                in
                (*merge the blacklist *)
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
        | _ -> (
            (*if something(s) failed:
            for every element that fails, add it to the blacklist *)
            let blist_elt (acc: Blacklist.t) (occ_fail_elt: Typ.t): Blacklist.t =
                Blacklist.add_elt acc (occ_fail_elt, Occurs)
            in
            let acc_blist = Blacklist.add_elt acc_blist (list_elt, Occurs) in
            let acc_blist = List.fold_left blist_elt acc_blist occ_fails in
            (acc_typs, tracked, eq_class, unseen_results, acc_blist, acc_res, deps)
        )
    in
    (*attempt to traverse and update for all explorable destinations *)
    let (typs, tracked, eq_class, unseen_results, blist, gen_results, deps) =
        List.fold_left traverse_if_valid ([], tracked, eq_class, unseen_results, [], gen_results, deps) destinations
    in
    (*combine explored results with those already known for a final generator *)
    let original_with_dfs_typs = 
        TypGen.extend_with_gens gens typs
    in
    (original_with_dfs_typs, tracked, eq_class, unseen_results, blist, gen_results, deps)
;;

(*a quick note:
since the final solution contains all references, there is technically no need to dfs; you could just 
replace the solution for all members of the list and call recursive protocol for any recursive types in it.*)

(* RESOLVE DOCUMENTATION *)
(* PURPOSE: given a root and its associated dfsed solution, updates results so that the root and related types
            (being in cycle or accessible as a child from some in cycle node) by using said solution*)
(* DETAILS:
    - root is the node from which resolution will start
    - solution represents the dfs result representing the tree beginning at root
    - gen_results represents the tree to resolve
    - tracked acts as a means to track which branches have been explored.
*)
(* RETURNS:
    - an updated result list gen_results
    - the currently tracked values passed in dfs
    - a blacklist (assuming dfs has been called, which it better have been) now including invalid shape offenders
among these, the only ones useful for programmers is the gen_results (and technically the blacklist, but thats more for handoff)
*)
let rec resolve (root: Typ.t) (solution: TypGen.typ_gens) (gen_results: TypGenRes.results) (tracked: CycleTrack.t)
    : TypGenRes.results * CycleTrack.t * Blacklist.t =
    (*track current node *)
    let tracked = CycleTrack.track_typ root tracked in
    (*based on shape of root, resole as is appropriate *)
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

(* PURPOSE: Given a recursive type constructed via 'ctr' with lhs 'ty1' and rhs 'ty2', applies the solution give, splitting across children *)
and resolve_of_ctr (ctr: Signature.ctr) (ty1: Typ.t) (ty2: Typ.t) (solution: TypGen.typ_gens) (gen_results: TypGenRes.results) 
    (tracked: CycleTrack.t): TypGenRes.results * CycleTrack.t * Blacklist.t =
    (*split the solution, saving the validity status *)
    let (split_res, lhs_tys, rhs_tys) = TypGen.split ctr solution in
    (*save the represented recursive type *)
    let rec_ty = ((Signature.get_mk_of_ctr ctr) ty1 ty2) in
    (*update the blacklist based on the split's success *)
    let new_blist: Blacklist.t =
        match split_res with
        | Success -> []
        | Fail f_stat -> (
            (*if simply an inconsistency in ctrs, only the rec typ's equivalence class is invalid; 
            if a use of a rec typ as a base type, then all elts of the rec are invalid *)
            match f_stat with
            | Ctr_fail -> [(rec_ty, Invalid);]
            | _ -> (
                (*generates a list of 'literal' types from a single recursive type *)
                let rec typ_to_typ_ls (typ: Typ.t): Typ.t list =
                    match typ with
                    | TArrow (ty1, ty2)
                    | TProd (ty1, ty2)
                    | TSum (ty1, ty2) -> (typ_to_typ_ls ty1) @ (typ_to_typ_ls ty2)
                    | _ -> [typ]
                in
                let ty_ls = typ_to_typ_ls rec_ty in
                (*add all contained recursive types to the blacklist as invalid *)
                List.rev_map (fun (x: Typ.t): (Typ.t * Blacklist.err)  -> (x, Invalid)) ty_ls
            )
        )
    in
    (*update results with information for children (resolve then replace)*)
    let (gen_results, tracked, blist1) = resolve_typ_gens lhs_tys gen_results tracked in
    let gen_results = TypGenRes.replace_gens_of_typ ty1 lhs_tys gen_results in
    let (gen_results, tracked, blist2) = resolve_typ_gens rhs_tys gen_results tracked in
    let gen_results = TypGenRes.replace_gens_of_typ ty2 rhs_tys gen_results in
    (* resolve the remainder of the solution (used to be only do so if the type has a result) *)
    let (gen_results, tracked, blist3) = resolve_typ_gens solution gen_results tracked in
    (*replace own result *)
    let gen_results  = 
        TypGenRes.replace_gens_of_typ ((Signature.get_mk_of_ctr ctr) ty1 ty2) solution gen_results
    in
    (*merge all blacklists *)
    let final_blist = Blacklist.merge_blists [blist1; blist2; blist3; new_blist;] in
    (gen_results, tracked, final_blist)

(* PURPOSE: to direct resolution along to recipients represented by the solution *)
and resolve_typ_gens (solution: TypGen.typ_gens) (gen_results: TypGenRes.results) (tracked: CycleTrack.t)
    : TypGenRes.results * CycleTrack.t * Blacklist.t =
    (*generate an explorable list from the solution *)
    let ty_ls = TypGenRes.explorable_list solution gen_results in
    (*traverse all valid elts and resolve them *)
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

(*PURPOSE: converts results to a final solution status set *)
let rec gen_to_status (gen_results: TypGenRes.results) (blist: Blacklist.t): Status.solution list =
    match gen_results with
    | [] -> []
    | hd::tl -> (
        let (hd_key, hd_val) = hd in
        let stat_of_key = Status.condense hd_val blist in
        (hd_key, stat_of_key)::(gen_to_status tl blist)
    )
;;

(*A wrapper for dfs and resolve; dfses types not seen or in need of revisiting as necessary and resolves them *)
let rec fix_tracked_results (results_to_fix: ResTrack.t) (gen_results: TypGenRes.results) (blist: Blacklist.t) (deps: ResTrack.dep_list)
    : ResTrack.t * TypGenRes.results * Blacklist.t * ResTrack.dep_list =
    (*cycle through the results in need of fixing *)
    match results_to_fix with
    | [] -> results_to_fix, gen_results, blist, deps
    | hd::_ -> (
        (*extract the result and if it is one from which unseen can grow *)
        let (hd_typ, updateable) = hd in
        (*Printf.printf "\n\n%s\n" (string_of_restrack results_to_fix);
        Printf.printf "%s\n" (string_of_dep_list deps);*)
        (*dfs and resolve with the results *)
        let (dfs_tys, _, _, results_to_fix, blist_occ, gen_results, deps) = 
            dfs_typs hd_typ gen_results CycleTrack.empty CycleTrack.empty results_to_fix deps updateable
        in
        let (gen_results, _, blist_shape) = resolve hd_typ dfs_tys gen_results CycleTrack.empty in
        (*accumulate blacklists *)
        let merged_blist = (Blacklist.merge_blists [blist; blist_occ; blist_shape;]) in
        fix_tracked_results results_to_fix gen_results merged_blist deps
    )
;;

(* NOTE Anand: main function *)
(*An all encompassing function that, given results from unification, performs all computation necessary to produce a final solution status set *)
let finalize_results (gen_results: TypGenRes.results): Status.solution list = 
    (* NOTE Anand: gen_results is a map (and a graph lol). There are holes and recursive types contained by values in the map. They also need to be keys, because they need to be solved for as well! *)
    (*add all referenced holes across recursive types as 'results' so that they are discoverable in dfs *)
    (*
      (|1|) 2
      
      ?1
      ?2 -> ?3

      post add all refs

      ?1
      ?2 -> ?3
      ?2 
      ?3
    *)
    let gen_results = add_all_refs_as_results gen_results in
    (*produce a set of types that must be dfsed for completion *)
    let results_to_fix = ResTrack.results_to_t gen_results in
    (*produce a dependency list to inform potential recomputation *)
    let deps = ResTrack.r_results_to_dep_list gen_results in
    (*fix all needed results and update the gen_results as appropriate *)
    let (_, gen_results, blacklist, _) = 
        fix_tracked_results results_to_fix gen_results [] deps
    in
    (*a helper to represent typs as ints for sorting *)
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
    (*a comparator for sort *)
    let comp_status (stat1: Status.solution) (stat2: Status.solution)
        : int =
        let (ty1, _) = stat1 in
        let (ty2, _) = stat2 in
        let id1 = extract_leftmost ty1 in
        let id2 = extract_leftmost ty2 in
        Stdlib.compare id1 id2
    in
    (*condense all results into solutions *)
    let solutions = gen_to_status gen_results blacklist in
    (*sort the solutions for readability *)
    List.fast_sort comp_status solutions
;; 