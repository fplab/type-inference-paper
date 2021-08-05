open Syntax

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
if an occurs check was failed due to the results and a list of all types or if invalid split occurred *)
let rec dfs_typs (root: Typ.t) (gen_results: TypGenRes.results) (tracked: CycleTrack.t) (unseen_results: ResTrack.t) (ctr_exp: bool)
    : TypGen.typ_gens * CycleTrack.t * ResTrack.t * Blacklist.t =
    let tracked = CycleTrack.track_typ root tracked in
    (*
    Printf.printf "Beginning %s" (string_of_typ root);
    Printf.printf " with ctr_exp as %s\n" (if (ctr_exp) then "true" else "false");
    *)
    let unseen_results = ResTrack.remove_typ root unseen_results in
    let by_ctr_exp (ctr_exp: bool) (ctr: Signature.ctr) (ty1: Typ.t) (ty2: Typ.t)
        : (TypGen.typ_gens) * CycleTrack.t * ResTrack.t * Blacklist.t =
        if (ctr_exp) then (
            dfs_typs_of_ctr ctr ty1 ty2 gen_results tracked unseen_results
        ) else (
            match (TypGenRes.retrieve_gens_for_typ root gen_results) with
            | Some gens -> dfs_typs_gen gens gen_results tracked unseen_results false
            | None -> ([], tracked, unseen_results, [])
        )
    in
    let (dfs_all, tracked, unseen_results, blist) = 
        match root with
        | TNum -> ([], tracked, unseen_results, [])
        | TBool -> ([], tracked, unseen_results, [])
        | TArrow (ty1, ty2) -> (by_ctr_exp ctr_exp Signature.Arrow ty1 ty2)
        | TProd (ty1, ty2) -> (by_ctr_exp ctr_exp Signature.Prod ty1 ty2)
        | TSum (ty1, ty2) -> (by_ctr_exp ctr_exp Signature.Sum ty1 ty2)
        | THole _ -> (
            match (TypGenRes.retrieve_gens_for_typ root gen_results) with
            | Some gens -> (dfs_typs_gen gens gen_results tracked unseen_results ctr_exp)
            | None -> ([], tracked, unseen_results, [])
        )
    in
    (*Printf.printf "dfs blacklist: \n%s\n" (string_of_blist blist);*)
    (*Printf.printf "Finishing %s\n" ((string_of_typ root) ^ " {:} " ^ (string_of_typ_gens dfs_all));*)
    ((TypGen.extend_with_typ dfs_all root), tracked, unseen_results, blist)
and dfs_typs_of_ctr (ctr: Signature.ctr) (ty1: Typ.t) (ty2: Typ.t) (gen_results: TypGenRes.results) (tracked: CycleTrack.t) (unseen_results: ResTrack.t)
    : TypGen.typ_gens * CycleTrack.t * ResTrack.t * Blacklist.t =
    let rec_ty = ((Signature.get_mk_of_ctr ctr) ty1 ty2) in
    let (tys_u, _, _, _) =
        match (TypGenRes.retrieve_gens_for_typ rec_ty gen_results) with
        | Some gens -> dfs_typs_gen gens gen_results tracked unseen_results false
        | None -> ([], [], [], [])
    in
    let (_, lhs_tys, rhs_tys) = TypGen.split ctr tys_u in
    (*
    Printf.printf "validity of (%s) " (string_of_typ ((Signature.get_mk_of_ctr ctr) ty1 ty2));
    Printf.printf "is %s\n" (if (valid) then "VALID" else "INVALID");
    *)
    let gen_results = TypGenRes.link_typ_to_gen ty1 lhs_tys gen_results in
    let gen_results = TypGenRes.link_typ_to_gen ty2 rhs_tys gen_results in
    (*Printf.printf "new tree: %s\n" (string_of_gen_res gen_results);*)
    let (ty1_gens, _, unseen_results, blist1) = 
        dfs_typs ty1 gen_results CycleTrack.empty unseen_results true
    in
    let (ty2_gens, _, unseen_results, blist2) = 
        dfs_typs ty2 gen_results CycleTrack.empty unseen_results true
    in
    let rec_tys_gen = TypGen.fuse ctr ty1_gens ty2_gens in
    let (dfs_tys, tracked, unseen_results, blist3) = 
        match (TypGenRes.retrieve_gens_for_typ rec_ty gen_results) with
        | Some gens -> dfs_typs_gen gens gen_results tracked unseen_results true
        | None -> ([], tracked, unseen_results, [])
    in
    (*Printf.printf "DEBUG:\n";
    Printf.printf "%s\n" ((string_of_typ (ctr ty1 ty2)) ^ " {:} "^ (string_of_typ_ls final_tys));*)
    let new_gens = TypGen.extend_with_gen dfs_tys rec_tys_gen in
    (*
    Printf.printf "fusion had:\n%s\n" (string_of_typ_gen rec_tys_gen);
    Printf.printf "DFS had: \n %s\n" (string_of_typ_gens dfs_tys);
    Printf.printf "Merge of the two had:\n %s\n\n" (string_of_typ_gens new_gens);
    *)
    (*
    Printf.printf "new blacklist: \n%s\n" (string_of_blist new_blist);
    Printf.printf "b1 blacklist: \n%s\n" (string_of_blist blist1);
    Printf.printf "b2 blacklist: \n%s\n" (string_of_blist blist2);
    Printf.printf "b3 blacklist: \n%s\n" (string_of_blist blist3);
    *)
    let final_blist = Blacklist.merge_blists [blist1; blist2; blist3;] in
    (*
    Printf.printf "final blacklist: \n%s\n" (string_of_blist final_blist);*)
    (new_gens, tracked, unseen_results, final_blist)
and dfs_typs_gen (gens: TypGen.typ_gens) (gen_results: TypGenRes.results) (tracked: CycleTrack.t) (unseen_results: ResTrack.t) (ctr_exp: bool)
    : TypGen.typ_gens * CycleTrack.t * ResTrack.t * Blacklist.t =
    let destinations = TypGenRes.explorable_list gens gen_results in
    (*
    Printf.printf "To where?\n";
    Printf.printf "%s\n" (string_of_typ_gens gens);
    Printf.printf "%s\n" (string_of_typ_ls destinations);
    *)
    let in_domain_and_unequal (list_elt: Typ.t) (tracked_elt: Typ.t): bool =
        (tracked_elt <> list_elt) && (Typ.contains_typ tracked_elt list_elt)
    in
    let traverse_if_valid (acc: TypGen.typ_gens * CycleTrack.t * ResTrack.t * Blacklist.t) (list_elt: Typ.t)
        : TypGen.typ_gens * CycleTrack.t * ResTrack.t * Blacklist.t =
        let (acc_typs, tracked, unseen_results, acc_blist) = acc in
        (*if invalid *)
        let occ_fail_opt = List.find_opt (in_domain_and_unequal list_elt) tracked in
        match occ_fail_opt with
        | Some occ_fail_elt -> (
            let acc_blist = Blacklist.add_elt acc_blist (occ_fail_elt, Occurs) in
            let acc_blist = Blacklist.add_elt acc_blist (list_elt, Occurs) in
            (acc_typs, tracked, unseen_results, acc_blist)
        )
        | None -> (
            (*if already traversed *)
            if (CycleTrack.is_tracked list_elt tracked) then (
                (acc_typs, tracked, unseen_results, acc_blist)
            ) else (
                let (dfs_all, tracked, unseen_results, new_blist) = 
                    dfs_typs list_elt gen_results tracked unseen_results ctr_exp
                in
                (*
                Printf.printf "acc blacklist: \n%s\n" (string_of_blist acc_blist);
                Printf.printf "new blacklist: \n%s\n" (string_of_blist new_blist);
                *)
                let acc_blist = Blacklist.merge_blists [acc_blist; new_blist] in
                (*
                Printf.printf "merge blacklist: \n%s\n" (string_of_blist acc_blist);
                *)
                (*
                Printf.printf "Debug pre extend in dfs gen\n";
                Printf.printf "acc: %s\n" (string_of_typ_gens acc_typs);
                Printf.printf "dfs: %s\n" (string_of_typ_gens dfs_all);
                *)
                ((TypGen.extend_with_gens acc_typs dfs_all),
                tracked,
                unseen_results,
                acc_blist)
            )
        )
    in
    let (typs, tracked, unseen_results, blist) =
        List.fold_left traverse_if_valid ([], tracked, unseen_results, []) destinations
    in
    (*Printf.printf "blacklist: \n%s\n" (string_of_blist blist);*)
    (*combine explored results with those already known that weren't giving more info than present. *)
    let original_with_dfs_typs = 
        TypGen.extend_with_gens gens typs
    in
    (original_with_dfs_typs, tracked, unseen_results, blist)
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
    (*
    Printf.printf "resolve target: %s\n" (string_of_typ root);
    *)
    match root with
    | TNum
    | TBool -> (gen_results, tracked, [])
    | TArrow (ty1, ty2) -> resolve_of_ctr Signature.Arrow ty1 ty2 solution gen_results tracked
    | TProd (ty1, ty2) -> resolve_of_ctr Signature.Prod ty1 ty2 solution gen_results tracked
    | TSum (ty1, ty2) -> resolve_of_ctr Signature.Sum ty1 ty2 solution gen_results tracked
    | THole _ -> (
        (*what if i reframed it to return a sol occ and only replace after getting that update! *)
        let (gen_results, tracked, blist) = resolve_typ_gens solution gen_results tracked in
        (*
        Printf.printf "resolving target (%s) complete" (string_of_typ root);
        Printf.printf " which has sol_occ status %s\n" (if (sol_occ) then "VALID" else "INVALID");
        *)
        let gen_results = TypGenRes.replace_gens_of_typ root solution gen_results in
        (*
        if (root = (Typ.THole 6)) then (
            Printf.printf "%s\n" (string_of_gen_res gen_results)
        ) else (
            ()
        );*)
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
        (*
        Printf.printf "(res) validity of (%s) " (string_of_typ ((Signature.get_mk_of_ctr ctr) ty1 ty2));
        Printf.printf "is split %s " (if (valid) then "VALID" else "INVALID");
        Printf.printf "with found sol_occ status %s\n" (if (sol_occ) then "pass" else "fail");
        *)
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
        (hd_key, (Status.condense hd_val blist))::(gen_to_status tl blist)
    )
;;

let rec fix_tracked_results (results_to_fix: ResTrack.t) (gen_results: TypGenRes.results) (blist: Blacklist.t)
    : ResTrack.t * TypGenRes.results * Blacklist.t =
    match results_to_fix with
    | [] -> results_to_fix, gen_results, blist
    | hd::_ -> (
        let (dfs_tys, _, results_to_fix, blist') = dfs_typs hd gen_results CycleTrack.empty results_to_fix true in
        (*Printf.printf "fix blacklist': \n%s\n" (string_of_blist blist');*)
        (*
        Printf.printf "DEBUG DFS:\n";
        Printf.printf "currently running: %s\n " (string_of_typ hd);
        Printf.printf "with occ pass status: %s\n" (if (occ) then "pass" else "fail");
        Printf.printf "%s\n\n" (string_of_typ_gens dfs_tys);
        *)
        (*
        Printf.printf "currently running: %s " (string_of_typ hd);
        Printf.printf "with occ pass status: %s\n" (if (occ) then "pass" else "fail");
        *)
        let (gen_results, _, blist'') = resolve hd dfs_tys gen_results CycleTrack.empty in
        (*
        Printf.printf "After fixing %s, the results were: \n" (string_of_typ hd); 
        Printf.printf "%s\n\n" (string_of_gen_res gen_results);
        *)
        let merged_blist = (Blacklist.merge_blists [blist; blist'; blist'';]) in
        (*Printf.printf "merge fix blacklist': \n%s\n" (string_of_blist merged_blist);*)
        fix_tracked_results results_to_fix gen_results merged_blist
    )
;;

let finalize_results (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results)
    : Status.solution list = 
    let (u_results, r_results) = 
        add_all_refs_as_results u_results r_results
    in
    let gen_results = TypGenRes.unif_results_to_gen_results u_results r_results in
    (*
    Printf.printf "Initial gen results:\n";
    Printf.printf "%s\n" (string_of_gen_res gen_results);
    *)
    let results_to_fix = ResTrack.results_to_t u_results r_results in
    let (_, gen_results, blacklist) = 
        fix_tracked_results results_to_fix gen_results []
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
    Printf.printf "final results: \n%s\n" (string_of_gen_res gen_results);
    Printf.printf "blacklist: \n%s\n" (string_of_blist blacklist);
    List.fast_sort comp_status solutions
;; 