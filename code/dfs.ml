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
      | Arrow -> "->"
      | Prod -> "*"
      | Sum -> "+"
    in
    ("({" ^ str1 ^ "}" ^ ctr_str ^ "{" ^ str2 ^ "})");
  )
;;

let rec string_of_gen_res (gen_results: TypGenRes.results) =
  match gen_results with
  | [] -> "\n";
  | hd::tl -> (
    let (key, occ, res) = hd in
    let hd_str = 
      (string_of_typ key) ^ ": " ^ (if (occ) then "occ true" else "occ false") ^ ", ls: " ^ (string_of_typ_gens res) ^ "\n"
    in
    hd_str ^ (string_of_gen_res tl)
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
    : bool * (TypGen.typ_gens) * CycleTrack.t * ResTrack.t = 
    let tracked = CycleTrack.track_typ root tracked in
    let unseen_results = ResTrack.remove_typ root unseen_results in
    let by_ctr_exp (ctr_exp: bool) (ctr: Signature.ctr) (ty1: Typ.t) (ty2: Typ.t)
        : bool * (TypGen.typ_gens) * CycleTrack.t * ResTrack.t =
        if (ctr_exp) then (
            dfs_typs_of_ctr ctr ty1 ty2 gen_results tracked unseen_results
        ) else (
            match (TypGenRes.retrieve_gens_for_typ root gen_results) with
            | Some gens -> dfs_typs_gen gens gen_results tracked unseen_results false
            | None -> (true, [], tracked, unseen_results)
        )
    in
    let (occ, dfs_all, tracked, unseen_results) = 
        match root with
        | TNum -> (true, [], tracked, unseen_results)
        | TBool -> (true, [], tracked, unseen_results)
        | TArrow (ty1, ty2) -> (by_ctr_exp ctr_exp Signature.Arrow ty1 ty2)
        | TProd (ty1, ty2) -> (by_ctr_exp ctr_exp Signature.Prod ty1 ty2)
        | TSum (ty1, ty2) -> (by_ctr_exp ctr_exp Signature.Sum ty1 ty2)
        | THole _ -> (
            match (TypGenRes.retrieve_gens_for_typ root gen_results) with
            | Some gens -> (dfs_typs_gen gens gen_results tracked unseen_results ctr_exp)
            | None -> (true, [], tracked, unseen_results)
        )
    in
    (*Printf.printf "DEBUG:\n";
    Printf.printf "%s\n" ((string_of_typ root) ^ " {:} " ^ (string_of_typ_ls dfs_all));*)
    (occ, (TypGen.extend_with_typ dfs_all root), tracked, unseen_results)
and dfs_typs_of_ctr (ctr: Signature.ctr) (ty1: Typ.t) (ty2: Typ.t) (gen_results: TypGenRes.results) (tracked: CycleTrack.t) (unseen_results: ResTrack.t)
    : bool * (TypGen.typ_gens) * CycleTrack.t * ResTrack.t =
    let rec_ty = ((Signature.get_mk_of_ctr ctr) ty1 ty2) in
    let (_, tys_u, _, _) =
        match (TypGenRes.retrieve_gens_for_typ rec_ty gen_results) with
        | Some gens -> dfs_typs_gen gens gen_results tracked unseen_results false
        | None -> (true, [], [], [])
    in
    let (valid, lhs_tys, rhs_tys) = TypGen.split ctr tys_u in
    let gen_results = TypGenRes.link_typ_to_gen ty1 lhs_tys gen_results in
    let gen_results = TypGenRes.link_typ_to_gen ty2 rhs_tys gen_results in
    let (occ1, ty1_gens, _, unseen_results) = 
        dfs_typs ty1 gen_results CycleTrack.empty unseen_results true
    in
    let (occ2, ty2_gens, _, unseen_results) = 
        dfs_typs ty2 gen_results CycleTrack.empty unseen_results true
    in
    let rec_tys_gens = TypGen.fuse ctr ty1_gens ty2_gens in
    let (dfs_occ, dfs_tys, tracked, unseen_results) = 
        match (TypGenRes.retrieve_gens_for_typ rec_ty gen_results) with
        | Some gens -> dfs_typs_gen gens gen_results tracked unseen_results true
        | None -> (true, [], tracked, unseen_results)
    in
    (*Printf.printf "DEBUG:\n";
    Printf.printf "%s\n" ((string_of_typ (ctr ty1 ty2)) ^ " {:} "^ (string_of_typ_ls final_tys));*)
    (occ1 && occ2 && dfs_occ && valid, (TypGen.extend_with_gen dfs_tys rec_tys_gens), tracked, unseen_results)
and dfs_typs_gen (gens: TypGen.typ_gens) (gen_results: TypGenRes.results) (tracked: CycleTrack.t) (unseen_results: ResTrack.t) (ctr_exp: bool)
    : bool * (TypGen.typ_gens) * CycleTrack.t * ResTrack.t =
    let destinations = TypGenRes.explorable_list gens gen_results in
    (*
    Printf.printf "To where?\n";
    Printf.printf "%s\n" (string_of_typ_gens gens);
    Printf.printf "%s\n" (string_of_typ_ls destinations);
    *)
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
                    dfs_typs list_elt gen_results tracked unseen_results ctr_exp
                in
                Printf.printf "Debug pre extend in dfs gen\n";
                Printf.printf "acc: %s\n" (string_of_typ_gens acc_typs);
                Printf.printf "dfs: %s\n" (string_of_typ_gens dfs_all);
                (acc_b && occ_all, 
                (TypGen.extend_with_gens acc_typs dfs_all),
                tracked,
                unseen_results)
            )
        )
    in
    let (occ, typs, tracked, unseen_results) =
        List.fold_left traverse_if_valid (true, [], tracked, unseen_results) destinations
    in
    (*combine explored results with those already known that weren't giving more info than present. *)
    let original_with_dfs_typs = 
        TypGen.extend_with_gens gens typs
    in
    (occ, original_with_dfs_typs, tracked, unseen_results)
;;

(*since the final solution contains all references, there is technically no need to dfs; you could just 
replace the solution for all members of the list and call recursive protocol for any recursive types in it
wouldn't be a hard change. just remove calls to resolve_res and wrap calls to the other two in a standard
recursive matching on a list generated from the solution *)
let rec resolve (root: Typ.t) (solution: TypGen.typ_gens) (sol_occ: bool) (gen_results: TypGenRes.results) (tracked: CycleTrack.t)
    : TypGenRes.results * CycleTrack.t =
    let tracked = CycleTrack.track_typ root tracked in
    match root with
    | TNum
    | TBool -> (gen_results, tracked)
    | TArrow (ty1, ty2) -> resolve_of_ctr Signature.Arrow ty1 ty2 solution sol_occ gen_results tracked
    | TProd (ty1, ty2) -> resolve_of_ctr Signature.Prod ty1 ty2 solution sol_occ gen_results tracked
    | TSum (ty1, ty2) -> resolve_of_ctr Signature.Sum ty1 ty2 solution sol_occ gen_results tracked
    | THole _ -> (
        let gen_results = TypGenRes.replace_gens_and_occ_of_typ root solution sol_occ gen_results in
        resolve_typ_gens solution sol_occ gen_results tracked
    )
and resolve_of_ctr (ctr: Signature.ctr) (ty1: Typ.t) (ty2: Typ.t) (solution: TypGen.typ_gens) (sol_occ: bool) (gen_results: TypGenRes.results) 
    (tracked: CycleTrack.t): TypGenRes.results * CycleTrack.t =
    let (valid, lhs_tys, rhs_tys) = TypGen.split ctr solution in
    let sol_occ = valid && sol_occ in
    (*no need to generate new type results since dfs should already have traversed this and constructed the necessary ones *)
    (*update results with information for children *)
    let gen_results = TypGenRes.replace_gens_and_occ_of_typ ty1 lhs_tys sol_occ gen_results in
    let (gen_results, tracked) = resolve_typ_gens lhs_tys sol_occ gen_results tracked in
    let gen_results = TypGenRes.replace_gens_and_occ_of_typ ty2 rhs_tys sol_occ gen_results in
    let (gen_results, tracked) = resolve_typ_gens rhs_tys sol_occ gen_results tracked in
    match (TypGenRes.retrieve_gens_for_typ ((Signature.get_mk_of_ctr ctr) ty1 ty2) gen_results) with
    | Some _ -> (
        let gen_results  = 
            TypGenRes.replace_gens_and_occ_of_typ ((Signature.get_mk_of_ctr ctr) ty1 ty2) solution sol_occ gen_results
        in
        resolve_typ_gens solution sol_occ gen_results tracked
    )
    | None -> (gen_results, tracked)
(*already following a replaced value; just dfs so other funcs can replace *)
and resolve_typ_gens (solution: TypGen.typ_gens) (sol_occ: bool) (gen_results: TypGenRes.results) (tracked: CycleTrack.t)
    : TypGenRes.results * CycleTrack.t =
    let ty_ls = TypGenRes.explorable_list solution gen_results in
    let traverse_if_valid (acc: TypGenRes.results * CycleTrack.t) (list_elt: Typ.t)
        : TypGenRes.results * CycleTrack.t =
        let (acc_res, tracked) = acc in
        if (CycleTrack.is_tracked list_elt tracked) then (
            (acc_res, tracked)
        ) else (
            resolve list_elt solution sol_occ acc_res tracked
        )
    in
    List.fold_left traverse_if_valid (gen_results, tracked) ty_ls
;;

let rec gen_to_status (gen_results: TypGenRes.results): Status.solution list =
    match gen_results with
    | [] -> []
    | hd::tl -> (
        let (hd_key, hd_occ, hd_val) = hd in
        (hd_key, (Status.condense hd_val hd_occ))::(gen_to_status tl)
    )
;;

let rec fix_tracked_results (results_to_fix: ResTrack.t) (gen_results: TypGenRes.results)
    : ResTrack.t * TypGenRes.results =
    match results_to_fix with
    | [] -> results_to_fix, gen_results
    | hd::_ -> (
        let (occ, dfs_tys, _, results_to_fix) = dfs_typs hd gen_results CycleTrack.empty results_to_fix true in
        Printf.printf "DEBUG DFS:\n";
        Printf.printf "%s\n" (string_of_typ_gens dfs_tys);
        let (gen_results, _) = resolve hd dfs_tys occ gen_results CycleTrack.empty in
        Printf.printf "%s\n" (string_of_gen_res gen_results);
        fix_tracked_results results_to_fix gen_results
    )
;;

let finalize_results (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results)
    : Status.solution list = 
    let (u_results, r_results) = 
        add_all_refs_as_results u_results r_results
    in
    let gen_results = TypGenRes.unif_results_to_gen_results u_results r_results in
    Printf.printf "Initial gen results:\n";
    Printf.printf "%s\n" (string_of_gen_res gen_results);
    let results_to_fix = ResTrack.results_to_t u_results r_results in
    let (_, gen_results) = 
        fix_tracked_results results_to_fix gen_results
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
    let solutions = gen_to_status gen_results in
    List.fast_sort comp_status solutions
;; 