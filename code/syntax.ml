module Identifier = struct
    type t = string
end

module TypeInferenceVar = struct
    type t = int
    let recent (var_1:t) (var_2:t) = max var_1 var_2;;
end

module Typ = struct
    type t =
        | THole of TypeInferenceVar.t
        | TBool
        | TNum
        | TArrow of t * t
        | TProd of t * t
        | TSum of t * t

    (*
    The solved status is for:
        if only unify has run:
            type variables that have no other type variables found constraining them yet
            and are constrained without inconsistency to a literal/structure of literals.
        if top-sort has also run:
            that have been assessed such that beyond a shadow of a doubt, they have the value of some hole/literal/literal structure through
            topological sorting without any inconsistencies. Such a solution is different from an unreported
            unify_result in that it must occur when a variable is constrained by some OTHER variable (also being potentially cyclic)

    The ambiguous status is for: 
        type variables constrained to other type variables with at most one found base type
        and multiple types involving holes (where NONE of these are inconsistent with the found base type, 
        if present, and all are pairwise consistent)
        These need to be topologically resolved so cycles can be detected and collapsed properly
        After topological sorting, all ambiguous statuses should be resolved to Solved or UnSolved
        Ambiguity is not the same as unconstrained solution to a single type variable
        
    The unsolved status is for:
        type variables that are guaranteed to be unsolved, whether or not the listed dependencies are fully simplified.
        Being fully simplified is guaranteed only if top-sort has been run.
    *)
    type unify_result = 
        | Solved of t
        | Ambiguous of (t option) * (t list)
        | UnSolved of (t list)

    (*solutions for recursive types involving holes;
    really just a type of unify result that isn't for variables,
    but whose solution will help to resolve variables contained
    by describing their dependencies with variables of simpler structure
    ex: TArrow(THole4, THole5) = Solved (THole 0)*)
    type rec_unify_results = (t * unify_result) list

    type unify_results  = (TypeInferenceVar.t * unify_result) list

    (*New helpers to construct recursive types *)
    let mk_arrow (ty1: t) (ty2: t): t = TArrow (ty1, ty2);;
    let mk_prod (ty1: t) (ty2: t): t = TProd (ty1, ty2);;
    let mk_sum (ty1: t) (ty2: t): t = TSum (ty1, ty2);;

    (*Moved consistency to be a typ function *)
    let rec consistent (t1: t) (t2: t) : bool = 
    match (t1,t2) with
    | (THole _ , _)
    | (_ , THole _)
    | (TNum, TNum)
    | (TBool, TBool) -> true
    | (TArrow (t1, t2), TArrow (t3, t4))
    | (TProd (t1, t2), TProd (t3, t4))
    | (TSum (t1, t2), TSum (t3, t4)) -> (consistent t1 t3) && (consistent t2 t4)
    | _ -> false
    ;;

    let rec in_dom lst typ = 
        match lst with
        | [] -> false
        | hd::tl -> hd=typ || (in_dom tl typ)
    ;;
    
    let add_to_typ_lst  (typ: t) (ls: t list)  =
        if (in_dom ls typ) then ls else typ::ls
    ;;
    let rec merge_typ_lst (ls1: t list) (ls2: t list) =
        match ls1 with
        | [] -> ls2
        | hd::tl ->  
            if (in_dom ls2 hd) then 
            (merge_typ_lst tl ls2) else
            (hd::(merge_typ_lst tl ls2))
    ;;

    let type_variable = ref (0);;

    (* generates a new unique type variable *)
    let gen_new_type_var () =
        let var = !type_variable in
        incr type_variable; var
        ;;

    let reset_type_var () =
        type_variable:= 0
        ;;
    let rec load_type_variable (t: t) =
        match t with
        | THole id -> type_variable:= TypeInferenceVar.recent (id+1) !type_variable
        | TBool
        | TNum -> ()
        | TProd (ty1,ty2)
        | TSum (ty1,ty2)
        | TArrow (ty1,ty2)-> (
        load_type_variable(ty1);
        load_type_variable(ty2);
        )
    ;;

    let rec is_fully_literal (typ: t): bool =
        match typ with
        | TNum 
        | TBool -> true
        | THole _ -> false
        | TArrow (ty1, ty2)
        | TProd (ty1, ty2)
        | TSum (ty1, ty2) -> is_fully_literal ty1 && is_fully_literal ty2
    ;;
end

module Signature = struct
    type sig_elt = bool * bool * bool
    type t = sig_elt list

    type ctr =
        | Arrow
        | Prod
        | Sum

    let empty_sig: sig_elt = false * false * false;;

    let sig_of_ctr (ctr_used: ctr): sig_elt =
        Signature.add_ctr ctr Signature.empty_sig
    ;;

    let get_mk_of_ctr (ctr_used: ctr): Typ.t -> Typ.t -> Typ.t =
        match ctr_used with
        | Arrow -> Typ.mk_arrow
        | Prod -> Typ.mk_prod
        | Sum -> Typ.mk_sum
    ;;

    let elt_has_ctr (ctr_used: ctr) (elt: sig_elt): bool =
        match ctr_used with
        | Arrow -> (
            match elt with
            | (true, _, _) -> true
            |  _ -> false
        )
        | Prod -> -> (
            match elt with
            | (_, true, _) -> true
            |  _ -> false
        )
        | Sum -> -> (
            match elt with
            | (_, _, true) -> true
            |  _ -> false
        )
    ;;

    let merge_sig_elts (sig_elt1: sig_elt) (sig_elt2: sig_elt): sig_elt =
        let (a1, p1, s1) = sig_elt1 in
        let (a2, p2, s2) = sig_elt2 in
        ((a1 || a2), (s1 || s2), (p1 || p2))
    ;;

    let add_ctr (ctr_used: ctr) (elt: sig_elt): sig_elt =
        let (or_elt) =
            match ctr_used with
            | Arrow -> (true, false, false)
            | Prod -> (false, true, false)
            | Sum -> (false, false, true)
        in
        merge_sig_elts elt or_elt
    ;;

    let rec combine (sign1: t) (sign2: t): t =
        match sign1 with
        | [] -> sign2
        | hd::tl -> (
            match sign2 with
            | [] -> sign1
            | hd'::tl' -> ((merge_sig_elts hd hd')::(combine tl tl'))
        )
    ;;
end

(*All type gen operations preserve all possible type combinations EXCEPT those that produce a unify result (ie condense) *)
module TypGen = struct
    type base_typ = 
        | Num
        | Bool
        | Hole of TypeInferenceVar.t

    type typ_gen =
        | Base of base_typ
        | Compound of ctr * typ_gens * typ_gens
    
    and typ_gens = typ_gen list
    
    let rec get_sig_of_typ_gens (gen: typ_gens): Signature.t =
        match gen with
        | [] -> []
        | hd::tl -> (Signature.combine (get_sig_of_typ_gen hd) (get_sig_of_typ_gens tl))
    and get_sig_of_typ_gen (gen_elt: typ_gen): Signature.t = 
        match gen_elt with
        | Base _ -> []
        | Compound (ctr, _, gen) -> (Signature.sig_of_ctr ctr)::(get_sig_of_typ_gens gen)
    ;;

    let rec has_sig (ctrs: Signature.t) (gen: TypGen.typ_gen): bool =
        match gen with
        | Base _ -> (ctrs = [])
        | Compound (ctr, _, gens2) -> (
            let (succ, ctrs) = 
                match ctrs with
                | [] -> (false, [])
                | hd::tl -> ((ctr = hd), tl)
            in
            if (succ) then (has_sig ctrs gens2) else false
        )
    ;;

    let rec typ_to_typ_gen (typ: Typ.t): typ_gen =
        match typ with
        | TNum -> Base Num
        | TBool -> Base Bool
        | THole var -> Base (Hole var)
        | TArrow (ty1, ty2) -> Compound (Arrow, [(typ_to_typ_gen ty1)], [(typ_to_typ_gen ty2)])
        | TProd (ty1, ty2) -> Compound (Prod, [(typ_to_typ_gen ty1)], [(typ_to_typ_gen ty2)])
        | TSum (ty1, ty2) -> Compound (Sum, [(typ_to_typ_gen ty1)], [(typ_to_typ_gen ty2)])
    ;;

    let split_typ_gen (gen: typ_gen): (typ_gen * typ_gen) option =
        match gen with
        | Base _ -> None
        | Compound (_, gens1, gens2) -> Some (gens1, gens2)
    ;; 

    let rec extend_with_typ_gen (gen: typ_gens) (gen_rep_typ: typ_gen): typ_gens =
        match gen with
        | [] -> [gen_rep_typ]
        | hd::tl -> (
            let gen_sig = get_sig_of_typ_gen gen_rep_typ in
            (*if the head matches the desired signature *)
            if (has_sig gen_sig hd) then (
                match hd with
                | Base _ -> (
                    (*if already present exactly, stop *)
                    if (hd = gen_rep_typ) then (
                        gen
                    ) else (
                        hd::(extend_with_typ_gen tl gen_rep_typ)
                    )
                )
                | Compound (ctr, gens1, gens2) -> (
                    (*split the rep into two parts *)
                    let (lhs_typ_gen, rhs_typ_gen) = 
                        match (split_typ_gen gen_rep_typ) with
                        | None -> raise Impossible
                        | Some pair -> pair
                    in
                    (*extend both parts of the matching compound to include the halves *)
                    let gens1 = extend_with_typ_gen gens1 lhs_typ_gen in
                    let gens2 = extend_with_typ_gen gens2 rhs_typ_gen in
                    (*combine and complete *)
                    (Compound (ctr, gens1, gens2))::tl
                )
            ) else (
                hd::(extend_with_typ_gen tl gen_rep_typ)
            )
        )
    ;;

    let extend_with_typ (gen: typ_gens) (typ: Typ.t): typ_gens =
        let gen_rep_typ = typ_to_typ_gen typ in
        extend_with_typ_gen gen gen_rep_typ
    ;;

    let combine (gens1: typ_gens) (gens2: typ_gens): typ_gens =
        List.fold_left extend_with_typ_gen gens1 gens2
    ;;

    (*maintains invariant of all combinations present; bool returned
    dictates whether the split was valid for all values split *)
    let split (ctr_used: Signature.ctr) (gen: typ_gens): bool * typ_gen * typ_gen =
        let of_ctr (gen_elt: typ_gen): bool = 
            match gen_elt with
            | Base ty -> (
                match ty with
                | Num
                | Bool -> false
                | _ -> true
            )
            | Compound (ctr', _, _) -> (ctr' = ctr_used)
        in
        let accumulate_splits (acc: typ_gens * typ_gens) (gen_elt: typ_gen)
            : typ_gens * typ_gens =
            match (split_typ_gen gen_elt) with
            | None -> acc
            | Some (first, second) -> (
                let (acc_first, acc_second) = acc in
                (first::acc_first, second::acc_second)
            )
        in
        let (lhs_gen, rhs_gen) = List.fold_left accumulate_splits ([], []) gen in
        ((List.for_all of_ctr gen), lhs_gen, rhs_gen)
    ;;

    let fuse (ctr_used: Signature.ctr) (gen1: typ_gens) (gen2: typ_gens): typ_gen =
        Compound (ctr_used, gen1, gen2)
    ;;

    let rec dest_in_gens (dest_parts: Typ.t list) (dest_sig: Signature.t) (gen: typ_gens): bool =
        match gen with
        | [] -> ((dest_parts = []) && (dest_sig = []))
        | hd::tl -> (if (dest_in_gen hd) then (true) else (dest_in_gens dest_parts dest_sig tl))
    and dest_in_gen (dest_parts: Typ.t list) (dest_sig: Signature.t) (gen_elt: typ_gen): bool =
        match gen_elt with
        | Base ty -> (
            match dest_parts with
            | hd::[] -> (hd = ty)
            | _ -> false
        )
        | Compound (ctr, gens1, gens2) -> (
            match dest_sig with
            | [] -> false
            | hd_sig::tl_sig -> (
                if (hd_sig = ctr) then (
                    match dest_parts with
                    | [] -> false
                    | hd_parts::tl_parts -> (
                        (dest_in_gens [hd_parts] [] gens1) && (dest_in_gens tl_parts tl_sig gens2) 
                    )
                ) else (
                    false
                )
            )
        )
    ;;

    (*constructs a list of all values that can be explored from a typgen given a set of results
    by listing all those types represented in gen that have a result in the result set supplied *)
    let explorable_list (gen: typ_gens) (gens: TypGenRes.results): Typ.t list =
        let get_key (acc: Typ.t list) (elt: TypGenRes.t): Typ.t list =
            let (ty, _) = elt in
            ty::acc
        in
        let destinations = List.fold_left get_key [] gens in
        let rec typ_to_typ_ls (typ: Typ.t): Typ.t list = 
            match typ with 
            | TNum
            | TBool
            | THole _ -> [typ]
            | TArrow (ty1, ty2) 
            | TProd (ty1, ty2)
            | TSum (ty1, ty2) -> (typ_to_typ_ls ty1) @ (typ_to_typ_ls ty2)
        in
        let dest_check_and_acc (acc: Typ.t list) (dest: Typ.t): Typ.t list =
            let dest_parts = typ_to_typ_ls dest in
            let dest_sig = get_sig_of_typ_gen (typ_to_typ_gen dest) in
            if (dest_in_gen dest_parts dest_sig gen) then (
                dest::acc
            ) else (
                acc
            )
        in
        List.fold_left dest_check_and_acc [] destinations
    ;;

    let base_typ_to_typ (base: base_typ): Typ.t =
        match base with
        | Num -> TNum
        | Bool -> TBool
        | Hole var -> THole var 
    ;;

    let is_base_lit_or_comp (gen_elt: typ_gen): bool =
        match gen_elt with
        | Base (Hole _) -> false
        | _ -> true
    ;;

    (*helper; call fn below *)
    let rec filter_unneeded_holes_gen (remove: bool) (gen: typ_gens): gen =
        match gen with
        | [] -> []
        | hd::tl -> (
            let had_hole, elt_op = filter_unneeded_holes_gen_elt remove hd in
            let remove = had_hole || remove in
            match elt_op with
            | None -> filter_unneeded_holes_gen found tl
            | Some hd' -> hd'::(filter_unneeded_holes_gen found tl)
        )
    and filter_unneeded_holes_gen_elt (remove: bool) (gen_elt: typ_gen): bool * gen_elt option =
        match gen_elt with
        | Base btyp -> (
            match btyp with
            | Hole _ -> (
                let op = if remove then None else gen_elt in
                (true, op)
            )
            | _ -> (false, Some gen_elt)
        )
        | Compound (ctr, gens1, gens2) -> (
            let e_base_lit_or_comp1 = List.exists is_base_lit_or_comp gens1 in
            let e_base_lit_or_comp2 = List.exists is_base_lit_or_comp gens2 in
            let gens1' = filter_unneeded_holes_gen e_base_lit_or_comp1 gens1 in
            let gens2' = filter_unneeded_holes_gen e_base_lit_or_comp2 gens2 in
            (false, (Some (Compound (ctr, gens1', gens2'))))
        )
    ;;

    (*removes all base type holes in the generator that:
        - have a literal as an option in the same position
        - have a compound as an option in the same position
        - are discovered after a needed hole in the same position *)
    let filter_unneeded_holes (gen: typ_gens): gen =
        let e_base_lit_or_comp = List.exists is_base_lit_or_comp gens in
        filter_unneeded_holes_gen e_base_lit_or_comp gen
    ;;

    (*returns the solved value associated with a filtered generator IF IT EXISTS; requires gen be nonempty *)
    let rec filtered_solved_val (gen: typ_gens): Typ.t option =
        match gen with
        | [] -> None
        | (Base btyp)::[] -> Some (base_typ_to_typ btyp)
        | (Compound (ctr, gens1, gens2))::[] -> (
            match (filtered_solved_val gens1) with 
            | None -> None
            | Some typ1 -> (
                match (filtered_solved_val gens2) with
                | None -> None
                | Some typ2 -> (Signature.get_mk_of_ctr ctr) typ1 typ2
            )
        )
        | _ -> None
    ;;
end

module Status = struct
    (*can be solved of a type or unsolved with a generator containing possible types *)
    type t =
        | Solved of Typ.t
        | UnSolved of TypGen.typ_gens

    type solution = Typ.t * t
    
    type solutions = solution list

    (*this function should only be called during completion *)
    let condense (gen: TypGen.typ_gens) (occ_pass: bool): t =
        let filtered_gen = TypGen.filter_unneeded_holes gen in
        if (occ_pass) then (
            UnSolved filtered_gen
        ) else (
            let solved_op = TypGen.filtered_solved_val filtered_gen in
            match solved_op with
            | Some typ -> Solved typ
            | None -> UnSolved filtered_gen
        )
    ;;
end

module TypGenRes = struct
    (*bool represents occurs check status; if false, condensation will make it unsolved *)
    type t = Typ.t * bool * TypGen.typ_gens

    type results = t list

    let retrieve_gen_for_typ (typ: Typ.t) (gens: results): TypGen.typ_gens option =
        let matches (elt: t): bool = 
            let (key, _, _) = elt in
            key = typ
        in
        let key_value = List.find_opt matches gens in
        match key_value with
        | Some (key, value) -> Some value
        | None -> None
    ;;

    let unif_res_to_gen_res (key: Typ.t) (u_res: Typ.unify_result): t =
        let typ_ls = 
            match u_res with
            | Solved ty -> [ty]
            | Ambiguous ((Some ty), tys) -> ty::tys
            | UnSolved tys -> tys
        in
        let gen_of_key = List.fold_left TypGen.extend_with_typ [] typ_ls in
        (key, true, gen_of_key)
    ;;

    let unif_results_to_gen_results (u_results: Typ.unify_results) (r_results: Typ.rec_unify_results): results =
        let u_convert_acc (acc: results) (elt: TypeInferenceVar.t * Typ.unify_result): results =
            let (key_var, u_res) = elt in
            (unif_res_to_gen_res (Typ.THole key_var) u_res)::acc
        in
        let acc = List.fold_left u_convert_acc [] u_results in
        let r_convert_acc (acc: results) (elt: Typ.t * Typ.unify_result): results =
            let (key, u_res) = elt in
            (unif_res_to_gen_res key u_res)::acc
        in
        List.fold_left r_convert_acc acc r_results
    ;;

    let gen_results_to_unif_results (gens: results): Typ.unify_results * Typ.rec_unify_results =
        let acc_results (acc: Typ.unify_results * Typ.rec_unify_results) (gen_res: t)
            : Typ.unify_results * Typ.rec_unify_results =
            let (acc_u, acc_r) = acc in
            match gen_res with
            | ((Typ.THole key_var), occ, gen) -> ((key_var, (Status.condense gen occ))::acc_u, acc_r)
            | (key, occ, gen) -> (acc_u, ((key, Status.condense gen occ)::acc_r))
        in
        List.fold_left acc_results ([], []) gens
    ;;

    let rec replace_gen_of_typ (typ: Typ.t) (replacement: typ_gens) (gens: results): results =
        match results with
        | [] -> []
        | hd::tl -> (
            let (key, occ, _) = hd in
            if (typ = key) then (
                (key, occ, replacement)::tl
            ) else (
                hd::(replace_gen_of_typ typ replacement tl)
            )
        )
    ;;

    let rec replace_gen_and_occ_of_typ (typ: Typ.t) (replacement: typ_gens) (replace_occ: bool) (gens: results)
        : results =
        match results with
        | [] -> []
        | hd::tl -> (
            let (key, _, _) = hd in
            if (typ = key) then (
                (key, replace_occ, replacement)::tl
            ) else (
                hd::(replace_gen_of_typ typ replacement tl)
            )
        )
    ;;

    (*may need to add results for more than just those that have a result-> could be anything with a hole
    however, it could also be that the preservation of all combinations makes it fine
    N->?1 ana against ?3 and ?3 is against B; ?3 is unsolved but ?1 should be too *)
    let link_typ_to_gen (typ: Typ.t) (gen: TypGen.typ_gens) (gens: results): results =
        (*typ should be connected to gen in gens if typ has a result in gens
        all elements of gen that are explorable should be linked to typ *)
        let gens = 
            match (retrieve_gen_for_typ typ gens) with
            | Some gen' -> (
                let updated_gen = TypGen.combine gen gen' in
                replace_gen_of_typ typ updated_gen gens
            )
            | None -> (
                if (is_fully_literal typ) then (
                    gens
                ) else (
                    (typ, true, gen)::gens
                )
            )
        in
        let to_be_linked_to_typ = TypGen.explorable_list gen gens in
        let update (addition: Typ.t) (acc: results) (key: Typ.t): results =
            match (retrieve_gen_for_typ key acc) with
            | Some gen' -> (
                let updated_gen = TypGen.extend_with_typ gen' addition in
                replace_gen_of_typ key updated_gen acc
            )
            | None -> (
                if (is_fully_literal typ) then (
                    acc
                ) else (
                    (key, true, [(typ_to_typ_gen addition)])::acc
                )
            )
        in
        List.fold_left (update typ) gens to_be_linked_to_typ
    ;;
end

module Exp = struct

    type hole_id = int

    type binop = OpAp | OpPlus

    type t =
        | EVar of Identifier.t
        | ELam of Identifier.t * t
        | ELamAnn of Identifier.t * Typ.t * t
        | EBinOp of t * binop * t
        | EBoolLiteral of bool
        | ENumLiteral of int
        | EAsc of t * Typ.t
        | EEmptyHole of hole_id
        | EExpHole of hole_id * t
        | EIf of t * t * t
        | ELet of Identifier.t * Typ.t option * t * t
        | EPair of t * t
        | ELetPair of Identifier.t * Identifier.t * t * t
        | EPrjL of t
        | EPrjR of t
        | EInjL of t
        | EInjR of t
        | ECase of t * Identifier.t * t * Identifier.t * t
end


module Ctx = struct
    type assumption = Identifier.t * Typ.t

    type t = assumption list

    let empty : t = []

    let lookup (ctx : t) (id : Identifier.t) : Typ.t option =
        List.fold_left
        (fun found (i, v) ->
            match found with
            | Some _ -> found
            | None -> if i = id then Some v else None)
        None ctx

    let extend (ctx : t) (e : assumption) : t =
        let id, vl = e in
        match lookup ctx id with
        | None -> e :: ctx
        | Some _ ->
            List.fold_right
            (fun (i, v) new_ctx ->
                if id = i then (i, vl) :: new_ctx else (i, v) :: new_ctx)
            ctx empty
end


module Constraints = struct
    type consistent = Typ.t * Typ.t

    type t = consistent list
end