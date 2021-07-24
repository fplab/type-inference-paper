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

    (*New helpers to extract the list of variables from unify_results *)
    let extract_var (result: (TypeInferenceVar.t * unify_result)): TypeInferenceVar.t =
        match result with
        | (var, _) -> var
    ;;

    let extract_var_list (results: unify_results): TypeInferenceVar.t list =
        List.map extract_var results
    ;;

    (*New helpers to extract a list results from unify_results *)
    let extract_result (result: (TypeInferenceVar.t * unify_result)): unify_result = 
        match result with
        | (_, result) -> result
    ;;

    let extract_result_list (results: unify_results): unify_result list = 
        List.map extract_result results
    ;;

    (* A function that checks if the given type is a Hole of the var id or is a recursive type involving the var id*)
    let rec contains_var (var: TypeInferenceVar.t) (ty: t): bool =
        match ty with
        | TArrow (ty1, ty2)
        | TProd (ty1, ty2)
        | TSum (ty1, ty2) -> (contains_var var ty1) || (contains_var var ty2)
        | THole ty_var -> (ty_var = var)
        | _ -> false
    ;;

    let rec contains_typ (typ: t) (container: t): bool =
        if (typ = container) then true
        else (
            match container with
            | TArrow (ty1, ty2)
            | TProd (ty1, ty2)
            | TSum (ty1, ty2) -> (contains_typ typ ty1 || contains_typ typ ty2)
            | _ -> false
        )
    ;;

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

    (*select the longest value with the most literals that most different to self
        order of imp: lit num, longest, diff to self; could proceed lexicographically with this ordering *)
    let find_representative (typs: Typ.t list): Typ.t option =
        let rec count_lits (typ: Typ.t): int =
            match typ with
            | TNum
            | TBool -> 1
            | THole _ -> 0
            | TArrow (ty1, ty2)
            | TProd (ty1, ty2)
            | TSum (ty1, ty2) -> (count_lits ty1) + (count_lits ty2)
        in
        let acc_max (find_value: Typ.t -> int) (acc: int * (Typ.t list)) (typ: Typ.t)
            : int * (Typ.t list) =
            let (acc_max, acc_ls) = acc in
            let typ_count = find_value typ in
            if (typ_count > acc_max) then (
                (typ_count, typ::[])
            ) else (
                if (typ_count = acc_max) then (
                    (acc_max, typ::acc_ls)
                ) else (
                    acc
                )
            )
        in
        match typs with
        | [] -> None
        | hd::tl -> (
            let acc = ((count_lits hd), [hd]) in
            let (_, out_tys) = List.fold_left (acc_max count_lits) acc tl in
            match out_tys with
            | [] -> raise Impossible
            | hd::[] -> Some hd
            | hd::tl -> (
                let rec typ_len (typ: Typ.t): int =
                    match typ with
                    | TNum
                    | TBool
                    | THole _ -> 1
                    | TArrow (ty1, ty2)
                    | TProd (ty1, ty2)
                    | TSum (ty1, ty2) -> (typ_len ty1) + (typ_len ty2)
                in
                let acc = ((typ_len hd), [hd]) in
                let (_, out_tys) = List.fold_left (acc_max typ_len) acc tl in
                match out_tys with
                | [] -> raise Impossible
                | hd::_ -> Some hd
            )
        )
    ;;
end

(*All type gen operations preserve all possible type combinations EXCEPT those that produce a unify result (ie condense) *)
module TypGen = struct
    type base_typ = 
        | Num
        | Bool
        | Hole of TypeInferenceVar.t
    
    type ctr =
        | Arrow
        | Prod
        | Sum

    type typ_gen =
        | Base of base_typ
        | Compound of ctr * typ_gens * typ_gens
    
    and typ_gens = typ_gen list

    let get_mk_of_ctr (ctr_used: ctr): Typ.t -> Typ.t -> Typ.t =
        match ctr_used with
        | Arrow -> Typ.mk_arrow
        | Prod -> Typ.mk_prod
        | Sum -> Typ.mk_sum
    ;;

    let rec get_sig_of_typ_gen (gen: typ_gen): (ctr list) = 
        match gen with
        | Base -> []
        | Compound (ctr, _, gens) -> ctr::(get_sig_of_typ_gen gens)
    ;;

    let rec has_sig (ctrs: (ctr list)) (gen: TypGen.typ_gen): bool =
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
        extend_with_typ_gen gen gen_rep_typ ty_sig
    ;;

    let combine (gens1: typ_gens) (gens2: typ_gens): typ_gens =
        List.fold_left extend_with_typ_gen gens1 gens2
    ;;

    (*maintains invariant of all combinations present; bool returned
    dictates whether the split was valid for all values split *)
    let split (ctr_used: ctr) (gen: typ_gens): bool * typ_gen * typ_gen =
        let of_ctr (gen_elt: typ_gen): bool = 
            match gen_elt with
            | Base ty -> (
                match ty with
                | Num
                | Bool -> false
                | _ -> true
            )
            | Compound (ctr', gens1, gens2) -> (ctr' = ctr_used)
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

    let fuse (ctr_used: ctr) (gen1: typ_gens) (gen2: typ_gens): typ_gen =
        Compound (ctr_used, gen1, gen2)
    ;;

    let rec dest_in_gens (dest_parts: Typ.t list) (dest_sig: ctr list) (gen: typ_gens): bool =
        match gen with
        | [] -> ((dest_parts = []) && (dest_sig = []))
        | hd::tl -> (if (dest_in_gen hd) then (true) else (dest_in_gens dest_parts dest_sig tl))
    and dest_in_gen (dest_parts: Typ.t list) (dest_sig: ctr list) (gen_elt: typ_gen): bool =
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
                if (hd = ctr) then (
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

    let explorable_list (gen: typ_gens) (gens: TypGenRes.results): Typ.t list =
        let get_key (acc: Typ.t list) (elt: TypGenRes.t): Typ.t list =
            let (ty, _) = elt in
            ty::acc
        in
        let destinations = List.fold_left get_key [] gens in
        let rec typ_to_typ_ls (Typ.t): Typ.t list = 
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

    let rec most_informative_in_typ_gens (gen: typ_gens): Typ.t list =
        match gen with
        | [] -> []
        | hd::tl -> Typ.smallest_unequal_no_id_pair (most_informative_in_typ_gens tl) (most_informative_in_typ_gen hd)
    and most_informative_in_typ_gen (gen_elt: typ_gen): Typ.t list =
        match gen_elt with
        | Base btyp -> base_typ_to_typ btyp
        | Compound (ctr, gens1, gens1) -> (
            let typ1_ls = most_informative_in_typ_gens gens1 in
            let typ2_ls = most_informative_in_typ_gens gens2 in
            Typ.fuse_lists (get_mk_of_ctr ctr) typ1_ls typ2_ls
        )
    ;;

    (*this function should only be called during disambiguation, if at all *)
    let condense (gen: typ_gens): Typ.unify_result =
        let pruned_typs = most_informative_in_typ_gens gen in
        let all_cons_with_typ (typs: Typ.t list) (typ: Typ.t): bool = 
            List.for_all (Typ.consistent typ) typs 
        in
        let all_cons = List.for_all (all_cons_with_typ pruned_typs) pruned_typs in
        if (all_cons) then (
            Typ.Solved (find_representative pruned_typs)
        ) else (
            Typ.UnSolved pruned_typs
        )
    ;;
end

module TypGenRes = struct
    type t = Typ.t * TypGen.typ_gens

    type results = t list

    type u_res =
        | Hole of Typ.unify_result
        | Ctr of Typ.r

    let retrieve_gen_for_typ (typ: Typ.t) (gens: results): TypGen.typ_gens option =
        let matches (elt: t): bool = 
            let (key, _) = elt in
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
        (key, gen_of_key)
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
            | ((Typ.THole key_var), gen) -> ((key_var * (TypGen.condense gen))::acc_u, acc_r)
            | (key, gen) -> (acc_u, ((key, TypGen.condense gen)::acc_r))
        in
        List.fold_left acc_results ([], []) gens
    ;;

    let replace_gen_of_typ (typ: Typ.t) (replacement: gens) (gens: results): results =
        let replace_if_match (gen_res: t): t =
            let (key, value) = gen_res in
            if (typ = key) then (
                replacement
            ) else (
                value
            )
        in
        List.rev_map replace_if_match gens
    ;;

    let link_typ_to_gen (typ: Typ.t) (gen: TypGen.typ_gens) (gens: results): results =
        (*typ should be connected to gen in gens if typ has a result in gens
        all elements of gen that are explorable should be linked to typ *)
        let gens = 
            match (retrieve_gen_for_typ typ gens) with
            | Some gen' -> (
                let updated_gen = TypGen.combine gen gen' in
                replace_gen_of_typ typ updated_gen gens
            )
            | None -> gens
        in
        let to_be_linked_to_typ = TypGen.explorable_list gen gens in
        let update (addition: Typ.t) (acc: results) (key: Typ.t): results =
            match (retrieve_gen_for_typ key acc) with
            | Some gen' -> (
                let updated_gen = TypGen.extend_with_typ gen' addition in
                replace_gen_of_typ key updated_gen gens
            )
            | None -> gens
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

(*
module Solver = struct 
    type hole_eq = TypeInferenceVar.t * (Typ.t list)
    type hole_eqs = hole_eq list
    type result = 
        | Solved of (t list)
        | UnSolved of (t list)
    type results = result list
    
    let rec lookup (hole_var : TypeInferenceVar.t) (eqs : hole_eqs) : (Typ.t list) option =
        match eqs with
        | [] -> None
        | hd::tl -> (
            let (hole_eq_var, hole_typ_ls) = hd in if hole_eq_var == hole_var 
            then Some(hole_typ_ls) 
            else (lookup hole_var tl)
        )
    (*
    (*adds a type to the list of type equivalences if it is not already in the domain of it *)
    let rec update_typ_in_hole_eqs (eqs : hole_eqs) (hole_var : TypeInferenceVar.t) (typ: Typ.t): hole_eqs =
        match eqs with
        | [] -> []
        | hd::tl -> (
            let (hole_eq_var, hole_typ_ls) = hd in 
            if (hole_eq_var == hole_var) then (
                if (Typ.in_dom hole_typ_ls typ) then (
                    hd::tl
                )
                else (
                    (*buggy; something about brackets? 
                    if not in the domain then add it to the list of types*)
                    (hole_eq_var, [typ, ...hole_typ_ls])::tl
                )
            )
            else (
                hd::(update_typ_in_hole_eqs tl hole_var typ)
            )
        )
        *)
    let rec merge_hole_eqs (eqs1 : hole_eqs) (eqs2 : hole_eqs): hole_eqs =
        match eqs1 with 
        | [] -> eqs2
        | (hd_v, hd_typ)::tl -> merge_hole_eqs tl (update_typ_in_hole_eqs eqs2 hd_v hd_typ)
end
*)
