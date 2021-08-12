exception Impossible

module Identifier = struct
    type t = string
end

module TypeInferenceVar = struct
    type t = int
    let recent (var_1:t) (var_2:t) = max var_1 var_2;;
end

(*a lot of this module was coded before I got here; some of it may be redundant *)
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
    type variables that have no other type variables found constraining them yet
    and are constrained without inconsistency to a literal/structure of literals.

    The ambiguous status is for: 
        type variables constrained to other type variables with at most one found base type
        and multiple types involving holes (where NONE of these are inconsistent with the found base type, 
        if present, and all are pairwise consistent)
        
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

    (*solutions for holes *)
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
end

(*can only represent types (not type generators) *)
(*a module to represent constructors, series thereof, and the conversions from construct *)
module Signature = struct
    type ctr =
        | Arrow
        | Prod
        | Sum

    type t = ctr list

    let get_mk_of_ctr (ctr_used: ctr): Typ.t -> Typ.t -> Typ.t =
        match ctr_used with
        | Arrow -> Typ.mk_arrow
        | Prod -> Typ.mk_prod
        | Sum -> Typ.mk_sum
    ;;
end

(*All type gen operations preserve all possible type combinations EXCEPT those that produce a unify result (ie condense) *)
(*A module allowing the representation of type generators *)
module TypGen = struct
    (*in other words, a literal *)
    type base_typ = 
        | Num
        | Bool
        | Hole of TypeInferenceVar.t

    (*a single typ_gen represents a single path of generation *)
    type typ_gen =
        | Base of base_typ
        | Compound of Signature.ctr * typ_gens * typ_gens
    (*a list of typ_gen represents a set of paths for generation *)
    and typ_gens = typ_gen list

    (* converts a typ to a typ gen*)
    let rec typ_to_typ_gen (typ: Typ.t): typ_gen =
        match typ with
        | TNum -> Base Num
        | TBool -> Base Bool
        | THole var -> Base (Hole var)
        | TArrow (ty1, ty2) -> Compound (Arrow, [(typ_to_typ_gen ty1)], [(typ_to_typ_gen ty2)])
        | TProd (ty1, ty2) -> Compound (Prod, [(typ_to_typ_gen ty1)], [(typ_to_typ_gen ty2)])
        | TSum (ty1, ty2) -> Compound (Sum, [(typ_to_typ_gen ty1)], [(typ_to_typ_gen ty2)])
    ;;

    (*splits a typ gen into two separate gens if possible *)
    let split_typ_gen (gen: typ_gen): (typ_gens * typ_gens) option =
        match gen with
        | Base _ -> None
        | Compound (_, gens1, gens2) -> Some (gens1, gens2)
    ;; 

    (*extend a typ_gens with another typ_gens; effectively a merge *)
    let rec extend_with_gens (gens: typ_gens) (gens': typ_gens): typ_gens =
        match gens' with
        | [] -> gens
        | hd::tl -> (
            let gens = extend_with_gen gens hd in
            extend_with_gens gens tl
        )
    (*extend a typ_gens with a typ_gen *)
    and extend_with_gen (gens: typ_gens) (gen: typ_gen): typ_gens = 
        (* assess the gens *)
        match gens with
        | [] -> [gen]
        | hd::tl -> (
            (*if nonempty, assess the gen to see how to insert *)
            match gen with
            | Base _ -> (
                (*if a base, then see if the gens's first path matches exactly *)
                if (hd = gen) then (
                    (*if so, finish *)
                    gens
                ) else (
                    (*else attempt to extend in the remainder *)
                    hd::(extend_with_gen tl gen)
                )
            )
            | Compound (ctr, gens1, gens2) -> (
                (*if compound, see if the hd can be used to insert *)
                match hd with 
                | Base _ -> hd::(extend_with_gen tl gen)
                | Compound (ctr_hd, gens1_hd, gens2_hd) -> (
                    if (ctr_hd = ctr) then (
                        (*the basic structure matches; extend each path of the compound with the parts we want to insert *)
                        let gens1_new = extend_with_gens gens1_hd gens1 in
                        let gens2_new = extend_with_gens gens2_hd gens2 in
                        (*combine the two and replace the old hd *)
                        (Compound (ctr_hd, gens1_new, gens2_new))::tl
                    ) else (
                        (*the basic structures don't match; try to extend in the rest *)
                        hd::(extend_with_gen tl gen)
                    )
                )
            )
        )
    ;;
    
    (*to extend with a type, make the type into a gen and then use the method above *)
    let extend_with_typ (gens: typ_gens) (typ: Typ.t): typ_gens =
        let gen_rep_typ = typ_to_typ_gen typ in
        extend_with_gen gens gen_rep_typ
    ;;

    (*some niche types for use in split for error handling *)
    
    (*effectively a split error status
    ways a split can fail: 
        wasn't splittable (literal aka lit_fail); 
        wasn't splittable as the specified ctr, but was a compound (ctr_fail) *)
    type split_fail =
        | Lit_fail
        | Ctr_fail
    
    (*possible outcomes of a split
        success or a failure with a split error status *)
    type split_status =
        | Success
        | Fail of split_fail

    (*splits the gens in two, maintaining all combinations assuming the split was valid (if not, all valid combinations are passed)
    status returned dictates whether the split was valid for all values split
    and if it failed, what kind of failure occurred *)
    let split (ctr_used: Signature.ctr) (gens: typ_gens): split_status * typ_gens * typ_gens =
        (*a method to check if a gen is of the ctr_used, and if not, with what status such failure occurred *)
        let of_ctr (gen: typ_gen): split_status = 
            match gen with
            | Base ty -> (
                match ty with
                | Num
                | Bool -> Fail Lit_fail
                | _ -> Success
            )
            | Compound (ctr', _, _) -> if (ctr' = ctr_used) then (Success) else (Fail Ctr_fail)
        in
        let accumulate_splits (acc: typ_gens * typ_gens) (gen: typ_gen)
            : typ_gens * typ_gens =
            match (split_typ_gen gen) with
            | None -> acc
            | Some (first, second) -> (
                let (acc_first, acc_second) = acc in
                ((extend_with_gens acc_first first), (extend_with_gens acc_second second))
            )
        in
        (*round up all the splits of each gen in gens *)
        let (lhs_gens, rhs_gens) = List.fold_left accumulate_splits ([], []) gens in
        (*a method that uses of_ctr to evaluate the validity of splits across all gen in gens 
        if a ctr fail is found, keeps checking to see if a lit fail can be found, as it results
        in more severe error handling*)
        let rec check_ctr (gens: typ_gens) (ctr_fail_found: bool): split_status =
            match gens with
            | [] -> if ctr_fail_found then (Fail Ctr_fail) else Success
            | hd::tl -> (
                let hd_check = of_ctr hd in
                match (hd_check) with
                | Fail Lit_fail -> hd_check
                | Fail Ctr_fail -> check_ctr tl true
                | _ -> check_ctr tl ctr_fail_found
            )
        in
        (*return cumulative split error status *)
        ((check_ctr gens false), lhs_gens, rhs_gens)
    ;;

    (*fuses two gens's into a compound of the specified ctr *)
    let fuse (ctr_used: Signature.ctr) (gens1: typ_gens) (gens2: typ_gens): typ_gen =
        Compound (ctr_used, gens1, gens2)
    ;;

    (* converts a base type to its typ representative *)
    let base_typ_to_typ (base: base_typ): Typ.t =
        match base with
        | Num -> TNum
        | Bool -> TBool
        | Hole var -> THole var 
    ;;

    (*checks if dest_gen is present in gens *)
    let rec dest_gen_in_gens (gens: typ_gens) (dest_gen: typ_gen): bool =
        (*is true if in hd or in tl *)
        match gens with
        | [] -> false
        | hd::tl -> ((dest_gen_in_gen hd dest_gen) || (dest_gen_in_gens tl dest_gen))
    and dest_gen_in_gen (gen: typ_gen) (dest_gen: typ_gen): bool =
        (*check the container gen 
        if a base, they should exactly match
        if a compound with a compound dest, then given ctrs match, return true
            only if the dest's gens's are in the containers subpath gens's*)
        match gen with
        | Base _ -> (dest_gen = gen)
        | Compound (ctr, gens1, gens2) -> (
            match dest_gen with
            | Base _ -> false
            | Compound (dest_ctr, dest_gens1, dest_gens2) -> (
                if (dest_ctr = ctr) then (
                    (dest_gens_in_gens gens1 dest_gens1) && (dest_gens_in_gens gens2 dest_gens2)
                ) else (
                    false
                )
            )
        )
    and dest_gens_in_gens (gens: typ_gens) (dest_gens: typ_gens): bool =
        (*need all the dest_gen in dest_gens to be in gens*)
        List.for_all (dest_gen_in_gens gens) dest_gens
    ;;

    (*a version of the algorithm above with a slightly lighter constraint *)
    let rec dest_gen_used_in_gens (gens: typ_gens) (dest_gen: typ_gen): bool =
        match gens with
        | [] -> false
        | hd::tl -> ((dest_gen_used_in_gen hd dest_gen) || (dest_gen_used_in_gens tl dest_gen))
    and dest_gen_used_in_gen (gen: typ_gen) (dest_gen: typ_gen): bool =
        match gen with
        | Base _ -> (dest_gen = gen)
        | Compound (ctr, gens1, gens2) -> (
            let in_either_side = (dest_gen_used_in_gens gens1 dest_gen) || (dest_gen_used_in_gens gens2 dest_gen) in
            match dest_gen with
            | Base _ -> in_either_side
            | Compound (dest_ctr, dest_gens1, dest_gens2) -> (
                if (dest_ctr = ctr) then (
                    (*either the dest is used in either side or it is exactly representable using both sides *)
                    in_either_side || ((dest_gens_in_gens gens1 dest_gens1) && (dest_gens_in_gens gens2 dest_gens2))
                ) else (
                    in_either_side
                )
            )
        )
    and dest_gens_used_in_gens (gens: typ_gens) (dest_gens: typ_gens): bool =
        (*need all the dest_gen in dest_gens to be in gens  *)
        List.for_all (dest_gen_used_in_gens gens) dest_gens
    ;;

    let is_base_lit (gen_elt: typ_gen): bool =
        match gen_elt with
        | Base Num
        | Base Bool -> true
        | _ -> false
    ;;

    let is_base_lit_or_comp (gen_elt: typ_gen): bool =
        match gen_elt with
        | Base (Hole _) -> false
        | _ -> true
    ;;

    (*helper; call fn below *)
    let rec filter_unneeded_holes_gens (comp: typ_gen -> bool) (remove: bool) (gens: typ_gens): typ_gens =
        match gens with
        | [] -> []
        | hd::tl -> (
            let had_hole, elt_op = filter_unneeded_holes_gen comp remove hd in
            let remove = had_hole || remove in
            match elt_op with
            | None -> filter_unneeded_holes_gens comp remove tl
            | Some hd' -> hd'::(filter_unneeded_holes_gens comp remove tl)
        )
    and filter_unneeded_holes_gen (comp: typ_gen -> bool) (remove: bool) (gen: typ_gen): bool * typ_gen option =
        match gen with
        | Base btyp -> (
            match btyp with
            | Hole _ -> (
                let op = if remove then None else Some gen in
                (true, op)
            )
            | _ -> (false, Some gen)
        )
        | Compound (ctr, gens1, gens2) -> (
            let e_comp1 = List.exists comp gens1 in
            let e_comp2 = List.exists comp gens2 in
            let gens1' = filter_unneeded_holes_gens comp e_comp1 gens1 in
            let gens2' = filter_unneeded_holes_gens comp e_comp2 gens2 in
            (false, (Some (Compound (ctr, gens1', gens2'))))
        )
    ;;

    (*removes all base type holes in the generator that:
        - have a literal as an option in the same position
        - have a compound as an option in the same position
        - are discovered after a needed hole in the same position *)
    let filter_unneeded_holes (comp: typ_gen -> bool) (gens: typ_gens): typ_gens =
        let e_comp = List.exists comp gens in
        filter_unneeded_holes_gens comp e_comp gens
    ;;

    (*returns the solved value associated with a filtered generator IF IT EXISTS; requires gen be nonempty *)
    let rec filtered_solved_val (gens: typ_gens): Typ.t option =
        match gens with
        | [] -> None
        | (Base btyp)::[] -> Some (base_typ_to_typ btyp)
        | (Compound (ctr, gens1, gens2))::[] -> (
            match (filtered_solved_val gens1) with 
            | None -> None
            | Some typ1 -> (
                match (filtered_solved_val gens2) with
                | None -> None
                | Some typ2 -> Some ((Signature.get_mk_of_ctr ctr) typ1 typ2)
            )
        )
        | _ -> None
    ;;

    let comp_gen_elt (gen1: typ_gen) (gen2: typ_gen): int =
        let gen_to_float (gen: typ_gen): float =
            match gen with
            | Base Num
            | Base Bool -> 1.0
            (*the larger the var number, the smaller the  *)
            | Base (Hole var) -> if (var = 0) then 0.0 else (Float.sub 0.0  (Float.div 1.0 (float_of_int var)))
            | Compound _ -> 2.0
        in
        Stdlib.compare (gen_to_float gen1) (gen_to_float gen2)
    ;;

    let rec gens_sort_layer (gens: typ_gens): typ_gens =
        let gens = List.fast_sort comp_gen_elt gens in
        gens_sort_explore gens
    and gens_sort_explore (gens: typ_gens): typ_gens =
        match gens with
        | [] -> []
        | hd::tl -> (
            match hd with
            | Base _ -> hd::(gens_sort_explore tl)
            | Compound (ctr, gens1, gens2) -> (
            let sorted1 = gens_sort_layer gens1 in
            let sorted2 = gens_sort_layer gens2 in
            (Compound (ctr, sorted1, sorted2))::(gens_sort_explore tl)
            )
        )
    ;;
end

module Blacklist = struct
    type err =
        | Invalid
        | Occurs
    
    type t = (Typ.t * err) list

    let rec add_elt (blist: t) (typ_reason: Typ.t * err): t =
        match blist with
        | [] -> [typ_reason]
        | hd::tl -> (
            if (hd = typ_reason) then (
                blist
            ) else (
                hd::(add_elt tl typ_reason)
            )
        )
    ;;

    let merge_blists (bset: t list): t =
        match bset with
        | [] -> []
        | hd::[] -> hd
        | hd::tl -> (
            let acc_cat (acc: t) (elt: t): t =
                List.fold_left add_elt acc elt
            in
            List.fold_left acc_cat hd tl
        )
    ;;

    let has_blacklisted_elt (gens: TypGen.typ_gens) (blist: t): bool =
        let get_key (acc: Typ.t list) (elt: Typ.t * err): Typ.t list =
            let (key, _) = elt in
            key::acc
        in
        let blist_keys = List.fold_left get_key [] blist in
        let blist_inside (key: Typ.t): bool =
            let key_gen = TypGen.typ_to_typ_gen key in
            TypGen.dest_gen_used_in_gens gens key_gen
        in
        List.exists blist_inside blist_keys
    ;;
end

module Status = struct
    (*can be solved of a type or unsolved with a generator containing possible types *)
    type t =
        | Solved of Typ.t
        | UnSolved of TypGen.typ_gens

    type solution = Typ.t * t

    (*this function should only be called during completion *)
    let condense (gens: TypGen.typ_gens) (blist: Blacklist.t): t =
        let gens = TypGen.gens_sort_layer gens in
        if (Blacklist.has_blacklisted_elt gens blist) then (
            let filtered_gens = TypGen.filter_unneeded_holes TypGen.is_base_lit_or_comp gens in
            UnSolved filtered_gens
        ) else (
            let filtered_gens = TypGen.filter_unneeded_holes TypGen.is_base_lit_or_comp gens in
            let solved_op = TypGen.filtered_solved_val filtered_gens in
            match solved_op with
            | Some typ -> Solved typ
            | None -> UnSolved filtered_gens
        )
    ;;
end

module TypGenRes = struct
    (*bool represents occurs check status; if false, condensation will make it unsolved *)
    type t = Typ.t * TypGen.typ_gens

    type results = t list

    let retrieve_gens_for_typ (typ: Typ.t) (gen_results: results): TypGen.typ_gens option =
        let matches (elt: t): bool = 
            let (key, _) = elt in
            key = typ
        in
        let key_value = List.find_opt matches gen_results in
        match key_value with
        | Some (_, value) -> Some value
        | None -> None
    ;;

    let unif_res_to_gen_res (key: Typ.t) (u_res: Typ.unify_result): t =
        let typ_ls = 
            match u_res with
            | Solved ty -> [ty]
            | Ambiguous ((Some ty), tys) -> ty::tys
            | Ambiguous (None, tys) -> tys
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

    let rec replace_gens_of_typ (typ: Typ.t) (replacement: TypGen.typ_gens) (gen_results: results): results =
        match gen_results with
        | [] -> []
        | hd::tl -> (
            let (key, _) = hd in
            if (typ = key) then (
                (key, replacement)::tl
            ) else (
                hd::(replace_gens_of_typ typ replacement tl)
            )
        )
    ;;

    (*constructs a list of all values that can be explored from a typgen given a set of results
    by listing all those types represented in gen that have a result in the result set supplied 
    note:
        the explorable list is simply that: an explorable list detailing all the places that can spawn
        further information within this scope; this does not bar the possibility of explorable locations
        being nested within the types implied by the supplied gens
        in order to generate a proper dfs, be sure to also dfs the most informative types currently seen*)
    let explorable_list (gens: TypGen.typ_gens) (gen_results: results): Typ.t list =
        let get_key (acc: Typ.t list) (elt: t): Typ.t list =
            let (ty, _) = elt in
            ty::acc
        in
        let destinations = List.fold_left get_key [] gen_results in
        let dest_check_and_acc (acc: Typ.t list) (dest: Typ.t): Typ.t list =
            let dest_gen = TypGen.typ_to_typ_gen dest in
            if (TypGen.dest_gen_in_gens gens dest_gen) then (
                dest::acc
            ) else (
                acc
            )
        in
        List.fold_left dest_check_and_acc [] destinations
    ;;

    (*may need to add results for more than just those that have a result-> could be anything with a hole
    however, it could also be that the preservation of all combinations makes it fine
    N->?1 ana against ?3 and ?3 is against B; ?3 is unsolved but ?1 should be too *)
    let link_typ_to_gen (typ: Typ.t) (gens: TypGen.typ_gens) (gen_results: results): results =
        (*typ should be connected to gen in gens if typ has a result in gens
        all elements of gen that are explorable should be linked to typ *)
        let gen_results = 
            match (retrieve_gens_for_typ typ gen_results) with
            | Some gens' -> (
                let updated_gens = TypGen.extend_with_gens gens gens' in
                replace_gens_of_typ typ updated_gens gen_results
            )
            | None -> (
                if (Typ.is_fully_literal typ) then (
                    gen_results
                ) else (
                    (typ, gens)::gen_results
                )
            )
        in
        let to_be_linked_to_typ = explorable_list gens gen_results in
        let update (addition: Typ.t) (acc: results) (key: Typ.t): results =
            match (retrieve_gens_for_typ key acc) with
            | Some gens' -> (
                let updated_gens = TypGen.extend_with_typ gens' addition in
                replace_gens_of_typ key updated_gens acc
            )
            | None -> (
                if (Typ.is_fully_literal typ) then (
                    acc
                ) else (
                    (key, [(TypGen.typ_to_typ_gen addition)])::acc
                )
            )
        in
        List.fold_left (update typ) gen_results to_be_linked_to_typ
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