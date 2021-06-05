exception Impossible
open Syntax

(*
    AN EFFICIENCY NOTICE: List.map is NOT tail recursive. 
    An alternative that is tail recursive is List.rev (List.rev_map f l)
    However, this is (obviously) of a higher constant in its unsimplified complexity.
    If stack space is a concern, List.map can be swapped for the rev version.

    Another non tail recursive operation is @. This may be fine, but if possible, 
    use the smaller list first or try to use the simple item::list instead of [item] @ list
    (cat is length of the first argument)
 *)

(* checks if the type of var is used to determine the type of any other type infernce variable *)
let inf_var_is_depended_upon (var: TypeInferenceVar.t) (result_list: Typ.unify_result list)
    : bool =
    let result_contains_var (result: Typ.unify_result): bool =
        match ty with
        | Solved ty -> (Typ.contains_var ty)
        | Unsolved tys -> (List.exists Typ.contains_var tys)
    in
    List.exists result_contains_var result_list
;;

(*current code assumes a hole won't solve to itself (ie no loops). It would seem the code does so, but unclear! *)
(* cycle management not implemented yet *)
(*Performs a topological sort on the unify results by interpreting it as an adjacency list *)
(*Performs substitution in order based on type dependencies *)
let top_sort_and_sub (results: Typ.unify_results)
    : Typ.unify_results = 
    (* Find most dependent nodes; 
        a 'most dependent node' corresponds to a variable that no variables are dependent on*)
    let var_list = Typ.extract_var_list results in
    let result_list =  Typ.extract_result_list results in
    let tuple_dependencies (var: TypeInferenceVar.t): (TypeInferenceVar.t * bool) = 
        (var, (inf_var_is_depended_upon var result_list))
    in
    let vars_with_dependency = List.map tuple_dependencies var_list in
    let wrap_not_depended (tuple: TypeInferenceVar.t * bool): Typ.t option =
        match tuple with
        | (var, true) -> None
        | (var, false) -> Some(THole var)
    in
    (* generate the root list from all variables that are not depended upon *)
    let root_list = List.filter_map wrap_not_depended vars_with_dependency in
    (* 
    update the unify_results by successively passing its current state to be resolved by substitution along each root node 
        function:    acc -> list_item -> acc: sub_on_root_by_dependence
        accumulator: unify_results, unify_result*^
        list_item:   root_list
    *^NOTE: the type in the accumulator is solely for efficiency within the function and its initial value has no effect
    *)
    let (results, _) = List.fold_left sub_on_root_by_dependence (results, Solved TNum) root_list in
    results
;;

(* recurses on the root node specified and recursively adjusts each solution to its most basic (most independent/literal) value*)
(* each call returns the current adjusted set of results and the unify_result associated with the recursed upon node *)
(*if a node's children are known to be inconsistent, all nodes receiving data from this should know *)
(*however, all subtrees may still be able to be resolved further, even if parents cannot *)
(*
currently all UnSolved instances due to inconsistencies will be propogated upward
ex:     THole 0 = Solved THole 1
        THole 1 =  UnSolved TNum TBool
    will resolve to
        THole 0 = UnSolved TNum TBool
        THole 1 = UnSolved TNum TBool
*)
let rec sub_on_root_by_dependence (results: Typ.unify_results) (root: Typ.t)
    : (Typ.unify_results * Typ.unify_result) = 
    (* If at a leaf node, return self *)
    (* If at an intermediate node, use result of recursion of children to sub for self using
    sub_inf_var_for_child. Return resultant list*)
    match root with
    | TBool -> (results, TBool)
    | TNum -> (results, TNum)
    | TArrow (ty1, ty2) -> sub_two_of_constructor Typ.mk_arrow ty1 ty2
    | TProd (ty1, ty2) -> sub_two_of_constructor Typ.mk_prod ty1 ty2
    | TSum (ty1, ty2) -> sub_two_of_constructor Typ.mk_sum ty1 ty2
    | THole var -> (
        match (retrieve_results_for_inf_var var) with
        | Some unif_res -> (
            match unif_res with
            | Solved ty -> (
                let (results, result_ty) = sub_on_root_by_dependence results ty in
                sub_inf_var_for_child results var result_ty
            )
            | Unsolved tys -> (
                (*the following function accumulates the current state of the unify results and list set
                by taking the current state and a new child's type and updating the state by recursing on the type *)
                let recurse_and_accumulate (acc: (Typ.unify_results * (Typ.t list) list)) (ty: Typ.t)
                    : (Typ.unify_results * (Typ.t list) list) =
                    let (curr_results, curr_list) = acc in
                    let (updated_results, unify_res) = sub_on_root_by_dependence results ty in
                    let ty_results = 
                        match unify_res with
                        | Solved single_ty -> [single_ty]
                        | UnSolved tys -> tys
                    in
                    (updated_results, ty_results @ cur_list)
                in
                let (results, inconsistency_set) = List.fold_left recurse_and_acc (results, []) tys in
                (results, (smallest_inconsistent_set inconsistency_set))
            )
        )
        | None -> raise Impossible (* list of unification results itself was used to generate variable names used; must be present *)
    )
(* a common instance for recursive types *)
and sub_two_of_constructor (ctr: (Typ.t -> Typ.t) -> Typ.t) (ty1: Typ.t) (ty2: Typ.t)
    : (Typ.unify_results * Typ.unify_result) =
    let (results, result_ty1) = sub_on_root_by_dependence results ty1 in
    let (results, result_ty2) = sub_on_root_by_dependence results ty2 in
    let updated_unify_result =
        match (resolved_ty1, resolved_ty2) with
        | ((Solved resolved_ty1), (Solved resolved_ty2)) -> Solved (ctr resolved_ty1 resolved_ty2)
        | ((UnSolved tys), (Solved resolved_ty2)) -> UnSolved (cat_if_inconsistent_for_all resolved_ty2 tys)
        | ((Solved resolved_ty1), (UnSolved tys)) -> Unsolved (cat_if_inconsistent_for_all resolved_ty1 tys)
        | ((UnSolved tys1), (UnSolved tys2)) -> UnSolved (smallest_inconsistent_pair tys1 tys2)
    in
    (results, updated_unify_result)
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

(* A generalized version of smallest_inconsistent_pair that simply concatenates the tail of a list set to be used in pair *)
let smallest_inconsistent_set (list_set: (Typ.t list) list)
    : Typ.t list =
    match list_set with
    | [] -> []
    | hd::tl -> 
        let tl = List.fold_left tl [] (@) in
        smallest_inconsistent_pair hd tl
;;

(* retrieve's an inference variables associated solution in the results list (if present) *)
let rec retrieve_results_for_inf_var (results: Typ.unify_results) (var: TypeInferenceVar.t)
    : Typ.unify_result option =
    match results with
    | [] -> None
    | ((THole ty_var), result)::tl -> (
        if (ty_var == var) then (Some result) else retrieve_results_for_inf_var tl var
    )
    | _::tl -> retrieve_results_for_inf_var tl var
;;

(* Searches for instances of target within the type's tree structure and replaces if found *)
let rec find_and_replace (target: TypeInferenceVar.t) (replacement: Typ.t) (ty: Typ.t)
    : Typ.t =
    let replace_target_in = find_and_replace target replacement in
    match ty with
    | TArrow (ty1, ty2) -> TArrow ((replace_target_in ty1) (replace_target_in ty1))
    | TProd (ty1, ty2) -> TProd ((replace_target_in ty1) (replace_target_in ty1))
    | TSum (ty1, ty2) -> TSum ((replace_target_in ty1) (replace_target_in ty1))
    | THole ty_var -> if (ty_var == var) then replacement else ty
    | _ -> ty
;;

(*Iterates through unify_results to replace all instances of target with ty. 
    Isolates target from the tree in that no references to it exist in any referenced types*)
(*Map. 
    Perform a function (described indented) that maps (TypeInferenceVar.t * Typ.unify_result) 
    to a new such type value adjusted as described below
        For each elt of the results list extract the results in the var * unify_result item
            Manage the unify_result status
                If the type in the result status matches: (cases below in terms of scrutinized result)
                    If currently Solved target and substituting a child that is Solved,
                    simply replace the unify_result status with the child value

                    If currently Solved target and substituting a child that is UnSolved, 
                    change to UnSolved by simply replacing the unify_result status
                    with the child's (this is okay as Solved only has one type: the child)

                    If currently UnSolved with a list containing target and substituting a 
                    child that is Solved, remove the var id. Next, cat the type contained in 
                    the child's Solved status with the Unsolved type list through using
                    cat_if_inconsistent_for_all

                    If currently UnSolved with a list containing target and substituting a child
                    that is UnSolved, remove the var id. Next, merge the UnSolved lists through
                    smallest_inconsistent_pair.
                If the type doesn't match:
                    Move on to the next variable *)
let sub_inf_var_for_child (results: Typ.unify_results) (target: TypeInferenceVar.t) (child: Typ.unify_result)
    : Typ.unify_results = 
    let sub_on_res (var_with_res: (TypeInferenceVar.t * Typ.unify_result))
        : (TypeInferenceVar.t * Typ.unify_result) =
        let (var, result) = var_with_res in
        if (var == target) then (
            (var, child)
        )
        else (
            let accumulate_unsolved_by_list (replacements: Typ.t list) (acc: Typ.t list) (base_ty: Typ.t)
                : Typ.t list =
                (*to avoid potential excessive computation *)
                if (Typ.contains_var target base_ty) then (
                    let accumulate_unsolved_by_single (acc_s: Typ.t list) (replacement_ty: Typ.t)
                        : Typ.t list =
                        (find_and_replace target replacement_ty base_ty)::acc_s
                    in
                    (*for efficiency in empty accumulator case*)
                    let addition = (List.fold_left accumulate_unsolved_by_single [] replacements) in
                    match acc with
                    | [] -> addition
                    | _ -> addition @ acc
                ) else (
                    base_ty::acc
                )
            in
            match result with
            | Solved var_ty -> (
                match child with
                | Solved child_ty -> (var, Solved (find_and_replace target child_ty var_ty))
                | UnSolved child_tys -> (var, UnSolved (accumulate_unsolved_by_list child_tys [] var_ty))
            )
            | UnSolved var_tys -> (
                (*note that they are already inconsistent without the type hole being replaced. inserting one only decreases their generality
                and will not result in consistency*)
                match child with
                | Solved child_ty -> (
                    let find_and_replace_wrapper (acc: Typ.t list) (ty: Typ.t): Typ.t list =
                        (find_and_replace target child_ty ty)::acc
                    in
                    (var, UnSolved (List.fold_left find_and_replace_wrapper [] var_tys))
                )
                | UnSolved child_tys -> (var, UnSolved (List.fold_left (accumulate_unsolved_by_list child_tys) [] var_tys))
            )
        )
    in
    (*given how large sub_on_res is, it may be a bad idea to use it non tail recursively. hence, the rev method is used *)
    List.rev(List.rev_map sub_on_res results)
;;