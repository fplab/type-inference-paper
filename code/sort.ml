exception Impossible
open Syntax

(* checks if the type of var is used to determine the type of any other type infernce variable *)
let inf_var_is_depended_upon (var: TypeInferenceVar.t) (result_list: Typ.unify_result list)
    : bool =
    let is_var (ty: Typ.t): bool = 
        match ty with
        | Hole ty_var -> (ty_var == var)
        | _ -> false
    in
    let contains_var (result: Typ.unify_result): bool =
        match ty with
        | Solved ty -> (is_var ty)
        | Unsolved tys -> (
            let conjunct_is_var (acc: bool) (ty: Typ.t): bool = 
                (acc || (is_var ty)) 
            in
            List.fold_left conjunct_is_var false equiv_list
        )
    in
    List.fold_left contains_var false result_list
;;

(*current code assumes a hole won't solve to itself (ie no loops). It would seem the code does so, but unclear! *)
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
                let (results, resolved_ty) = sub_on_root_by_dependence results ty in
                (*INCORRECT: needs to check if the result was unsolved and adjust accordingly if so *)
                sub_inf_var_for_child results var (Solved resolved_ty)
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
and sub_two_of_constructor (ctr: (Typ.t -> Typ.t) -> Typ.t) (ty1: Typ.t) (ty2: Typ.2)
    : (Typ.unify_results * Typ.unify_result) =
    let (results, result_ty1) = sub_on_root_by_dependence results ty1 in
    let (results, result_ty2) = sub_on_root_by_dependence results ty2 in
    let updated_unify_result =
        match (resolved_ty1, resolved_ty2) with
        | ((Solved resolved_ty1), (Solved resolved_ty2)) -> Solved (ctr resolved_ty1 resolved_ty2)
        | ((UnSolved tys), (Solved resolved_ty2)) -> UnSolved cat_if_inconsistent_for_all resolved_ty2 tys
        | ((Solved resolved_ty1), (UnSolved tys)) -> Unsolved cat_if_inconsistent_for_all resolved_ty1 tys
        | ((UnSolved tys1), (UnSolved tys2)) -> UnSolved smallest_inconsistent_pair tys1 tys2
    in
    (results, updated_unify_result)
;;

let cat_if_inconsistent_for_all (target_list: Typ.t list) (item: Typ.t)
    : Typ.t list =
    let any_is_consistent (acc: bool) (ty: Typ.t): bool = 
        acc || (Typ.consistent item ty)
    in
    let any_consistent_for_all = 
        List.fold_left any_is_consistent false target_list 
    in
    if (any_consistent_for_all) then (
        target_list
    ) else (
        item::target_list
    )
;;

let smallest_inconsistent_pair (l1: Typ.t list) (l2: Typ.t list)
    : Typ.t list =
    List.fold_left cat_if_inconsistent_for_all l1 l2
;;

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
        if (ty_var == var) then (
            (Some result)
        ) else (
            retrieve_results_for_inf_var tl var
        )
    )
    | _::tl -> (
        retrieve_results_for_inf_var tl var
    )

(*Iterates through unify_results to replace all instances of target with ty. Isolates target from the tree *)
let sub_inf_var_for_child (results: Typ.unify_results) (target: TypeInferenceVar.t) (child: Typ.unify_result)
    : Typ.unify_results = 
    
    results
;;