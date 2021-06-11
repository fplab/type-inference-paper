exception Impossible
open Syntax

(*From the Wikipedia page on Topological Sorts:
"In computer science, a topological sort or topological ordering of a directed
graph is a linear ordering of its vertices such that for every directed edge uv 
from vertex u to vertex v, u comes before v in the ordering." 
https://en.wikipedia.org/wiki/Topological_sorting

The DFS method guides the intuitions of this 'topological sort' of sorts.
Instead of generating a list here, we simply use the access order to immediately perform
relevant computations.

AN EFFICIENCY NOTICE:
sub_on_root_by_dependence is NOT tail recursive.

List.map is NOT tail recursive. 
An alternative that is tail recursive is List.rev (List.rev_map f l)
However, this is (obviously) of a higher constant in its unsimplified complexity.
If stack space is a concern, List.map can be swapped for the rev version.

Another non tail recursive operation is @. This may be fine, but if possible, 
use the smaller list first or try to use the simple item::list instead of [item] @ list
(cat is length of the first argument)
    If order doesn't matter, consider List.rev_append!
*)

(********************)
(*current code assumes a hole won't solve to itself (ie no loops). It would seem the code does so, but unclear! *)
(*cycle management not implemented yet; standard methods for detecting include methods that occur during the search
like marking visited nodes. Anand mentioned algorithms that detect cycles as well. Whatever is done, ideally, should
be able to resolve nodes not dependent on the cycle equivalence and ignore those involved or dependent on it. What is
to be reported for such variables is TBD *)
(********************)

module CycleTrack = struct
    type t = TypeInferenceVar.t list

    let empty : t = [];;

    let track_var (var: TypeInferenceVar.t) (vars: t): t =
        var::vars
    ;;

    let is_tracked (var: TypeInferenceVar.t) (vars: t): bool =
        let is_var (scrut: TypeInferenceVar.t): bool =
            var == scrut
        in
        List.exists is_var vars
    ;;
end

(*a sub result is some updated set of unify_results after resolving dependencies to simplest form and the result associated 
with the root called upon *)
type sub_result = Typ.unify_results * Typ.unify_result

(*  A node can be:
        -free from cycles in its dependencies, 
        -cyclic,
            where it is directly involved in a cycle,
            and its name is not substituted out 
        -or dependently cyclic, 
            where it is consistent, through some path, with at least one cycle
            a dependently cyclic node can theoretically be involved in the path to multiple cycles once all
            children are evaluated. Thus, a dependently cyclic node is associated with a set of cycle paths,
            each of which maps to a cyclic node to which all involved could be resolved to *)
type sub_status = 
    | SubSuccess of sub_result
    | Cyclic of TypeInferenceVar.t 
    | DependentlyCyclic of sub_result * (TypeInferenceVar.t list)

(* checks if the type of var is used to determine the type of any other type infernce variable
    i.e. if the result type of any variable depends on var's result*)
let inf_var_is_depended_upon (var: TypeInferenceVar.t) (result_list: Typ.unify_result list)
    : bool =
    let result_contains_var (result: Typ.unify_result): bool =
        match result with
        | Solved ty -> (Typ.contains_var var ty)
        | UnSolved tys -> (List.exists (Typ.contains_var var) tys)
    in
    List.exists result_contains_var result_list
;;

(* retrieve's an inference variables associated solution in the results list (if present) *)
let rec retrieve_result_for_inf_var (var: TypeInferenceVar.t) (results: Typ.unify_results)
    : Typ.unify_result option =
    match results with
    | [] -> None
    | (ty_var, result)::tl -> (
        if (ty_var == var) then (Some result) else retrieve_result_for_inf_var var tl
    )
;;

(* Searches for instances of target within the type's tree structure and replaces if found *)
let rec find_and_replace (target: TypeInferenceVar.t) (replacement: Typ.t) (ty: Typ.t)
    : Typ.t =
    let replace_target_in = find_and_replace target replacement in
    match ty with
    | TArrow (ty1, ty2) -> TArrow ((replace_target_in ty1), (replace_target_in ty2))
    | TProd (ty1, ty2) -> TProd ((replace_target_in ty1), (replace_target_in ty2))
    | TSum (ty1, ty2) -> TSum ((replace_target_in ty1), (replace_target_in ty2))
    | THole ty_var -> if (ty_var == target) then replacement else ty
    | _ -> ty
;;

(*Iterates through unify_results to replace all instances of target with ty. 
    Isolates target from the tree in that no references to it exist in any referenced types*)
let sub_inf_var_for_child (target: TypeInferenceVar.t) (child: Typ.unify_result) (results: Typ.unify_results)
    : Typ.unify_results = 
    (* a function to map over all unify_result values in results that performs necessary substitutions *)
    let sub_on_res (var_with_res: (TypeInferenceVar.t * Typ.unify_result))
        : (TypeInferenceVar.t * Typ.unify_result) =
        let (var, result) = var_with_res in
        (*if at the variable itself, then replace its value with the child *)
        if (var == target) then (
            (var, child)
        )
        else (
            (*A function to potentially fold with that accumulates all unsolved types through replacements in the provided list 
            the boolean in the return type is to denote if substitution occurred or not; this is useful to determine is the result is
            solved or unsolved in the case where the var scrutinized is solved but the child is unsolved (not useful otherwise)*)
            let accumulate_unsolved_by_list (replacements: Typ.t list) (acc: (bool * Typ.t list)) (base_ty: Typ.t)
                : (bool * Typ.t list) =
                let (changed, acc_list) = acc in
                (*to avoid excessive computation, first check if target is in the base_ty *)
                if (Typ.contains_var target base_ty) then (
                    (*a function to fold with that accumulates a type through a single replacement*)
                    let accumulate_unsolved_by_single (acc_s: Typ.t list) (replacement_ty: Typ.t)
                        : Typ.t list =
                        (find_and_replace target replacement_ty base_ty)::acc_s
                    in
                    let extended = List.fold_left accumulate_unsolved_by_single acc_list replacements in
                    (true, extended)
                ) else (
                    (changed || false, base_ty::acc_list)
                )
            in
            (*match on the result associated with the variable 
            if both single types, find and replace target with child in the result 
            if result is single but child is many, accumulate unsolved *)
            match result with
            | Solved var_ty -> (
                match child with
                | Solved child_ty -> (var, Solved (find_and_replace target child_ty var_ty)) 
                | UnSolved child_tys -> (
                    let (changed, sub_list) = accumulate_unsolved_by_list child_tys (false, []) var_ty in
                    if (changed) then (var, UnSolved (sub_list)) else var_with_res
                )
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
                | UnSolved child_tys -> (
                    let (_, adjusted_var_tys) = 
                        List.fold_left (accumulate_unsolved_by_list child_tys) (false, []) var_tys
                    in
                    (var, UnSolved adjusted_var_tys)
                )
            )
        )
    in
    (*given how large sub_on_res is, it may be a bad idea to use it non tail recursively. hence, the rev method is used *)
    (* the list is reverted in order to give more consistency in output (and make debugging easier) *)
    List.rev (List.rev_map sub_on_res results)
;;

(*recurses on the root node specified and adjusts each var solution to its most basic (most independent/literal) value*)
(*each call returns the current adjusted set of results and the unify_result associated with the recursed upon node *)
(*if a node's children are known to be inconsistent, all dependent nodes will also be rendered UnSolved *)
(*
ex:     THole 0 = Solved THole 1
        THole 1 =  UnSolved TNum TBool
    will resolve to
        THole 0 = UnSolved TNum TBool
        THole 1 = UnSolved TNum TBool
*)
let rec sub_on_root_by_dependence (root: Typ.t) (results: Typ.unify_results) (tracked: CycleTrack.t)
    : sub_status =
    match root with
    | TBool -> SubSuccess (results, Solved TBool)
    | TNum -> SubSuccess (results, Solved TNum)
    | TArrow (ty1, ty2) -> sub_two_of_constructor Typ.mk_arrow ty1 ty2 results tracked
    | TProd (ty1, ty2) -> sub_two_of_constructor Typ.mk_prod ty1 ty2 results tracked
    | TSum (ty1, ty2) -> sub_two_of_constructor Typ.mk_sum ty1 ty2 results tracked
    | THole var -> (
        match (CycleTrack.is_tracked var tracked) with
        | true -> (
            (*A cycle exists; stop evaluation to prevent looping. Node resolved to itself*)
            (*since there is no viable simplifying solution, it is not substituted out of the tree;
            all direct references it it or those dependent on it will be rendered DependentlyCyclic*)
            Cyclic var
        )
        | false -> (
            (*no cycle found with this node yet. proceed as usual, and track the variable *)
            let tracked = CycleTrack.track_var var tracked in
            match (retrieve_result_for_inf_var var results) with
            | Some unif_res -> (
                match unif_res with
                | Solved ty -> (
                    let subres = sub_on_root_by_dependence ty results tracked in
                    match subres with 
                    | SubSuccess (results, result_sol) -> (
                        SubSuccess ((sub_inf_var_for_child var result_sol results), result_sol)
                    )
                    | Cyclic cyc -> (
                        let result_sol: Typ.unify_result = Solved (THole cyc) in
                        DependentlyCyclic (((sub_inf_var_for_child var result_sol results), result_sol), cyc::[])
                    )
                    | DependentlyCyclic ((results, result_sol), cycles) -> (
                        DependentlyCyclic (((sub_inf_var_for_child var result_sol results), result_sol), cycles)
                    )
                )
                | UnSolved tys -> (
                    (*the following function accumulates the current state of the unify results and list set
                    by taking the current state and a new child's type and updating the state by recursing on the type *)
                    let recurse_and_accumulate (acc: (Typ.unify_results * (Typ.t list) * (TypeInferenceVar.t list) * bool)) (ty: Typ.t)
                        : (Typ.unify_results * (Typ.t list) * (TypeInferenceVar.t list) * bool) =
                        let (curr_results, curr_list, cycles, found_cyc) = acc in
                        let res_to_ty_list (unify_res: Typ.unify_result): Typ.t list = 
                            match unify_res with
                            | Solved single_ty -> [single_ty]
                            | UnSolved tys -> tys
                        in
                        match (sub_on_root_by_dependence ty curr_results tracked) with
                        | SubSuccess (updated_results, result_sol) -> (
                            let updated_list = List.rev_append (res_to_ty_list result_sol) curr_list in
                            (updated_results, updated_list, cycles, found_cyc)
                        )
                        | Cyclic cyc -> (
                            (curr_results, (THole cyc)::curr_list, cyc::cycles, true)
                        )
                        | DependentlyCyclic ((updated_results, result_sol), new_cycles) -> (
                            let updated_list = List.rev_append (res_to_ty_list result_sol) curr_list in
                            let updated_cycles = List.rev_append new_cycles cycles in
                            (updated_results, updated_list, updated_cycles, true)
                        )
                    in
                    let (results, inconsistency_list, cycles, found_cyc) = 
                        List.fold_left recurse_and_accumulate (results, [], [], false) tys 
                    in
                    let child_res: Typ.unify_result =  UnSolved inconsistency_list in
                    if (found_cyc) then (
                        SubSuccess ((sub_inf_var_for_child var child_res results), child_res)
                    )
                    else (
                        DependentlyCyclic (((sub_inf_var_for_child var child_res results), child_res), cycles)
                    )
                )
            )
            | None -> (
                raise Impossible (* list of unification results itself was used to generate variable names used; must be present *)
            )
        )
    )
(* a common instance for recursive types *)
and sub_two_of_constructor (ctr: Typ.t -> Typ.t -> Typ.t) (ty1: Typ.t) (ty2: Typ.t) (results: Typ.unify_results) (tracked: CycleTrack.t)
    : sub_status =
    let sub_res_ty1 = sub_on_root_by_dependence ty1 results tracked in
    let (results, result_ty1, cycles1, has_cyc1) =
        match sub_res_ty1 with
        | SubSuccess (updated_results, result_sol1) -> (updated_results, result_sol1, [], false)
        | Cyclic cyc -> (results, Solved (THole cyc), cyc::[], true)
        | DependentlyCyclic ((updated_results, result_sol1), cycles1) -> (updated_results, result_sol1, cycles1, true)
    in
    let sub_res_ty2 = sub_on_root_by_dependence ty2 results tracked in
    let (results, result_ty2, cycles2, has_cyc2) =
        match sub_res_ty2 with
        | SubSuccess (updated_results, result_sol2) -> (updated_results, result_sol2, [], false)
        | Cyclic cyc -> (results, Solved (THole cyc), cyc::[], true)
        | DependentlyCyclic ((updated_results, result_sol2), cycles2) -> (updated_results, result_sol2, cycles2, true)
    in
    let mk_ctr_types (ctr: Typ.t -> Typ.t -> Typ.t) (const: Typ.t) (const_is_left: bool) (acc: Typ.t list) (variant: Typ.t)
        : Typ.t list =
        if (const_is_left) then (ctr const variant)::acc else (ctr variant const)::acc
    in
    let updated_unify_result : Typ.unify_result =
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
    in
    if (has_cyc1 || has_cyc2) then (
        DependentlyCyclic ((results, updated_unify_result), (List.rev_append cycles1 cycles2))
    ) else (
        SubSuccess (results, updated_unify_result)
    )
;;

(*Performs a topological sort on the unify results by interpreting it as an adjacency list*)
(*Performs substitution in order based on type dependencies *)
let top_sort_and_sub (results: Typ.unify_results)
    : Typ.unify_results * (TypeInferenceVar.t list) = 
    (*Find roots; a root corresponds to a variable that no variables are dependent on (no incoming edges)*)
    let var_list = Typ.extract_var_list results in
    let result_list =  Typ.extract_result_list results in
    let tuple_dependencies (var: TypeInferenceVar.t): (TypeInferenceVar.t * bool) = 
        (var, (inf_var_is_depended_upon var result_list))
    in
    let vars_with_dependency = List.map tuple_dependencies var_list in
    let wrap_not_depended (tuple: TypeInferenceVar.t * bool): Typ.t option =
        match tuple with
        | (_, true) -> None
        | (var, false) -> Some(THole var)
    in
    (*generate the root list from all variables that are not depended upon by filtering None's*)
    let root_list = List.filter_map wrap_not_depended vars_with_dependency in
    (*update the unify_results by successively passing its current state to be resolved by substitution along each root node*)
    (*folding sub on root is a wrapped version of sub_on_root_by_dependence for fold_left*)
    let folding_sub_on_root (acc: Typ.unify_results * (TypeInferenceVar.t list)) (root: Typ.t)
        : Typ.unify_results * (TypeInferenceVar.t list) =
        let acc_res, acc_cycles = acc in
        match (sub_on_root_by_dependence root acc_res CycleTrack.empty) with
        | SubSuccess (results, _) -> (results, acc_cycles)
        | Cyclic cyc -> (acc_res, cyc::acc_cycles)
        | DependentlyCyclic ((results, _), new_cycles) -> (results, (List.rev_append new_cycles acc_cycles))
    in
    let results_and_cycles = List.fold_left folding_sub_on_root (results, []) root_list in
    results_and_cycles
;;

(*The following three functions do not seem to have use anymore:
    - old intended use: to remove any elements rendered consistent with others after a substitution
    - reason for lack thereof: only holes are substituted. If known as an inconsistent set, replacing 
                            holes will never increase consistency*)

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
        let tl = List.fold_left (@) [] tl in
        smallest_inconsistent_pair hd tl
;;
