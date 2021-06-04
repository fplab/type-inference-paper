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
    let wrap_not_depended (tuple: TypeInferenceVar.t * bool): TypeInferenceVar.t option =
        match tuple with
        | (var, true) -> None
        | (var, false) -> Some(var)
    in
    (* generate the root list from all variables that are not depended upon *)
    let root_list = List.filter_map wrap_not_depended vars_with_dependency in
    (* update the unify_results by successively passing its current state to be resolved by substitution along each root node 
        function of type acc -> list_item -> acc: sub_on_root_by_dependence
        accumulator: unify_results
        list_item: roots *)
    List.fold_left sub_on_root_by_dependence results root_list
;;

(* recurses on the root node specified and recursively adjusts each solution to its most basic (most independent/literal) value*)
let rec sub_on_root_by_dependence (results: Typ.unify_results) (root: TypeInferenceVar.t)
    : Typ.unify_results = 
    (* If at a leaf node, return self *)
    (* If at an intermediate node, use result of recursion of children to sub for self using
    sub_inf_var_for_child. Return resultant list*)
    results
;;

(*Iterates through unify_results to replace all instances of target with ty. Isolates target from the tree *)
let sub_inf_var_for_child (results: Typ.unify_results) (target: TypeInferenceVar.t) (ty: Typ.t)
    : Typ.unify_results = 
    
    results
;;