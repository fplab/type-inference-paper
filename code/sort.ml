open Syntax

(*Performs a topological sort on the unify results by interpreting it as an adjacency list *)
(*Performs substitution in order based on type dependencies *)
let top_sort_and_sub (results: Typ.unify_results)
    : Typ.unify_results = 
    (*Find most dependent nodes *)
    (*tree recurse on each 'most dependent node' to substitute*)
    results
;;

(* recurses on the root node specified and recursively adjusts each solution to its most basic value*)
let rec dependently_sub_on_root (results: Typ.unify_results) (root: TypeInferenceVar.t)
    : Typ.unify_results = 
    results
;;

(*Iterates through unify_results to replace all instances of target with ty. Isolates target from the tree *)
let sub_inf_var_for_child (results: Typ.unify_results) (target: TypeInferenceVar.t) (ty: Typ.t)
    : Typ.unify_results = 
    results
;;