open Union
module Identifier = struct
    type t = string
end

module TypeInferenceVar = struct
    type t = int
    let recent (var_1:t) (var_2:t) = max var_1 var_2;; 
    type holes_repl_set = UnionFind.t
    
    let group_create n = UnionFind.create n;;
    let get_group (holes_repl_set:holes_repl_set) (var: t) = 
        UnionFind.get_group holes_repl_set var;;
    
    let rec group_union (sorted_ls1: t list) (sorted_ls2: t list) =
        match (sorted_ls1, sorted_ls2) with
        | ([], ls) | (ls, []) -> ls
        | (hd1::tl1, hd2::tl2) -> 
            if hd1<hd2 then [hd1]@(group_union tl1 sorted_ls2)
            else if hd1>hd2 then [hd2]@(group_union tl2 sorted_ls1)
            else [hd1]@(group_union tl1 tl2)
    ;;

    let rec group_inter (sorted_ls1: t list) (sorted_ls2: t list) =
        match (sorted_ls1, sorted_ls2) with
        | ([], _) | (_, []) -> []
        | (hd1::tl1, hd2::tl2) -> 
            if hd1<hd2 then (group_inter tl1 sorted_ls2)
            else if hd1>hd2 then (group_inter tl2 sorted_ls1)
            else [hd1]@(group_inter tl1 tl2)
    ;;
    let disconnect (holes_repl_set:holes_repl_set) (var:t) = UnionFind.disconnect holes_repl_set var;;
    let rec disconnect_ls (holes_repl_set:holes_repl_set) (var_ls:t list) = 
        match var_ls with
        | [] -> ();
        | hd::tl -> 
            disconnect holes_repl_set hd; 
            disconnect_ls holes_repl_set tl;;

    let union (holes_repl_set:holes_repl_set) (var1:t) (var2:t) = UnionFind.union holes_repl_set var1 var2;;
end

module Typ = struct
    type t =
        | THole of TypeInferenceVar.t
        | TNum
        | TArrow of t * t

    type unify_result = 
        | Solved of t
        | UnSolved of (t list)

    type unify_results  = (TypeInferenceVar.t * unify_result) list

    let rec in_dom lst typ = 
        match lst with
        | [] -> false
        | hd::tl -> hd==typ || (in_dom tl typ)
    ;;
    let rec find_result (var: TypeInferenceVar.t) (unify_results: unify_results): unify_result option = 
        match unify_results with
        | [] -> None
        | hd::tl -> 
            let (v, result) = hd in
            if (v == var) then (Some result)
            else (find_result var tl)
    ;;
    let rec add_to_unsolved_ls (var: TypeInferenceVar.t) (typ: t) (unify_results: unify_results): unify_results = 
        match unify_results with
        | [] -> []
        | hd::tl -> 
            let (v, result) = hd in
            if (v == var) then (
                match result with
                | Solved _ -> unify_results
                | UnSolved ls ->
                if (in_dom ls typ) then unify_results else
                ((v, UnSolved (ls @ [typ]))::tl)
            )
            else hd::(add_to_unsolved_ls var typ tl)
    ;;

    let rec erase_results (var1: TypeInferenceVar.t) (var2: TypeInferenceVar.t) (unify_results: unify_results) =
        match unify_results with
        | [] -> []
        | hd::tl -> 
            let (v, _) = hd in
            if (v == var1 || v == var2) then (erase_results var1 var2 tl)
            else hd::(erase_results var1 var2 tl)

    let  merge_unsolved_ls (var1: TypeInferenceVar.t) (ls1: t list) (var2: TypeInferenceVar.t) (ls2: t list) (unify_results: unify_results): unify_results = 
        let rec merge_typ_lst (ls1: t list) (ls2: t list) =
            match ls1 with
            | [] -> ls2
            | hd::tl ->  
                if (in_dom ls2 hd) then 
                (merge_typ_lst tl ls2) else
                (merge_typ_lst tl (ls2)@[hd])
        in  let unsolved_ls =  merge_typ_lst ls1 ls2 in
        (erase_results var1 var2 unify_results) @ [(var1, UnSolved unsolved_ls); (var2, UnSolved unsolved_ls)]
    ;;
    let type_variable = ref (0)

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
        | TNum -> ()
        | TArrow (ty1,ty2)-> (
        load_type_variable(ty1);
        load_type_variable(ty2);
        )
end


module Exp = struct

    type hole_id = int

    type binop = OpAp | OpPlus

    type t =
        | EVar of Identifier.t
        | ELam of Identifier.t * t
        | ELamAnn of Identifier.t * Typ.t * t
        | EBinOp of t * binop * t
        | ENumLiteral of int
        | EAsc of t * Typ.t
        | EEmptyHole of hole_id
        | EExpHole of hole_id * t
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



(* module SubTyp = struct
  type t =
    | HoleSubs of TypeInfVarSet.t * typ
    | Primitive of typ
  and typ =
    | STHole of TypeInferenceVar.t
    | STNum
    | STArrow of t * t
end
 *)
module Constraints = struct
  type consistent = Typ.t * Typ.t

  type t = consistent list
end