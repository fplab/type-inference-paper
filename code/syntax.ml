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

    type unify_result =
        | Solved of t
        | UnSolved of (t list)

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
        | THole ty_var -> (ty_var == var)
        | _ -> false
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
        | hd::tl -> hd==typ || (in_dom tl typ)
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
