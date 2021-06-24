module Identifier = struct
    type t = string
end

module TypeInferenceVar = struct
    type t = int
    let recent (var_1:t) (var_2:t) = max var_1 var_2;; 
end

(*Only missing types: Float and list*)
module Typ = struct
    type t =
        | THole of TypeInferenceVar.t
        | TBool
        | TNum
        | TArrow of t * t
        | TProd of t * t
        | TSum of t * t
    
    type dir =
        | L
        | R

    type dir_status = 
        | Arrow of dir
        | Sum of dir
        | Prod of dir

    type utyp =
        | Standard of t
        | SidedHole of utyp * dir_status

    type unify_result = 
        | Solved of utyp
        | Ambiguous of (t option) * (utyp list)
        | UnSolved of (utyp list)

    type unify_results  = (TypeInferenceVar.t * unify_result) list

    (*New helpers to construct recursive types *)
    let mk_arrow (ty1: t) (ty2: t): t = TArrow (ty1, ty2);;
    let mk_prod (ty1: t) (ty2: t): t = TProd (ty1, ty2);;
    let mk_sum (ty1: t) (ty2: t): t = TSum (ty1, ty2);;


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

    (* Need to consider: OpDiv, OpTimes, OpMinus, and float operators if float added; rules should be the same *)
    type binop = OpAp | OpPlus

    (*Floatlit, ListNil, ApPalette (?), Invalid text. Probably no interesting or new constraint rules for these*)
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