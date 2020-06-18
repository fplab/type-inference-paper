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
        | TNum
        | TArrow of t * t

    type subs = (TypeInferenceVar.t * t) list
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

module Constraints = struct
    type consistent = Typ.t * Typ.t

    type t = consistent list

    let empty : t = []
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