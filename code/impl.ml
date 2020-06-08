exception NotImplemented

module Identifier = struct
  type t = string
end


module Typ = struct
  type hole_id = int
  type t =
    | THole of hole_id
    | TNum
    | TArrow of t * t
end

module Exp = struct

  type hole_id = int

  type op = OpAp | OpPlus

  type t =
    | EVar of Identifier.t
    | ELam of Identifier.t * t
    | ELamAnn of Identifier.t * Typ.t * t
    | EBinOp of t * binop * t
    | ENumLiteral of int
    | EAsc of Typ.t
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

(**
 * The following are also available in your code
 * (but their implementations are hidden):
 *
 *   parse : string -> Exp.t
 *   sprint : Exp.t -> string
 *)