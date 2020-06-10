exception NotImplemented

exception Impossible
module Identifier = struct
  type t = string
end

module Typ = struct
  type hole_id = int
  type t =
    | THole of hole_id
    | TNum
    | TArrow of t * t

  let type_variable = ref (0)

  (* generates a new unique type variable *)
  let gen_new_type_var () =
      let var = !type_variable in
      incr type_variable; var
    ;;
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

(* TBD: build map for fresh var? *)
let get_match_arrow_typ (t: Typ.t): Typ.t option * Constraints.t = 
  match t with
  | Thole _ -> (
    let var_in = gen_new_type_var() in 
    let var_out = gen_new_type_var() in
    let arrow_typ = TArrow (THole(var_in),THole(var_out)) in
    (Some arrow_typ,[(t,arrow_typ)])
    )
  | TArrow (_,_) -> (Some t, [])
  | _ -> (None, [])

let rec syn (ctx: Ctx.t) (e: Exp.t): Typ.t option * Constraints.t =
  match e with
  | EVar x -> (Ctx.lookup ctx x, [])
  | ELam (_, _) -> (None,[]) (* TBD *)
  | ELamAnn (x, ty1, e2) -> (
      match syn (Ctx.extend ctx (x, ty1)) e2 with
      | (None, _)-> (None, []) (* TBD *)
      | (Some ty2, cons) -> (Some (TArrow (ty1, ty2)),cons) )
  | EBinOp (e1, OpPlus, e2) -> (
      match (ana ctx e1 Typ.TNum, ana ctx e2 Typ.TNum) with
      | ((false,_), _) 
      | (_, (false,_)) -> (None,[]) (* TBD *)
      | ((true,cons1), (true,cons2)) -> (Some TNum, cons1@cons2) )
  | EBinOp (e1, OpAp, e2) -> (
      match (syn ctx e1) with
      | (None, _)-> (None, []) (* TBD *)
      | (Some(typ_e1), cons1) -> (
          match get_match_arrow_typ typ_e1 with
          | (None, _) -> (None, []) (* TBD *)
          | (Some(TArrow (ty_in, ty_out)), cons2) -> (
            match ana ctx e2 ty_in with
            | (false, _) -> (None, []) (* TBD *)
            | (true, cons3) -> (Some ty_out, cons1@cons2@cons3)
          )
          | _ -> raise Impossible
        )
    )
  | ENumLiteral _ -> (Some TNum, cons)
  | EAsc (exp, typ) -> (
      match ana ctx exp typ with
      | (false, _) -> (None, []) (* TBD *)
      | (true, cons) -> (Some typ, cons)
  )
  | EEmptyHole _ -> (Some THole(gen_new_type_var()),[])
  | EExpHole (_, e2) -> (
    match syn ctx e2 with
    | (None, _)-> (None, []) (* TBD *)
    | (Some _, cons) -> (Some THole(gen_new_type_var()),cons)
  )
and ana (ctx: Ctx.t) (e: Exp.t) (ty: Typ.t): bool =
  match e with
  | ELam (x, exp) -> (
    match get_match_arrow_typ ty with
    | (None, _) -> (None, []) (* TBD *)
    | (Some(TArrow (ty_in, ty_out)), cons1) -> (
      match ana (Ctx.extend ctx (x, ty_in)) exp ty_out with
      | (false, _) -> (false, []) (* TBD *)
      | (true, cons2) -> (true, cons1@cons2)
    )
  ) 
  | ELamAnn (x, ty_in', exp) -> (
    match get_match_arrow_typ ty with
    | (None, _) -> (None, []) (* TBD *)
    | (Some(TArrow (ty_in, ty_out)), cons1) -> (
      match ana (Ctx.extend ctx (x, ty_in')) exp ty_out with
      | (false, _) -> (false, []) (* TBD *)
      | (true, cons2) -> (true, cons1@cons2@[(ty_in,ty_in')])
    )
  ) 
  | EVar _
  | EBinOp _ 
  | ENumLiteral _
  | EAsc _
  | EEmptyHole _
  | EExpHole _ ->
    (* subsumption *)
      (match syn ctx e with
        | (None, _) -> (None, []) (* TBD *)
        | (Some ty', cons) -> (true, cons@[(ty,ty')])
      )