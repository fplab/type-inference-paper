(* https://www.lri.fr/~filliatr/ftp/publis/puf-wml07.pdf *)
module UnionFind = struct
  type t = { parent : int array; rank : int array; size: int}
  let create n =
    { parent = Array.init n (fun i -> i);
    rank = Array.make n 0;
    size = n; }
  ;;
  let create_from start size =
    { parent = Array.init size (fun i -> i+start);
    rank = Array.make size 0;
    size = size; }
  ;;
(*   let extend_to uf n =
    { parent = Array.append uf.parent (Array.init (n - uf.size) (fun i -> i+ uf.size));
    rank = Array.make n 0;
    size = n; } *)

  let rec find uf i =
    let pi = uf.parent.(i) in
    if pi == i then
    i
    else begin
    let ci = find uf pi in
    uf.parent.(i) <- ci; (* path compression *)
    ci
    end
  
  
  let get_group uf i = 
    let rec _get_group uf pi index: (int list) =
      if (index<uf.size) then (
        if uf.parent.(index) == pi then (
        [index] @ (_get_group uf pi (index+1)))
        else (_get_group uf pi (index+1))
      ) else [] 
    in let pi = find uf i in _get_group uf pi 0;;

  let rec reset_parent uf group pi = 
    match group with
    | [] -> ()
    | hd::tl -> uf.parent.(hd) <- pi; reset_parent uf tl pi;;

  let elt_in_group uf pi = 
    let rec _elt_in_group uf pi index =
      if (index<uf.size) then (
        if (uf.parent.(index) == pi) && index!=pi then index
        else (_elt_in_group uf pi (index+1))
      ) else pi
    in _elt_in_group uf pi 0;;

  let disconnect uf i =
    let pi = find uf i in
    reset_parent uf (get_group uf i) (elt_in_group uf pi);
    uf.parent.(i) <- i;;
      
  let union ({ parent = p; rank = r; size= _} as uf) x y =
    let cx = find uf x in
    let cy = find uf y in
    if cx != cy then begin
      if r.(cx) > r.(cy) then
      p.(cy) <- cx
      else if r.(cx) < r.(cy) then
      p.(cx) <- cy
      else begin
      r.(cx) <- r.(cx) + 1;
      p.(cy) <- cx
      end
    end

end;;