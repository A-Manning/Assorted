module MergeSort
open FStar.List.Tot
open GenericSort
open GenericStability

val merge: #a:eqtype
  -> l_0:list a{is_Cons l_0}
  -> l_1:list a{is_Cons l_1}
  -> key:(a -> Tot int){sorted l_0 key /\ sorted l_1 key}
  -> l':list a{sorted l' key /\ permutation_2 l' l_0 l_1}

let rec merge #a l_0 l_1 key =
  let h_0 = hd l_0 in
  let h_1 = hd l_1 in
  if ((key h_0) <= (key h_1)) then
    if tl l_0 = [] then (h_0::l_1)
    else
    (cons_sorted h_0 (merge (tl l_0) l_1 key) key;
    h_0::(merge (tl l_0) l_1 key))
  else if tl l_1 = [] then (h_1::l_0)
    else
    cons_sorted h_1 (merge l_0 (tl l_1) key) key;
    h_1::(merge l_0 (tl l_1) key)
(*)
  match ((key h_0) <= (key h_1)) with
  | true ->
    cons_sorted h_0 (merge (tl l_0) l_1 key) key;
    h_0::(merge (tl l_0) l_1 key)
  | false ->
      cons_sorted h_1 (merge l_0 (tl l_1) key) key;
      h_1::(merge l_0 (tl l_1) key)

(*)
val ms: #a:eqtype -> l_0:list a -> key:(a -> Tot int) -> l':list a
let ms #a l_0 key =
  match l_0 with
  | [] | [_] -> l_0
  | [a_0;a_1] -> (if key a_0 <= key a_1 then [a_0;a_1] else [a_1;a_0])
  | [a_0;a_1;a_2] -> []

























(*)
type split_inv (#a:eqtype) (l:list a) (l1:list a) (l2:list a) (key:(a -> Tot int)) =
    permutation_2 l l1 l2 /\
    (* needed for decreases clause in mergesort function *)
    length l > length l1 /\ length l > length l2
    /\ (forall x y.
    (appears_before x y l ==>
    appears_before x y l1
    \/ appears_before x y l2
    \/ ~(mem x l1 /\ mem y l1 )))


val split: (#a:eqtype) -> l:list a -> Tot r:(list a * list a)
  (requires (is_Cons l /\ is_Cons (Cons.tl l)))
	(ensures (split_inv l (fst r) (snd r)))
let rec split (x::y::l) =
  match l with
    | [] -> [x], [y]
    | [x'] -> x::y, [x']
    | _ -> let l1, l2 = split l in
           x::l1, y::l2
(*)
(* Verification succeeds even without this invariant;
   it just takes a lot longer (22s vs 7s) *)
type merge_inv (l1:list int) (l2:list int) (l:list int) =
    (is_Cons l1 /\ is_Cons l /\ Cons.hd l1 = Cons.hd l) \/
    (is_Cons l2 /\ is_Cons l /\ Cons.hd l2 = Cons.hd l) \/
    (is_Nil l1 /\ is_Nil l2 /\ is_Nil l)

val merge: l1:list int -> l2:list int -> Pure (list int)
             (requires (sorted l1 /\ sorted l2))
             (ensures (fun l -> sorted l /\ permutation_2 l l1 l2
                                         /\ merge_inv l1 l2 l
                                         /\ (forall x y. ((appears_before x y l1 ==>
                                          appears_before x y l)
                                          /\(appears_before x y l2 ==>
                                          appears_before x y l)))))
let rec merge l1 l2 = match (l1, l2) with
  | [], _ -> l2
  | _, [] -> l1
  | h1::tl1, h2::tl2 -> if h1 <= h2
                        then h1::(merge tl1 l2)
                        else h2::(merge l1 tl2)
(*)
val mergesort: l:list int -> Pure (list int) (requires True)
      (ensures (fun r -> sorted r /\ permutation l r)) (decreases (length l))
let rec mergesort l = match l with
  | [] -> []
  | [x] -> [x]
  | _ ->
    let (l1, l2) = split l in
    let sl1 = mergesort l1 in
    let sl2 = mergesort l2 in
    merge sl1 sl2
