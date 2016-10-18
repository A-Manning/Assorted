(**
  @summary: This module defines sorting stability on the integers.
  @author: A Manning
**)
module IntStable
open FStar.List.Tot
open FStar.ListProperties
open IntSort
(*
  This module is heavily inspired by Leino and Lucio's 2012 paper,
  'An Assertional Proof of the Stability and Correctness of Natural Mergesort'.
  http://research.microsoft.com/en-us/um/people/leino/papers/krml241.pdf
*)

val appears_before: before:int -> after:int -> ls: list int -> Tot bool
let rec appears_before b4 aft ls =
  match ls with
  | _ | [_] -> false
  | hd::tl ->
    if hd = b4 then mem aft tl
    else appears_before b4 aft tl

type stable (l1:list int) (l2:list int{permutation l1 l2}) =
  forall x y. ((appears_before x y l1 /\ x = y) ==> appears_before x y l2)

(**
  filterEq returns the elements of a list that have the same key as n.
**)
val filter_eq: (n: int) -> (xs: list int) -> Tot (list int)
let rec filter_eq n xs =
  match xs with
  | [] -> []
  | hd::tl
    -> if n = hd then
        Cons hd (filter_eq n tl)
      else filter_eq n tl

(**
  Ensures that filtering is distinct with regards to append.
**)
val dist_filter_app: (x: int) -> (xs: list int) -> (ys: list int) ->
  Lemma
  (ensures (filter_eq x (append xs ys) = append (filter_eq x xs) (filter_eq x ys)))
let rec dist_filter_app x xs ys =
  match xs with
  | [] | [_] -> (match ys with
    | [] | [_] -> ()
    | a::b::cs -> dist_filter_app x xs (Cons b cs))
  | a::b::cs -> dist_filter_app x (Cons b cs) ys

(**
  Ensures that if a key does not appear in a list, then filtering for it returns [].
**)
val null_filter: (x:int) -> (ys: list int) ->
  Lemma
  (requires not (mem x ys))
  (ensures filter_eq x ys = [])
let rec null_filter x ys =
  match ys with
  | [] | [_] -> ()
  | a::b::cs -> null_filter x (Cons b cs)

(*
val stable_lifting: (x:int)
  -> (ws:list int{is_Cons ws})
  -> (zs:list int{sorted zs /\ is_Cons zs})
  -> Lemma (requires Cons.hd ws < Cons.hd zs /\ x = Cons.hd ws)
  (ensures (stable (zs@ws) ((Cons (Cons.hd ws) zs)@(Cons.tl ws))))
let stable_lifting x ws zs =
  dist_filter_app x zs ws;
  //assert(filter_eq x (zs@ws) = (filter_eq x zs)@(filter_eq x ws));
  //assert((filter_eq x zs)@((filter_eq x (Cons (Cons.hd ws) [])@(filter_eq x (Cons.tl ws)))) = filter_eq x (zs@ws));
  append_assoc (filter_eq x zs) (filter_eq x (Cons (Cons.hd ws) [])) (filter_eq x (Cons.tl ws));
  //assert((((filter_eq x zs)@(filter_eq x (Cons (Cons.hd ws) [])))@(filter_eq x (Cons.tl ws))) = filter_eq x (zs@ws));
  if (x = Cons.hd ws) then (
    null_filter x zs;
    append_nil_l (Cons (Cons.hd ws) []);
    append_l_nil (Cons (Cons.hd ws) []);
    dist_filter_app x (Cons (Cons.hd ws) []) (Cons.tl ws))
    //assert((filter_eq x (zs@ws)) = (filter_eq x ((Cons (Cons.hd ws) zs))@(Cons.tl ws)));
    //assert((filter_eq x (zs@ws)) = (filter_eq x (Cons (Cons.hd ws) (zs@(Cons.tl ws))))))

  else (append_l_nil (filter_eq x zs);
    assert(filter_eq x (Cons (Cons.hd ws) []) = []);
    append_nil_l zs;
    append_l_nil zs;
    dist_filter_app x zs (Cons.tl ws))
    //assert((filter_eq x (zs@ws)) = (filter_eq x ((Cons (Cons.hd ws) zs))@(Cons.tl ws)));
    //assert((filter_eq x (zs@ws)) <> (filter_eq x (Cons (Cons.hd ws) (zs@(Cons.tl ws))))))
*)
