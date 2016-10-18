(**
  @summary: This module defines sorting stability on the integers.
  @author: A Manning
**)
module GenericStability
open FStar.List.Tot
open FStar.ListProperties
open GenericSort
(*
  This module is heavily inspired by Leino and Lucio's 2012 paper,
  'An Assertional Proof of the Stability and Correctness of Natural Mergesort'.
  http://research.microsoft.com/en-us/um/people/leino/papers/krml241.pdf
*)

type stable (#a:eqtype) (l1:list a) (l2:list a{permutation l1 l2}) (key:(a -> Tot int)) =
  forall x y. ((appears_before x y l1 /\ key y = key x) ==> appears_before x y l2)

(**
  filterEq returns the elements of a list that have the same key as n.
**)
val filter_eq: #a:Type -> (k:int) -> key:(a -> Tot int) -> (xs: list a) -> Tot (list a)
let rec filter_eq #a k key xs =
  match xs with
  | [] -> []
  | hd::tl
    -> if key hd = k then
        hd::(filter_eq k key tl)
      else filter_eq k key tl

val filter_eq_contains: #a:eqtype -> (k:int) -> key:(a -> Tot int) -> (xs: list a) ->
  Lemma(ensures(forall x. (mem x xs /\ key x = k) <==> mem x (filter_eq k key xs)))
let rec filter_eq_contains #a k key xs =
  match xs with
  | [] -> ()
  | hd::tl ->
    if key hd = k then
      filter_eq_contains k key tl
    else filter_eq_contains k key tl

(*)
val filter_eq_ordered: #a:eqtype -> key:(a -> Tot int) -> (xs: list a) ->
  Lemma(ensures(forall x. ( (Cons.hd xs <> x)  /\ mem x (Cons.tl xs) /\ key (Cons.hd xs) = key x) ==>
  (Cons.hd xs = Cons.hd (filter_eq (key x) key xs) /\ mem x (Cons.tl (filter_eq (key x) key xs)))))
let filter_eq_ordered #a (key) xs = ()
