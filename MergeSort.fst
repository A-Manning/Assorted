(**This module implements a generic merge sort and proves it's stability.**)
module MergeSort
(**@author A Manning**)

open FStar.List.Tot
open GenericSort
open GenericStability

(** The key function k will appear frequently here.**)

(**First define the merge function without any properties.**)
val merge': #a:eqtype -> (l1:list a) -> (l2:list a) -> k:(a -> Tot int) -> Tot (list a)
let rec merge' #a l1 l2 k = match (l1, l2) with
  | [], _ -> l2
  | _, [] -> l1
  | h1::tl1, h2::tl2 -> if k h1 <= k h2
                        then h1::(merge' tl1 l2 k)
                        else h2::(merge' l1 tl2 k)


val merge'_permutation: #a:eqtype ->
  (l1:list a) ->
  (l2:list a) ->
  k:(a -> Tot int) ->
  Lemma(ensures permutation_2 (merge' l1 l2 k) l1 l2)

let rec merge'_permutation #a l1 l2 k = match (l1, l2) with
  | [], _ -> ()
  | _, [] -> ()
  | h1::tl1, h2::tl2 -> if k h1 <= k h2
                          then (merge'_permutation tl1 l2 k)
                        else (merge'_permutation l1 tl2 k)

val merge'_sorted: #a:eqtype ->
  (l1:list a) ->
  (l2:list a) ->
  k:(a -> Tot int) ->
  Lemma(requires (sorted l1 k /\ sorted l2 k))
    (ensures sorted (merge' l1 l2 k) k)
let rec merge'_sorted #a l1 l2 k = merge'_permutation l1 l2 k;
match (l1, l2) with
  | [], _ -> ()
  | _, [] -> ()
  | h1::tl1, h2::tl2 -> if k h1 <= k h2
                          then (merge'_sorted tl1 l2 k)
                        else (merge'_sorted l1 tl2 k)

let merge = merge'

val mergesort: #a:eqtype -> l0:list a -> k:(a -> Tot int) -> Tot (list a)
let rec mergesort #a l0 k =
  match l0 with
  | [] | [_] -> l0
  | a::b::tl -> if k a <= k b then merge (a::[b]) (mergesort tl k) k
                else merge (b::[a]) (mergesort tl k) k
