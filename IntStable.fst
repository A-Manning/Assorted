(**
  @summary: This module defines sorting stability on the integers.
  @author: A Manning
**)
module IntStable
open FStar.List.Tot
open FStar.ListProperties
(*
  This module is heavily inspired by Leino and Lucio's 2012 paper,
  'An Assertional Proof of the Stability and Correctness of Natural Mergesort'.
  http://research.microsoft.com/en-us/um/people/leino/papers/krml241.pdf
*)

(**
  filterEq returns the elements of a list that have the same key as n.
**)
val filterEq: (n: int) -> (xs: list int) -> Tot (list int)
let rec filterEq n xs =
  match xs with
  | [] -> []
  | hd::tl
    -> if n = hd then
        Cons hd (filterEq n tl)
      else filterEq n tl

(**
  The stability predicate
**)
type stable (xs: list int) (ys:list int) = forall x. filterEq x xs = filterEq x ys

(**
  Ensures that filtering is distinct with regards to append
**)
val distFilterApp: (x: int) -> (xs: list int) -> (ys: list int) ->
  Lemma
  (ensures (filterEq x (append xs ys) = append (filterEq x xs) (filterEq x ys)))
let rec distFilterApp x xs ys =
  match xs with
  | [] | [_] -> (match ys with
    | [] | [_] -> ()
    | a::b::cs -> distFilterApp x xs (Cons b cs))
  | a::b::cs -> distFilterApp x (Cons b cs) ys

val nullFilter: (x:int) -> (ys: list int) ->
  Lemma
  (requires not (mem x ys))
  (ensures filterEq x ys = [])
let rec nullFilter x ys =
  match ys with
  | [] | [_] -> ()
  | a::b::cs -> nullFilter x (Cons b cs)
