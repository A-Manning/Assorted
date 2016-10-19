(**
  @summary: This module defines properties of sortedness on a generic list.
  @author: A Manning
**)
module GenericSort
open FStar.List.Tot
open FStar.ListProperties

(**
  key is a function that will appear a lot here,
  as will 'a, a, #a, which are generic types.
  key is a function on 'a that returns an integer.
  #a and a appears where a is required to support equality.
**)

(**
  Checks that a list is sorted.
**)

val sorted: list 'a -> key:('a -> Tot int) -> Tot bool
let rec sorted l key = match l with
    | [] | [_] -> true
    | x::y::xs -> (key x <= key y) && (sorted (y::xs) key)

val test_sorted: x:'a -> l:list 'a -> key:('a -> Tot int) ->
      Lemma ((sorted (x::l) key /\ is_Cons l) ==> key x <= key (Cons.hd l))
let test_sorted x l key = ()

val test_sorted2: unit -> key:('a -> Tot int) -> Tot (m:list 'a{sorted m key})
let test_sorted2 () key = Nil

(**
  Lemmata about sorted.
**)
val sorted_smaller: #a:eqtype
                ->  x:a
                ->  y:a
                ->  l:list a
                ->  key:(a -> Tot int)
                ->  Lemma (requires (sorted (x::l) key /\ mem y l))
                          (ensures (key x <= key y))
                          [SMTPat (sorted (x::l) key); SMTPat (mem y l)]
let rec sorted_smaller #a x y l key = match l with
    | [] -> ()
    | z::zs -> if key z = key y then () else sorted_smaller x y zs key

val cons_sorted: #a:eqtype -> x:a -> l:list a{is_Cons l} -> key:(a -> Tot int)
  -> Lemma(requires sorted l key /\ key x <= key (hd l))
          (ensures sorted (x::l) key)
let cons_sorted #a x l key = ()

type permutation (#a:Type{hasEq a}) (l1:list a) (l2:list a) =
    length l1 = length l2 /\ (forall n. mem n l1 = mem n l2)

type permutation_2 (#a:Type{hasEq a}) (l:list a) (l1:list a) (l2:list a) =
    (forall n. mem n l = (mem n l1 || mem n l2)) /\
    length l = length l1 + length l2
