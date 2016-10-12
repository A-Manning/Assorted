(**
  @summary: This module defines sorting stability on the integers.
  @author: A Manning
**)
module IntStable
open FStar.List.Tot
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
  Several functions and lemmas are needed from FStar.List and FStar.ListProperties
  These do not load correctly in my binary....
**)

val append_nil_l: l:list int ->
  Lemma (requires True)
        (ensures ([]@l = l))[SMTPat ([]@l)]
let append_nil_l l = ()

val append_l_nil: l:list int ->
  Lemma (requires True)
        (ensures (l@[] = l)) [SMTPat (append l [])]
let rec append_l_nil = function
  | [] -> ()
  | hd::tl -> append_l_nil tl

val append_assoc: l1:list int -> l2:list int -> l3:list int ->
  Lemma (requires True)
        (ensures ((l1@(l2@l3)) = ((l1@l2)@l3))) [SMTPat (append l1 (append l2 l3))]
let rec append_assoc l1 l2 l3 = match l1 with
    | [] -> ()
    | hd::tl -> append_assoc tl l2 l3

(* Renamed to avoid conflict *)
val rev_acc2: list int -> list int -> Tot (list int)
let rec rev_acc2 l acc = match l with
    | [] -> acc
    | hd::tl -> rev_acc2 tl (hd::acc)

val reverseCons: (xs: list int) -> (r: list int) -> (x:int) ->
  Lemma(requires (xs = rev_acc2 r []))
    (ensures (append xs (Cons x []) = rev_acc2 (Cons x r) []))
let reverseCons xs r x =
  assert(forall a b c. append (rev_acc2 a b) c = rev_acc2 a (append b c))

val flatten: list (list int) -> Tot (list int)
let rec flatten l = match l with
    | [] -> []
    | hd::tl -> append hd (flatten tl)

(**
  As defined in 'An Assertional Proof...'
**)
val flatten_cons_append:
  (xs: list int)
  -> (ys: list int)
  -> (zzs: list (list int))
  -> Lemma(ensures
    (flatten (Cons (append xs ys) zzs) = append xs (append ys (flatten zzs))))
let flatten_cons_append xs ys zzs = ()


(**
  Ensures that filtering is distinct with regards to append
**)
val distFilterApp: (x: int) -> (xs: list int) -> (ys: list int) ->
  Lemma
  (ensures (filterEq x (append xs ys) = append (filterEq x xs) (filterEq x ys)))
let distFilterApp x xs ys = ()
