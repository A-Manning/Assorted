module NaturalMergeSort
(*
  Proves the sortedness and correctness of Natural Merge Sort.
  Follows the general form of
  http://research.microsoft.com/en-us/um/people/leino/papers/krml241.pdf
*)
open FStar.List.Tot

// Assigns a key to an element of a list.
// Left undefined intentionally, as the function is general
assume val assignKey: (i:int) -> Tot int


// gt and eq define greater than and equality

val gt: (x:int) -> (y:int) -> Tot bool
let gt x y = (assignKey x > assignKey y)
val eq: (x:int) -> (y:int) -> Tot bool
let eq x y = (assignKey x = assignKey y)


//1.1 Sortedness
val sorted: list int -> Tot bool
let rec sorted l = match l with
    | [] | [_] -> true
    | x::y::xs -> (assignKey x <= assignKey y) && (sorted (y::xs))

val test_sorted: x:int -> l:list int ->
      Lemma ((sorted (x::l) /\ is_Cons l) ==> assignKey x <= assignKey (Cons.hd l))
let test_sorted x l = ()

val test_sorted2: unit -> Tot (m:list int{sorted m})
let test_sorted2 () = Nil

//1.2 Stability
val filterEQ: (e:int) -> (xs:list int) -> Tot (list int)
let rec filterEQ e xs =
  match xs with
  | [] -> []
  | hd::tl ->
    if assignKey e = assignKey hd then
      hd::(filterEQ e tl)
    else filterEQ e tl

// the stable predicate will be proven later on

val naturalMergeSort: (xs:list int) -> xxs:
