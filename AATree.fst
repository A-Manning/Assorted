module AATree
(**https://en.wikipedia.org/wiki/AA_tree**)


type tree' =
  | E
  | T: (l:tree') -> (k:int) -> (lvl:nat) -> (r:tree') -> tree'

(**
  The first invariant:
    The level of a leaf node is 1.
  The fifth invariant:
    A node of level > 1 has 2 children.
**)
val level: tree' -> Tot nat
let level t =
  match t with
  | E -> 1
  | T _ _ lvl _ -> lvl
(**
  The second invariant:
    The level of a left child is 1 less than it's parent.
**)
val l_level_inv: tree' -> Tot bool
let rec l_level_inv t =
  match t with
  | E -> true
  | T l _ lvl r ->
    l_level_inv l && l_level_inv r && level l = lvl - 1

(**
  The third invariant:
    The level of a right child is equal to or 1 less than it's parent.
**)
val r_level_inv: tree' -> Tot bool
let rec r_level_inv t =
  match t with
  | E -> true
  | T l _ lvl r ->
    r_level_inv l &&
    r_level_inv r &&
    (lvl = level r + 1 || lvl = level r)
(*)
(**
  The fourth invariant:
    The level of a right grandchild is less than it's grandparent.
**)
val r_level_inv2: tree' -> Tot bool
let rec r_level_inv2 t =
  match t with
  | E -> true
  | T l _ r ->
    match r with
    | E -> true
    | T r_l _ r_r ->
      r_level_inv2 l &&
      r_level_inv2 r &&
      level r_l < level t &&
      level r_r < level t

(** Checks if a tree is a binary search tree **)
val is_bst : tree' -> Tot bool
let rec is_bst t =
  match t with
  | E -> true
  | T t_l t_k t_r ->
    match (t_l,t_r) with
    | E,E -> true
    | E, T _ r_k _ -> is_bst t_r && t_k < r_k
    | T _ l_k _, E -> is_bst t_l && l_k <= t_k
    | T _ l_k _, T _ r_k _ ->
      is_bst t_l && is_bst t_r && l_k <= t_k && t_k < r_k

val contains: int -> t:tree'{is_bst t} -> Tot bool
let rec contains x t =
  match t with
  | E -> false
  | T t_l t_k t_r ->
    if t_k = x then true
    else if x <= t_k then contains x t_l
    else contains x t_r

(**
  Checks if a tree has a left branch.
**)
val has_left: t:tree' -> Tot bool
let has_left t =
  match t with
  | E | T E _ _ -> false
  | _ -> true

(**
  Checks if a tree has a right branch.
**)
val has_right: t:tree' -> Tot bool
let has_right t =
  match t with
  | E | T _ _ E -> false
  | _ -> true

(** The skew function **)
val skew: t:tree'{has_left t} -> Tot tree'
let skew t =
  match t with
  | T t_l t_k t_r ->
    match t_l with
    | T l_l l_k l_r ->
      T (l_l) l_k (T l_r t_k t_r)

val skew_bst: t:tree'{has_left t /\ is_bst t} ->
  Lemma(ensures (is_bst (skew t)))
let skew_bst t =
  match t with
  | T t_l t_k t_r ->
    match t_l with
    | T l_l l_k l_r ->
      assert (is_bst l_l);
      assert(is_bst l_r);
      assert(is_bst t_r);
      assert(l_k <= t_k);
      admit()

(** The split function **)
val split: t:tree'{has_right t} -> Tot tree'
let split t =
  match t with
  | T t_l t_k t_r ->
  match t_r with
    | T r_l r_k r_r ->
      T (T t_l t_k r_l) r_k r_r
