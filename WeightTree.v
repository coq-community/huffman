(***********************************************************************)
(*    Proof of Huffman algorithm: WeightTree.v                         *)
(*                                                                     *)
(*                                                                     *)
(*                                    Laurent.Thery@inria.fr (2003)    *)
(***********************************************************************)

Require Export BTree.
Require Export Ordered.
Require Import ArithRing.
 
Section WeightTree.
Variable A : Set.
Variable f : A -> nat.

Fixpoint sum_leaves (t : btree A) : nat :=
  match t with
  | leaf n => f n
  | node t1 t2 => sum_leaves t1 + sum_leaves t2
  end.
 
Definition sum_order x y := sum_leaves x <= sum_leaves y.

Definition le_sum x y := le_bool (sum_leaves x) (sum_leaves y).
 
Theorem le_sum_correct1 :
 forall a b1 : btree A, le_sum a b1 = true -> sum_order a b1.
intros a b1; apply (le_bool_correct3 (sum_leaves a) (sum_leaves b1)).
Qed.
 
Theorem le_sum_correct2 :
 forall a b1 : btree A, le_sum a b1 = false -> sum_order b1 a.
intros a b1; apply (le_bool_correct4 (sum_leaves a) (sum_leaves b1)).
Qed.
 
Fixpoint weight_tree (t : btree A) : nat :=
  match t with
  | leaf n => 0
  | node t1 t2 =>
      sum_leaves t1 + weight_tree t1 + (sum_leaves t2 + weight_tree t2)
  end.
 
Definition weight_tree_list : list (btree A) -> nat :=
  fold_right (fun x : btree A => plus (weight_tree x)) 0.
 
Theorem weight_tree_list_node :
 forall (t1 t2 : btree A) (l : list (btree A)),
 weight_tree_list (node t1 t2 :: l) =
 sum_leaves t1 + sum_leaves t2 + weight_tree_list (t1 :: t2 :: l).
intros t1 t2 l; simpl in |- *; ring.
Qed.
 
Theorem weight_tree_list_permutation :
 forall l1 l2 : list (btree A),
 permutation l1 l2 -> weight_tree_list l1 = weight_tree_list l2.
intros l1 l2 H; elim H; auto.
simpl in |- *; auto; intros; ring.
simpl in |- *; auto; intros; ring.
intros l0 l3 l4 H0 H1 H2 H3; apply trans_equal with (1 := H1); auto.
Qed.
 
End WeightTree.

(* 
   Implicits
 *)

Implicit Arguments sum_leaves [A].
Implicit Arguments sum_order [A].
Implicit Arguments le_sum [A].
Implicit Arguments weight_tree [A].
Implicit Arguments weight_tree_list [A].


(* 
   sum_leaves are the same for ordered list that are permutations
   one from the other
 *)

Theorem ordered_sum_leaves_eq :
 forall (A : Set) (f : A -> nat) (l1 l2 : list (btree A)),
 permutation l1 l2 ->
 ordered (sum_order f) l1 ->
 ordered (sum_order f) l2 -> map (sum_leaves f) l1 = map (sum_leaves f) l2.
intros A f l1 l2 H H0 H1.
apply ordered_perm_antisym_eq with (order := le).
exact le_trans.
exact le_antisym.
apply permutation_map; auto.
apply ordered_map_inv; auto.
apply ordered_map_inv; auto.
Qed.
