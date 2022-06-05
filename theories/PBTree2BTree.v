(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU Lesser General Public License for more details.                *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)

(** * Translation from partial trees to binary trees

- Key definitions: [to_btree]
- Initial author: Laurent.Thery@inria.fr (2003)

*)

From Coq Require Export Compare_dec.
From Huffman Require Export AuxLib Code Build ISort.
From Huffman Require Export UniqueKey PBTree BTree.

Set Default Proof Using "Type".

Section PBTREE2BTREE.
Variable A : Type.
Variable A_eq_dec : forall a b : A, {a = b} + {a <> b}.
Variable empty : A.

(** Turn a partial tree into a binary tree *)
Fixpoint to_btree (a : pbtree A) : btree A :=
  match a with
  | pbleaf b => leaf b
  | pbleft l1 => to_btree l1
  | pbright l1 => to_btree l1
  | pbnode l1 l2 => node (to_btree l1) (to_btree l2)
  end.

(** Computing the binary tree preserves the leaves*)
Theorem to_btree_inb :
 forall a b, inpb (pbleaf a) b -> inb (leaf a) (to_btree b).
Proof.
intros a b; generalize a; elim b; clear a b; simpl in |- *; auto.
intros a a0 H; inversion H; auto.
intros p H a H0; apply H; auto; inversion H0; auto.
intros p H a H0; apply H; auto; inversion H0; auto.
intros p H p0 H0 a H1; inversion H1; auto.
Qed.

(** Leaves do not change *)
Theorem to_btree_inpb :
 forall a b, inb (leaf a) (to_btree b) -> inpb (pbleaf a) b.
Proof.
intros a b; generalize a; elim b; clear a b; simpl in |- *; auto.
intros a a0 H; inversion H; auto.
intros p H p0 H0 a H1.
inversion H1; auto.
Qed.

(** The list of all leaves does not change *)
Theorem to_btree_all_leaves :
 forall t, all_leaves (to_btree t) = all_pbleaves t.
Proof.
intros t; elim t; simpl in |- *; auto.
intros p H p0 H0; apply f_equal2 with (f := app (A:=A)); auto.
Qed.

(** Computing the btree preserves the property of having distinct leaves *)
Theorem to_btree_distinct_leaves :
 forall a : pbtree A, distinct_pbleaves a -> distinct_leaves (to_btree a).
Proof.
intros a H.
apply all_leaves_unique.
rewrite to_btree_all_leaves.
apply all_pbleaves_NoDup; auto.
Qed.

(** The transformation perserves distinct leaves *)
Theorem to_btree_distinct_pbleaves :
 forall a : pbtree A, distinct_leaves (to_btree a) -> distinct_pbleaves a.
Proof.
intros a H.
apply all_pbleaves_unique.
rewrite <- to_btree_all_leaves.
apply all_leaves_NoDup; auto.
Qed.

(** For each key, the resulting code of the computed tree is always smaller *)
Theorem to_btree_smaller :
 forall t a,
 length (find_code A_eq_dec a (compute_code (to_btree t))) <=
 length (find_code A_eq_dec a (compute_pbcode t)).
Proof.
intros t; elim t; simpl in |- *; auto.
intros p H a.
apply Nat.le_trans with (1 := H a); auto.
case (inpb_dec A_eq_dec (pbleaf a) p); intros H1.
case inpb_compute_ex with (1 := H1).
intros x Hx; rewrite in_find_map with (l := x); simpl in |- *; auto.
rewrite not_in_find_map; simpl in |- *; auto.
rewrite not_in_find_code; simpl in |- *; auto.
intros p1; contradict H1; auto.
apply in_pbcompute_inpb with (1 := H1).
intros p1; contradict H1; auto.
apply in_pbcompute_inpb with (1 := H1).
intros p H a.
apply Nat.le_trans with (1 := H a); auto.
case (inpb_dec A_eq_dec (pbleaf a) p); intros H1.
case inpb_compute_ex with (1 := H1).
intros x Hx; rewrite in_find_map with (l := x); simpl in |- *; auto.
rewrite not_in_find_map; simpl in |- *; auto.
rewrite not_in_find_code; simpl in |- *; auto.
intros p1; contradict H1; auto.
apply in_pbcompute_inpb with (1 := H1).
intros p1; contradict H1; auto.
apply in_pbcompute_inpb with (1 := H1).
intros p H p0 H0 a.
simpl in |- *; repeat rewrite find_code_app; auto.
case (inpb_dec A_eq_dec (pbleaf a) p); intros H1.
case inpb_compute_ex with (1 := H1).
intros x Hx; repeat rewrite in_find_map with (1 := Hx); simpl in |- *;
 auto with arith.
case inb_compute_ex with (a := a) (p := to_btree p); auto.
apply to_btree_inb; auto.
intros x1 Hx1; repeat rewrite in_find_map with (1 := Hx1); simpl in |- *;
 auto with arith.
rewrite not_in_find_map with (p := compute_code (to_btree p)); simpl in |- *;
 auto with arith.
rewrite not_in_find_map with (p := compute_pbcode p); simpl in |- *;
 auto with arith.
case (inpb_dec A_eq_dec (pbleaf a) p0); intros H2.
case inpb_compute_ex with (1 := H2).
intros x Hx; repeat rewrite in_find_map with (1 := Hx); simpl in |- *;
 auto with arith.
case inb_compute_ex with (a := a) (p := to_btree p0); auto.
apply to_btree_inb; auto.
intros x1 Hx1; repeat rewrite in_find_map with (1 := Hx1); simpl in |- *;
 auto with arith.
rewrite not_in_find_map with (p := compute_pbcode p0); simpl in |- *;
 auto with arith.
rewrite not_in_find_map with (p := compute_code (to_btree p0)); simpl in |- *;
 auto with arith.
intros l; contradict H2; apply to_btree_inpb;
 apply inCompute_inb with (1 := H2); auto.
intros l; contradict H2; apply in_pbcompute_inpb with (1 := H2).
intros l; contradict H1; apply in_pbcompute_inpb with (1 := H1).
intros l; contradict H1; apply to_btree_inpb;
 apply inCompute_inb with (1 := H1); auto.
Qed.

End PBTREE2BTREE.

Arguments to_btree [A].
