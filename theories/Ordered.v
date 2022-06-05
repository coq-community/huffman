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

(** * Ordered lists and their properties

- Key definitions: [ordered]
- Initial author: Laurent.Thery@inria.fr (2003)

*)

From Coq Require Import Sorting.Permutation.
From Huffman Require Export AuxLib.

Set Default Proof Using "Type".

Section ordered.
Variable A : Type.
Variable order : A -> A -> Prop.
Hypothesis order_trans : forall a b c : A, order a b -> order b c -> order a c.

(** Ordered list with respect to an order *)
Inductive ordered : list A -> Prop :=
  | ordered_nil : ordered []
  | ordered_one : forall a : A, ordered (a :: [])
  | ordered_cons :
      forall (a b : A) (l : list A),
      order a b -> ordered (b :: l) -> ordered (a :: b :: l).
Local Hint Constructors ordered : core.

(** Inversion theorem *)
Theorem ordered_inv_order :
 forall (a b : A) (l : list A), ordered (a :: b :: l) -> order a b.
Proof.
intros a b l H; inversion H; auto.
Qed.

(** Inversion theorem *)
Theorem ordered_inv :
 forall (a : A) (l : list A), ordered (a :: l) -> ordered l.
Proof.
intros a l H; inversion H; auto.
Qed.

(** The second element of a list can be skipped *)
Theorem ordered_skip :
 forall (a b : A) (l : list A), ordered (a :: b :: l) -> ordered (a :: l).
Proof using order_trans.
intros a b l; case l; clear l; auto.
intros c l H; apply ordered_cons.
apply order_trans with (b := b); auto.
apply ordered_inv_order with (1 := H).
apply ordered_inv_order with (1 := ordered_inv _ _ H).
apply ordered_inv with (1 := ordered_inv _ _ H).
Qed.

(** All the element of the list are smaller than the first one *)
Theorem ordered_trans :
 forall (a b : A) (l : list A), ordered (a :: l) -> In b l -> order a b.
Proof using order_trans.
intros a b l; generalize a b; elim l; clear l a b.
intros a b H H2; inversion H2.
simpl in |- *; intros c l H a b H0 [H1| H1].
rewrite <- H1; apply ordered_inv_order with (1 := H0).
apply order_trans with (b := c); auto.
apply ordered_inv_order with (1 := H0).
apply H; auto.
apply ordered_inv with (1 := H0).
Qed.

(**
  In an ordered list split in two, elements of the first part
  are always smaller than the ones of the second part
*)
Theorem ordered_trans_app :
 forall (a b : A) (l1 l2 : list A),
 ordered (l1 ++ l2) -> In a l1 -> In b l2 -> order a b.
Proof using order_trans.
intros a b l1 l2; generalize a b; elim l1; simpl in |- *; clear l1 a b.
intros a b H H1; case H1.
intros c l H a b H0 [H1| H1] H2.
rewrite <- H1; apply ordered_trans with (1 := H0); auto with datatypes.
apply H; auto.
apply ordered_inv with (1 := H0); auto.
Qed.

(** If the order is antisymmetric, there is only one ordered list *)
Theorem ordered_perm_antisym_eq :
 (forall a b : A, order a b -> order b a -> a = b) ->
 forall l1 l2 : list A,
 Permutation l1 l2 -> ordered l1 -> ordered l2 -> l1 = l2.
Proof using order_trans.
intros antisym l1; elim l1; clear l1; simpl in |- *; auto.
intros l2 H1 H2 H3; apply sym_equal; apply Permutation_nil; auto.
intros a l1 Rec l2; case l2; simpl in |- *.
intros H; absurd (length (a :: l1) = length (A:=A) []).
simpl in |- *; red in |- *; intros; discriminate.
apply Permutation_length; auto.
intros a0 l H H0 H1.
cut (a = a0).
intros H3; apply f_equal2 with (f := cons (A:=A)); auto.
apply Rec; auto.
apply Permutation_cons_inv with (a := a); auto.
pattern a at 2 in |- *; rewrite H3; auto.
apply ordered_inv with (1 := H0); auto.
apply ordered_inv with (1 := H1); auto.
generalize (Permutation_in a H); simpl in |- *;
 (intros H2; case H2; auto; clear H2; intros H2).
generalize (Permutation_in a0 (Permutation_sym H)); simpl in |- *;
 (intros H3; case H3; auto; clear H3; intros H3).
apply antisym.
apply ordered_trans with (1 := H0); auto.
apply ordered_trans with (1 := H1); auto.
Qed.

End ordered.

#[export] Hint Constructors ordered : core.

Arguments ordered [A].

(** Ordered list are preserved by maps *)
Theorem ordered_map_inv :
 forall (A B : Type) (order : A -> A -> Prop) (g : B -> A) (l : list B),
 ordered (fun x y => order (g x) (g y)) l -> ordered order (map g l).
Proof.
intros A B order g l; elim l; simpl in |- *; auto.
intros a1 l1; case l1; simpl in |- *; auto.
intros b l0 H H0; inversion H0; auto.
Qed.
