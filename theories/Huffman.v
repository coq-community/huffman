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

(** * The Huffman algorithm and its correctness

- Key definitions: [huffman]
- Initial author: Laurent.Thery@inria.fr (2003)

*)

From Coq Require Import Sorting.Permutation.
From Huffman Require Import Code BTree Build PBTree2BTree Restrict.

Set Default Proof Using "Type".

Section Huffman.
Variable A : Type.
Variable empty : A.
Variable A_eq_dec : forall a b : A, {a = b} + {a <> b}.
Variable m : list A.
Hypothesis frequency_more_than_one : 1 < length (frequency_list A_eq_dec m).

#[local] Hint Constructors Permutation : core.
#[local] Hint Resolve Permutation_refl : core.
#[local] Hint Resolve Permutation_app : core.
#[local] Hint Resolve Permutation_app_swap : core.

(** The message is not null *) 
Theorem not_null_m : m <> [].
Proof using frequency_more_than_one.
generalize frequency_more_than_one; case m; simpl in |- *; auto.
intros H; contradict H; auto with arith.
intros; discriminate.
Qed.

(** Every tree that is built is of minimum weight *)
Theorem huffman_build_minimum :
 forall (c : code A) (t : btree A),
 unique_prefix c ->
 in_alphabet m c ->
 build (fun x => number_of_occurrences A_eq_dec x m)
   (map (fun x => leaf (fst x)) (frequency_list A_eq_dec m)) t ->
 weight A_eq_dec m (compute_code t) <= weight A_eq_dec m c.
Proof using empty frequency_more_than_one.
intros c t H1 H2 H3; unfold weight in |- *.
rewrite restrict_code_encode_length with (c := c).
apply
 Nat.le_trans
  with
    (length
       (encode A_eq_dec
          (compute_code
             (to_btree (pbbuild empty (restrict_code A_eq_dec m c)))) m));
 auto.
repeat
 rewrite
  weight_tree_compute with (f := fun x => number_of_occurrences A_eq_dec x m);
 auto.
cut
 (cover_min A (fun x : A => number_of_occurrences A_eq_dec x m)
    (map (fun x : A * nat => leaf (fst x)) (frequency_list A_eq_dec m)) t).
intros (HH1, HH2); apply HH2; auto.
apply
 cover_permutation
  with
    (l1 := map (fun x : A => leaf x)
             (all_leaves
                (to_btree (pbbuild empty (restrict_code A_eq_dec m c))))).
apply cover_all_leaves.
replace (map (fun x : A * nat => leaf (fst x)) (frequency_list A_eq_dec m))
 with
 (map (fun x : A => leaf x) (map (fst (B:=_)) (frequency_list A_eq_dec m))).
apply Permutation_map.
rewrite to_btree_all_leaves.
rewrite frequency_list_restric_code_map with (c := c).
apply Permutation_sym; apply all_pbleaves_pbbuild.
apply restrict_not_null with (A_eq_dec := A_eq_dec); auto.
apply not_null_m; auto.
apply restrict_unique_prefix; auto.
apply frequency_not_null with (1 := frequency_more_than_one); auto.
elim (frequency_list A_eq_dec m); simpl in |- *; auto with datatypes.
intros a0 l H4; apply f_equal2 with (f := cons (A:=btree A)); auto.
apply build_correct; auto.
generalize frequency_more_than_one; case (frequency_list A_eq_dec m);
 simpl in |- *; auto.
intros H; contradict H; auto with arith.
intros; discriminate.
apply to_btree_distinct_leaves; auto.
apply pbbuild_distinct_pbleaves; auto.
apply restrict_unique_prefix; auto.
apply frequency_not_null with (1 := frequency_more_than_one); auto.
case
 (cover_ordered_cover _
    (map (fun x : A * nat => leaf (fst x)) (frequency_list A_eq_dec m)) t).
apply build_cover with (1 := H3).
intros l1 (H4, H5).
apply all_leaves_unique; auto.
apply Permutation_sym in H4.
case Permutation_map_inv with (1 := H4); auto.
intros l2 (HH1, HH2).
rewrite NoDup_ordered_cover with (l1 := l1) (l2 := map (fst (B:=_)) l2); auto.
apply Permutation_NoDup with (l := map (fst (B:=_)) (frequency_list A_eq_dec m));
 auto.
apply Permutation_map; auto.
apply unique_key_NoDup; auto.
apply Permutation_NoDup with (l := map (fst (B:=_)) (frequency_list A_eq_dec m));
 auto.
apply Permutation_map; auto.
apply unique_key_NoDup; auto.
rewrite HH1; elim l2; simpl in |- *; auto.
intros a0 l H6; apply f_equal2 with (f := cons (A:=btree A)); auto.
rewrite
 encode_permutation
                    with
                    (c1 := restrict_code A_eq_dec m c)
                   (c2 := 
                     compute_pbcode
                       (pbbuild empty (restrict_code A_eq_dec m c))).
generalize
 (to_btree_smaller _ A_eq_dec (pbbuild empty (restrict_code A_eq_dec m c))).
intros H4; pattern m at 2 4 in |- *; elim m; simpl in |- *; auto.
intros a0 l H5; repeat rewrite app_length.
apply Nat.add_le_mono; auto.
apply Permutation_sym; apply pbbuild_compute_perm.
apply restrict_not_null with (A_eq_dec := A_eq_dec); auto.
apply not_null_m; auto.
apply restrict_unique_prefix; auto.
apply frequency_not_null with (1 := frequency_more_than_one); auto.
apply restrict_unique_prefix; auto.
apply frequency_not_null with (1 := frequency_more_than_one); auto.
Qed.

Definition huffman_aux_type (l : list (nat * code A)) : Type :=
  l <> [] ->
  ordered (fun x y => fst x <= fst y) l ->
  (forall a,
   In a l -> compute_code (to_btree (pbbuild empty (snd a))) = snd a) ->
  (forall a,
   In a l ->
   sum_leaves (fun x => number_of_occurrences A_eq_dec x m)
     (to_btree (pbbuild empty (snd a))) = fst a) ->
  (forall a, In a l -> snd a <> []) ->
  {c : code A |
  compute_code (to_btree (pbbuild empty c)) = c /\
  build (fun x => number_of_occurrences A_eq_dec x m)
    (map (fun x => to_btree (pbbuild empty (snd x))) l)
    (to_btree (pbbuild empty c))}.

(** Auxiliary function to compute minimal code *)
Program Definition huffman_aux_F (l1 : list (nat * code A))
 (huffman_aux_rec : forall l2 : list (nat * code A), length l2 < length l1 -> huffman_aux_type l2) :
 huffman_aux_type l1 :=
match l1 with
| [] => eq_rect [] huffman_aux_type (fun _ _ _ _ _ => False_rect _ _) _ _
| (n1, c1) :: [] => fun nnil ord cc sl lin => exist _ c1 _
| (n1, c1) :: (n2, c2) :: l0 => fun nnil ord cc sl lin =>
  let (c3, _) :=
   huffman_aux_rec
     (insert (fun x y => fst x <=? fst y)
      (n1 + n2,
       map (fun x => (fst x, false :: snd x)) c1 ++
        map (fun x => (fst x, true :: snd x)) c2) l0) _ _ _ _ _ _
  in exist _ c3 _
end.
Next Obligation.
  split; [|apply build_one].
  apply cc with (a := (n1, c1)); auto with datatypes.
Qed.
Next Obligation.
  rewrite
    Permutation_length
    with
      (l' :=
         (n1 + n2,
          map (fun x : A * list bool => (fst x, false :: snd x))
              c1 ++
              map (fun x : A * list bool => (fst x, true :: snd x))
              c2) :: l0).
  simpl in |- *; auto with arith.
  apply Permutation_sym; apply insert_permutation.
Qed.
Next Obligation.
  red in |- *; intros H5;
    absurd
      ((n1 + n2,
        map (fun x : A * list bool => (fst x, false :: snd x)) c1 ++
            map (fun x : A * list bool => (fst x, true :: snd x)) c2) :: l0 = []).
  intros; discriminate.
  apply Permutation_nil; auto.
  apply Permutation_sym.
  unfold code in H5; rewrite <- H5; apply insert_permutation.
Qed.
Next Obligation.
  apply insert_ordered; auto.
  intros a b H5; apply leb_complete; auto.
  intros a b H5; apply Nat.leb_gt in H5; auto with arith.
  apply ordered_inv with (a := (n2, c2)).
  apply ordered_inv with (a := (n1, c1)); auto.
Qed.
Next Obligation.
  remember(n, c) as a.
  cut
    (In a
        ((n1 + n2,
          map (fun x : A * list bool => (fst x, false :: snd x)) c1 ++
              map (fun x : A * list bool => (fst x, true :: snd x)) c2) :: l0)).
  simpl in |- *; intros [H6| H6]; try rewrite <- H6; simpl in |- *;
    auto with datatypes.
  rewrite pbbuild_pbnode; simpl in |- *; auto with datatypes.
  apply f_equal2 with (f := app (A:=A * list bool)); auto.
  generalize (cc (n1, c1)); simpl in |- *; intros tmp; rewrite tmp; clear tmp;
    auto with datatypes.
  elim c1; simpl in |- *; auto.
  intros a0; case a0; simpl in |- *; auto.
  intros a1 l1 l2 H7; apply f_equal2 with (f := cons (A:=A * list bool)); auto.
  generalize (cc (n2, c2)); simpl in |- *; intros tmp; rewrite tmp; clear tmp;
    auto with datatypes.
  elim c2; simpl in |- *; auto.
  intros a0; case a0; simpl in |- *; auto.
  intros a1 l1 l2 H7; apply f_equal2 with (f := cons (A:=A * list bool));
    auto with datatypes.
  generalize (lin (n1, c1)); simpl in |- *; auto with datatypes.
  generalize (lin (n2, c2)); simpl in |- *; auto with datatypes.
  apply Permutation_in with (2 := H).
  apply Permutation_sym; apply insert_permutation.
Qed.
Next Obligation.
  remember(n, c) as a.
  cut
    (In a
        ((n1 + n2,
          map (fun x : A * list bool => (fst x, false :: snd x)) c1 ++
              map (fun x : A * list bool => (fst x, true :: snd x)) c2) :: l0)).
  simpl in |- *; intros [H6| H6]; try rewrite <- H6; simpl in |- *;
    auto with datatypes.
  rewrite pbbuild_pbnode; simpl in |- *; auto with datatypes.
  apply f_equal2 with (f := plus); auto.
  generalize (sl (n1, c1)); simpl in |- *; auto with datatypes.
  generalize (sl (n2, c2)); simpl in |- *; auto with datatypes.
  generalize (lin (n1, c1)); simpl in |- *; auto with datatypes.
  generalize (lin (n2, c2)); simpl in |- *; auto with datatypes.
  apply Permutation_in with (2 := H).
  apply Permutation_sym; apply insert_permutation.
Qed.
Next Obligation.
  remember(n, c) as a.
  cut
    (In a
        ((n1 + n2,
          map (fun x : A * list bool => (fst x, false :: snd x)) c1 ++
              map (fun x : A * list bool => (fst x, true :: snd x)) c2) :: l0)).
  simpl in |- *; intros [H6| H6]; try rewrite <- H6; simpl in |- *;
    auto with datatypes.
  generalize (lin (n1, c1)); case c1; simpl in |- *; auto with datatypes.
  intros; discriminate.
  apply Permutation_in with (2 := H).
  apply Permutation_sym; apply insert_permutation.
Qed.
Next Obligation.
  split; auto.
  apply build_step with (2 := H0); auto.
  simpl in |- *; red in |- *.
  exists (map (fun x : nat * code A => to_btree (pbbuild empty (snd x))) l0);
    exists (to_btree (pbbuild empty c1)); exists (to_btree (pbbuild empty c2));
      repeat (split; auto).
  - change
      (ordered (sum_order (fun x : A => number_of_occurrences A_eq_dec x m))
               (map (fun x : nat * code A => to_btree (pbbuild empty (snd x)))
                    ((n1, c1) :: (n2, c2) :: l0))) in |- *.
    apply ordered_map_inv; auto.
    assert (H2' : forall a, In a ((n1, c1) :: (n2, c2) :: l0) ->
     sum_leaves (fun x : A => number_of_occurrences A_eq_dec x m)
      (to_btree (pbbuild empty (snd a))) = fst a) by apply sl.
    generalize H2' ord; elim ((n1, c1) :: (n2, c2) :: l0); (simpl in |- *; auto).
    intros a l1; case a; case l1; simpl in |- *; auto; clear a l1.
    intros p0 l1 n4 c4; case p0; intros n5 c5; simpl in |- *; clear p0; auto.
    intros H6 H7 H8; apply ordered_cons; unfold sum_order in |- *; simpl in |- *;
      auto.
    * generalize (H7 (n4, c4)); simpl in |- *; intros tmp; rewrite tmp; clear tmp;
        auto with datatypes.
      generalize (H7 (n5, c5)); simpl in |- *; intros tmp; rewrite tmp; clear tmp;
        auto with datatypes.
      change (fst (n4, c4) <= fst (n5, c5)) in |- *.
      apply ordered_inv_order with (1 := H8); auto.
    * apply H6; auto.
      apply ordered_inv with (1 := H8); auto.
  - apply
      Permutation_trans
      with
        (map (fun x : nat * code A => to_btree (pbbuild empty (snd x)))
             ((n1 + n2,
               map (fun x : A * list bool => (fst x, false :: snd x)) c1 ++
                   map (fun x : A * list bool => (fst x, true :: snd x)) c2) :: l0));
      auto.
    apply Permutation_map; auto.
    apply Permutation_sym; apply insert_permutation.
    apply
      Permutation_trans
      with
        (map (fun x : nat * code A => to_btree (pbbuild empty (snd x)))
             ((n1 + n2,
               map (fun x : A * list bool => (fst x, false :: snd x)) c1 ++
                   map (fun x : A * list bool => (fst x, true :: snd x)) c2) :: l0));
      auto.
    simpl in |- *; auto.
    rewrite pbbuild_pbnode; auto.
    generalize (lin (n1, c1)); simpl in |- *; auto with datatypes.
    generalize (lin (n2, c2)); simpl in |- *; auto with datatypes.
Qed.

Definition huffman_aux : forall l : list (nat * code A), huffman_aux_type l :=
 list_length_induction (nat * code A) huffman_aux_type huffman_aux_F.

(** The Huffman algorithm *)
Program Definition huffman :
  {c : code A |
  unique_prefix c /\
  in_alphabet m c /\
  (forall c1 : code A,
   unique_prefix c1 ->
   in_alphabet m c1 -> weight A_eq_dec m c <= weight A_eq_dec m c1)} :=
let (c, _) :=
  huffman_aux
    (isort (fun x y => fst x <=? fst y)
      (map (fun x => (snd x, (fst x, []) :: [])) (frequency_list A_eq_dec m))) _ _ _ _ _
in exist _ c _.
Next Obligation.
  generalize frequency_more_than_one; case (frequency_list A_eq_dec m);
    simpl in |- *; auto.
  intros H; contradict H; auto with arith.
  intros p l frequency_more_than_one_bis H.
  absurd (In (A:=nat * code A) (snd p, (fst p, []) :: []) []).
  simpl in |- *; intros H1; case H1.
  rewrite <- H;
    apply
      Permutation_in
      with
        ((snd p, (fst p, []) :: [])
           :: isort
           (fun x y : nat * list (A * list bool) => fst x <=? fst y)
           (map (fun x : A * nat => (snd x, (fst x, []) :: [])) l));
    auto with datatypes.
  (* FIXME: prove by contradict instead *)
  apply insert_permutation.
Qed.
Next Obligation.
  apply isort_ordered; auto.
  intros a b H0; apply leb_complete; auto.
  intros a b H0; apply Nat.leb_gt in H0; auto with arith.
Qed.
Next Obligation.
  cut
    (In (n, c)
        (map (fun x : A * nat => (snd x, (fst x, []) :: []))
             (frequency_list A_eq_dec m))).
  intros H1; case (proj1 (in_map_iff _ _ _)) with (1 := H1); auto.
  intros x; case x; simpl in |- *; auto.
  intros a0 n0 (H3,H2).
  inversion H3; subst; simpl in |- *; auto.
  apply Permutation_in with (2 := H); auto.
  apply Permutation_sym; apply isort_permutation; auto.
Qed.
Next Obligation.
  cut
    (In (n, c)
        (map (fun x : A * nat => (snd x, (fst x, []) :: []))
             (frequency_list A_eq_dec m))).
  intros H1; case (proj1 (in_map_iff _ _ _)) with (1 := H1); auto.
  intros x; case x; simpl in |- *; auto.
  intros a0 n0 (H3,H2). inversion H3; subst; simpl in |- *; auto.
  apply unique_key_in_inv with (a := a0) (l := frequency_list A_eq_dec m); auto.
  apply frequency_number_of_occurrences; auto.
  apply frequency_list_in with (1 := H2); auto.
  apply Permutation_in with (2 := H); auto.
  apply Permutation_sym; apply isort_permutation; auto.
Qed.
Next Obligation.
  cut
    (In (n, c)
        (map (fun x : A * nat => (snd x, (fst x, []) :: []))
             (frequency_list A_eq_dec m))).
  intros H1; case (proj1 (in_map_iff _ _ _)) with (1 := H1); auto.
  intros x; case x; simpl in |- *; auto.
  intros a0 n0 (H3,H2); inversion H3; subst; simpl in |- *; auto.
  intros; discriminate.
  apply Permutation_in with (2 := H); auto.
  apply Permutation_sym; apply isort_permutation; auto.
Qed.
Next Obligation.
  rename H into Hc1.
  rename H0 into Hc2.
  cut
    (build (fun x : A => number_of_occurrences A_eq_dec x m)
           (map (fun x => leaf (fst x)) (frequency_list A_eq_dec m))
           (to_btree (pbbuild empty c))); [ intros Hc3 | idtac ].
  case
    (cover_ordered_cover _
                         (map (fun x : A * nat => leaf (fst x)) (frequency_list A_eq_dec m))
                         (to_btree (pbbuild empty c))).
  apply build_cover with (1 := Hc3).
  intros l1 (H4, H5).
  apply Permutation_sym in H4.
  case Permutation_map_inv with (1 := H4); auto.
  intros l2 (HH1, HH2).
  split; auto.
  rewrite <- Hc1; auto.
  apply btree_unique_prefix; auto.
  apply all_leaves_unique; auto.
  rewrite NoDup_ordered_cover with (l1 := l1) (l2 := map (fst (B:=_)) l2); auto.
  apply Permutation_NoDup with (l := map (fst (B:=_)) (frequency_list A_eq_dec m));
    auto.
  apply Permutation_map; auto.
  apply unique_key_NoDup; auto.
  apply Permutation_NoDup with (l := map (fst (B:=_)) (frequency_list A_eq_dec m));
    auto.
  apply Permutation_map; auto.
  apply unique_key_NoDup; auto.
  rewrite HH1; elim l2; simpl in |- *; auto.
  intros a0 l H6; apply f_equal2 with (f := cons (A:=btree A)); auto.
  split; auto.
  rewrite <- Hc1; auto.
  apply in_alphabet_compute_code; auto.
  intros a H; apply all_leaves_inb.
  rewrite NoDup_ordered_cover with (l1 := l1) (l2 := map (fst (B:=_)) l2); auto.
  apply Permutation_in with (map (fst (B:=_)) (frequency_list A_eq_dec m)); auto.
  apply Permutation_map; auto.
  apply Permutation_NoDup with (l := map (fst (B:=_)) (frequency_list A_eq_dec m));
    auto.
  apply Permutation_map; auto.
  apply unique_key_NoDup; auto.
  rewrite HH1; elim l2; simpl in |- *; auto.
  intros a0 l H6; apply f_equal2 with (f := cons (A:=btree A)); auto.
  intros c1 H H0.
  rewrite <- Hc1.
  apply huffman_build_minimum; auto.
  apply build_permutation with (1 := Hc2); auto.
  apply
    Permutation_trans
    with
      (map (fun x : nat * code A => to_btree (pbbuild empty (snd x)))
           (map (fun x : A * nat => (snd x, (fst x, []) :: []))
                (frequency_list A_eq_dec m))).
  apply Permutation_map; apply Permutation_sym; apply isort_permutation.
  elim (frequency_list A_eq_dec m); simpl in |- *; auto.
Qed.
 
End Huffman.
