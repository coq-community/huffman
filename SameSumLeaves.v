(**********************************************************************
    Proof of Huffman algorithm: SameSumLeaves.v                      
                                                                     
    Definition of the equality of sum leaves                         
                                                                     
    Definition: same_sum_leaves                                      
                                                                     
                                    Laurent.Thery@inria.fr (2003)    
  **********************************************************************)
Require Export Cover.
Require Export WeightTree.
 
Section SameSumLeaves.
Variable A : Set.
Variable f : A -> nat.
(* 
   the sum leaves are the same upto permutation
   *)
 
Definition same_sum_leaves (l1 l2 : list (btree A)) : Prop :=
  exists l3 : list (btree A),
    (exists l4 : list (btree A),
       permutation l1 l3 /\
       permutation l2 l4 /\ map (sum_leaves f) l3 = map (sum_leaves f) l4).
(* 
   if the sum leaves are the same, the list are of same length
   *)
 
Theorem same_sum_leaves_length :
 forall l1 l2 : list (btree A),
 same_sum_leaves l1 l2 -> length l1 = length l2.
intros l1 l2 (l3, (l4, (H0, (H1, H2)))).
rewrite (permutation_length _ _ _ H0).
rewrite (permutation_length _ _ _ H1).
repeat rewrite <- (length_map _ _ (sum_leaves f)); auto.
apply f_equal with (f := length (A:=nat)); auto.
Qed.
 
End SameSumLeaves.
Implicit Arguments same_sum_leaves [A].