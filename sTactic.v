(**********************************************************************
    Proof of Huffman algorithm: sTactic.v                            
                                                                     
    Useful tactics                                                   
                                                                     
    Tactics: Contradict, CaseEq, ElimEq                              
                                    Laurent.Thery@inria.fr (2003)    
  **********************************************************************)
 
Theorem Contradict1 : forall a b : Prop, b -> (a -> ~ b) -> ~ a.
intuition.
Qed.
 
Theorem Contradict2 : forall a b : Prop, b -> ~ b -> a.
intuition.
Qed.
 
Theorem Contradict3 : forall a : Prop, a -> ~ ~ a.
auto.
Qed.
(* 
   Contradict is used to contradict an hypothesis H
     if we have H:~A |- B the result is |- A
     if we have H:~A |- ~B the result is H:B |- A
   A tactic to deal with assumption that starts with a negation:
      ~H |- G gives |- H
   *)
 
Ltac Contradict name :=
  (apply (fun a : Prop => Contradict1 a _ name); clear name; intros name) ||
    (apply (fun a : Prop => Contradict2 a _ name); clear name);
   try apply Contradict3.
(* 
  Same as Case but keep the equality 
   *)
 
Ltac CaseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.
(* 
  Same as Case but clear the variable
   *)
 
Ltac Casec name := case name; clear name.
(* 
  Same as Elim but clear the variable  
   *)
 
Ltac Elimc name := elim name; clear name.