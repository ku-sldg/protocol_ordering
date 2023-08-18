(* Traditional simulation as defined in "Introduction to Bisimulation and Coinduction" 
   Files proves said definition is reflexive and transitive 
  
    By : Anna Fritz 
    Date: August 17, 2023 

*)

Require Import Coq.Classes.RelationClasses.

(* make abstract labeled transition system where labels are natural numbers *)
Record LTS : Type := {
    st : Set ;
    step : st -> nat -> st -> Prop 
  }.

Definition similarity (S1 S2: LTS) (R : S1.(st) -> S2.(st) -> Prop) :=
  forall P Q, R P Q -> forall P' u, S1.(step) P u P' -> (exists Q', S2.(step) Q u Q' /\ R P' Q').
  
Theorem sim_refl : forall lts, exists r, similarity lts lts r.
Proof.
  intros. exists eq. unfold similarity.
  intros.
  exists P'; intuition. rewrite <- H; eauto.
Qed.

Inductive relation_comp {A B C : Type} (R1 : A -> B -> Prop ) (R2 : B -> C -> Prop ) : A -> C -> Prop :=
| rc : forall a c, (exists b, R1 a b /\ R2 b c) -> relation_comp R1 R2 a c.

Theorem  sim_trans : forall X Y Z, 
                    (exists r1, similarity X Y r1) -> 
                    (exists r2, similarity Y Z r2) -> 
                    (exists r3, similarity X Z r3).
Proof.
  intros.
  destruct H as [RPQ]; intuition.
  destruct H0 as [RQR]; intuition.
  exists (relation_comp RPQ RQR).
  unfold similarity in *.
  intros P R H1 P' u stepx.
  destruct H1 as [P R].
  destruct H1 as [Q].
  destruct H1.
  eapply H in stepx; intuition.
  + destruct stepx as [Q'].
    destruct H3.
    eapply H0 in H3.
  ++ destruct H3 as [R'].
     exists R'. inversion H3; eauto.
     split.
  +++ eauto.
  +++ apply rc. exists Q'; split; eauto.
  ++ eauto.
  + eauto.
Qed. 