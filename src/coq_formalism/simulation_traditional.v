(* Traditional simulation as defined in "Introduction to Bisimulation and Coinduction" 
   Files proves said definition is reflexive and transitive 
  
    By : Anna Fritz 
    Date: August 17, 2023 

*)

Require Import Coq.Classes.RelationClasses.

Module StrongSimulation.

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

End StrongSimulation.

Module WeakSimulation. 

Inductive silent := 
| sl : silent.

Record LTS : Type := {
    st : Set ;
    step_labeled : st -> nat -> st -> Prop ; 
    step_silent : st -> st -> Prop
  }.

(* transitive reflexive closure of the states *)
Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TrcRefl : forall x, trc R x x
| TrcFront : forall x y z, R x y -> trc R y z -> trc R x z.

(* define similarity with steps for labeled case and steps for silent case *)
Definition similarity (S1 S2: LTS) (R : S1.(st) -> S2.(st) -> Prop) :=
  (forall P Q, R P Q -> forall P' l, S1.(step_labeled) P l P' -> (exists Q', S2.(step_labeled) Q l Q' /\ R P' Q')) 
  /\ 
  (forall P Q, R P Q -> forall P', S1.(step_silent) P P' -> (exists Q', trc S2.(step_silent) Q Q' /\ R P' Q')).
  
Theorem sim_refl : forall lts, exists r, similarity lts lts r.
Proof.
  intros. exists eq. unfold similarity; split; intuition.
  (* labeled case *)
  + exists P'; intuition. rewrite <- H; eauto.
  (* silent case *)
  + exists P'; intuition.
  ++ apply TrcFront with (y := P'). 
  +++ rewrite <- H. eauto.
  +++ econstructor.
Qed.

Inductive relation_comp {A B C : Type} (R1 : A -> B -> Prop ) (R2 : B -> C -> Prop ) : A -> C -> Prop :=
| rc : forall a c, (exists b, R1 a b /\ R2 b c) -> relation_comp R1 R2 a c.

Theorem  sim_trans : forall P Q R, 
                    (exists r1, similarity P Q r1) -> 
                    (exists r2, similarity Q R r2) -> 
                    (exists r3, similarity P R r3).
Proof.
  intros.
  destruct H as [RPQ]; intuition.
  destruct H0 as [RQR]; intuition.
  exists (relation_comp RPQ RQR).
  unfold similarity in *.
  destruct H as [PQ_lab PQ_sil].
  destruct H0 as [QR_lab QR_sil].
  split; intros p1 q1 H p2.
  + (* labeled case *) 
    destruct H as [p1 r1].
    destruct H as [q1]; intuition.
    apply PQ_lab with (Q := q1) in H; intuition.
    destruct H as [q2]; intuition.
    apply QR_lab with (Q := r1) in H2; intuition.
    destruct H2 as [r2]; intuition.
    exists r2; intuition.
    eapply rc; eauto.
  + (* silent case *) 
    intros.
    destruct H as [p1 r1].
    destruct H as [q1]; intuition.
    eapply PQ_sil in H1; intuition; eauto.
    destruct H1 as [q2]; intuition. 
    induction H1 as [q1 | q1 q2 q3].
  ++ (* q1 takes 0 steps *)
      exists r1. intuition; econstructor.
      exists q1; intuition.
  ++ (* q1 takes at least 1 step *) 
     apply QR_sil with (Q := r1) in H; intuition.
     destruct H as [r2]; intuition.
     induction H4 as [r1 | r1 r2 r3].
  +++ apply IHtrc; eauto.
Abort. 
