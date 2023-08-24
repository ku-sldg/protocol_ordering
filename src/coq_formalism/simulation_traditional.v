(* Traditional simulation as defined in "Introduction to Bisimulation and Coinduction" 
   Files proves said definition is reflexive and transitive 
  
    By : Anna Fritz 
    Date: August 17, 2023 

*)

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Equality.

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
| TrcFront : forall x y, R x y -> forall z, trc R y z -> trc R x z.

Theorem trc_trans :  forall {A} (R : A -> A -> Prop) x y, trc R x y
-> forall z, trc R y z
  -> trc R x z.
Proof.
  intros. induction H.
  + assumption.
  + eapply TrcFront.
  ++ eassumption.
  ++ apply IHtrc. eauto.
Qed.  

Inductive silentplus (lts : LTS) : lts.(st) -> lts.(st) -> Prop := 
| star_single : forall (s s' : lts.(st)), lts.(step_silent) s s' ->  
                                            silentplus lts s s'
| star_tran : forall (s s' s'' : lts.(st)), 
                lts.(step_silent) s s' -> 
                silentplus lts s' s'' ->  silentplus lts s s''.

Lemma trc_slientplus : forall LTS x y,
                              LTS.(step_silent) x y ->
                              trc LTS.(step_silent) x y ->
                              silentplus LTS x y.
Proof.
  intros. induction H0.
  + econstructor; eauto.
  + econstructor. eauto.
Qed.     

Lemma trc_slientplus' : forall LTS y z,
                              trc LTS.(step_silent) y z ->
                              silentplus LTS y z.
Proof.
  intros. induction H.
  + econstructor; eauto.
Abort. 

(* define similarity with steps for labeled case and steps for silent case... this definition is wrong as it does not take into consideration silent transitions for the labeled case  *)
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

(* reframming trc definition to say that the last step is silent *)
Lemma last_step : forall lts x y,
    trc (step_silent lts) x y  -> 
    x = y \/ exists int, trc (step_silent lts) x int /\ step_silent lts int y.
Proof.
  intros.
  induction H.
  + left. reflexivity.
  + inversion IHtrc.
  ++ subst. right. exists x; split; eauto; econstructor.
  ++ right. destruct H1 as [x' [H1 H2]].
     exists x'. split; auto.
     eapply TrcFront; eauto.
Qed.

(* the last step of a transition is in the transitive
 * reflexive closure *)
Lemma last_step_is_in_trc : forall lts x y z, 
  trc (step_silent lts) x y -> 
  step_silent lts y z -> 
  trc (step_silent lts) x z.
Proof. 
  intros.
  induction H; eapply TrcFront; eauto; econstructor.
Qed. 

Ltac dest_sp H v := destruct H as [v]; intuition.

(* prove the incorrect def is transitive *)
Theorem  sim_trans_incorrect : forall P Q, 
                    (exists r1, similarity P Q r1) -> 
                    forall R, (exists r2, similarity Q R r2) -> 
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
    eapply PQ_sil  with (P' := p2) in H0; eauto.
    destruct H0 as [q2]; intuition.
    (* must do something here are trc q1 q2 *)
    generalize dependent r1.
    clear H1.  
    induction H0.
  ++ intros. exists r1; repeat econstructor; eauto.  
  ++ intuition. apply QR_sil with (P' := y) in H2; eauto.
     destruct H2 as [r2]; intuition.
     specialize H1 with r2. intuition. 
     destruct H2 as [r3]; intuition.
     exists r3. intuition.
     apply trc_trans with (y := r2); eauto.
Qed.  

(* random Ltac that is useful for the labeled case *)
Ltac destruct_all q2 q3 q' H1 := destruct H1 as [q2 H1];  destruct H1 as [q3 H1];  destruct H1 as [q']; intuition.
Ltac exists_all q1 q2 q' := exists q1; exists q2; exists q'.

(*****************************
CORRECT SIMILARITY DEFINITION 
*****************************)

(* define similarity with steps for labeled case and steps for silent case *)
Definition similarity' (S1 S2: LTS) (R : S1.(st) -> S2.(st) -> Prop) :=
  (forall P Q, R P Q -> forall P' l, S1.(step_labeled) P l P' -> (exists Q1 Q2 Q', trc S2.(step_silent) Q Q1 /\ S2.(step_labeled) Q1 l Q2 /\ trc S2.(step_silent) Q2 Q' /\ R P' Q')) 
  /\ 
  (forall P Q, R P Q -> forall P', S1.(step_silent) P P' -> (exists Q', trc S2.(step_silent) Q Q' /\ R P' Q')).

Theorem  sim_trans' : forall P Q, 
(exists r1, similarity' P Q r1) -> 
forall R, (exists r2, similarity' Q R r2) -> 
(exists r3, similarity' P R r3).
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
    intros. 
    destruct H as [p1 r1].
    destruct H as [q1]; intuition.
    eapply PQ_lab with (P' := p2) in H0; intuition; eauto.
    destruct_all q2 q3 q' H0.
    generalize dependent r1.
(*    generalize dependent q'. *)
    clear H1.
    
    
  (* induction H0.
  ++ intros. 
     induction H3. 
  +++ intros. eapply QR_lab in H2; eauto.
     destruct_all r2 r3 r' H2.
     exists_all r2 r3 r'; intuition.
     econstructor; exists x0; eauto.
  +++ eapply QR_lab in H2; eauto.
      destruct_all r2 r3 r' H2.
      eapply QR_sil in H7; eauto.
      destruct H7; intuition.
 
      if you proceed by induction on first trc then you are stuck with an unuseable induction hypothesis 
 
      *)





    (* try with induction on the second trc *)
    induction H3.
  ++ intros.  generalize dependent r1.
     induction H0.
  (* 0 trc steps... q2 =l=> q3 *)
  +++ intros. eapply QR_lab in H2; eauto. destruct_all r2 r3 r' H2.
      exists_all r2 r3 r'. intuition; eauto. econstructor; intuition; eauto.
  (* silent step from q0 => q1 =trc=> q2 =l=> q3 *)
  +++ intuition. apply QR_sil with (P' := y) in H3; intuition.
      destruct H3 as [r2]; intuition.
      specialize H2 with r2. intuition.  
      destruct_all r3 r4 r' H3.
      exists_all r3 r4 r'; intuition.
      apply trc_trans with (y := r2); eauto.
  ++ intuition. generalize dependent r1. induction H0.
  +++ intuition.  eapply QR_lab in H2; eauto.
      destruct_all r2 r3 r' H2.
      (* stuck in the same spot again... the issue is when the second trc is transitive 
         because you get a weird hypothesis about the labeled step ... *)

