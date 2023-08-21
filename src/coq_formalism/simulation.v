(* stuck in this file proving transitivity *)

(******************************
    Looking into the following simulations relations 
    - Bisimulation 
    - Weak Bisimulation 
    - Branching Bisimulation 
    
    By: Anna Fritz
    Date: August 2, 2023 *)

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Classes.RelationClasses.
Set Implicit Arguments.

Section LabeledTransitionSystem.

Context {L: Set}. 
 
(* Redefine Labeled Transition System to include silent labels *)
Inductive sl := 
| silentlabel.

Record LTS : Type := {
    st : Set ; 
    initial : st -> Prop ; 
    step : st -> st -> Prop ;
    l : st -> L + sl
  }.

(* some state is an initial state if there does not exists any state which steps to that state *)
Hypothesis LTS_init : forall lts st2, lts.(initial) st2 <-> forall st1, ~ lts.(step) st1 st2.  

(* The transition system is left total *)
Hypothesis left_total : forall lts s, exists s', lts.(step) s s'.

(* labels are decidable *)
Hypothesis label_dec : forall a b: L, {a = b} + {a <> b}.


(**********************************************
* SILENTSTAR AND SILENTPLUS 
**********************************************)

(* the transitive reflexive closure of silent transitions *)
Inductive silentstar (lts : LTS) : lts.(st) -> lts.(st) -> Prop := 
| star_refl : forall (s : lts.(st)), silentstar lts s s
| star_trans : forall (s s' : lts.(st)), 
                (lts.(step) s s' /\ lts.(l) s = inr silentlabel) -> 
                forall s'', silentstar lts s' s'' ->  silentstar lts s s''.

(* silentplus takes one or more steps *)
Inductive silentplus (lts : LTS) : lts.(st) -> lts.(st) -> Prop := 
| star_single : forall a (s s' : lts.(st)), lts.(step) s s' -> 
                                            lts.(l) s = inr silentlabel ->
                                            lts.(l) s' = inl a -> 
                                            silentplus lts s s'
| star_tran : forall (s s' s'' : lts.(st)), 
                lts.(step) s s' -> 
                lts.(l) s = inr silentlabel -> 
                lts.(l) s' = inr silentlabel -> 
                silentplus lts s' s'' ->  silentplus lts s s''.

                
(**********************************************
* PROPERTIES OF SILENTSTAR AND SILENTPLUS 
**********************************************)
                
Theorem silentstar_trans : forall (lts : LTS) x y , 
  silentstar lts x y -> 
  forall z, silentstar lts y z -> 
  silentstar lts x z.
Proof.
  intros lts x y. intros H. intros z. induction H.
  + eauto.
  + intros. destruct H. apply IHsilentstar in H1. eapply star_trans.
    eauto. eauto.
Qed.

(* If you step from one silent state to a labeled state the you must 
 * have some last (int) silent state before hitting the label. *)
 Lemma silentstar_step : forall LTS sil lab a,
 silentstar LTS sil lab ->
 LTS.(l) sil = inr silentlabel ->
 LTS.(l) lab = inl a ->
 exists int, silentstar LTS sil int /\ LTS.(l) int = inr silentlabel /\ LTS.(step) int lab.
Proof.
 intros lts sil lab a. intros. 
 induction H.
 (* base case : star_refl *)
 + rewrite H0 in H1. inversion H1.
 + destruct (l lts s') as [b | ] eqn:Heq.
 (* s' is labeled *)
 ++ inversion H. inversion H2; subst.
 +++ exists s; repeat split; intuition; try econstructor.
 +++ rewrite Heq in H5. inversion H5. inversion H8.
 (* s' is silent *)
 ++ destruct s0; intuition.
    destruct H5 as [int1].
    exists int1; repeat split; intuition.
    subst.
    eapply star_trans; eauto.
Qed. 

(* if a silent state takes zero or more transitions 
* to a labeled state, then either the silent state has 
* stepped to the labeled state or there is some intermediate 
* silent state which the first silent state steps to 
* before taking zero or more steps to the labeled state
* *)
Lemma silentstar_stepfirst : forall LTS sil lab a,
 silentstar LTS sil lab ->
 LTS.(l) sil = inr silentlabel ->
 LTS.(l) lab = inl a ->
 (LTS.(step) sil lab) \/ 
 (exists int, LTS.(step) sil int /\ LTS.(l) int = inr silentlabel /\ silentstar LTS int lab).
Proof.
 intros. induction H. 
 (* base case : state steps to itself but it cannot be 
  * labeled and unlabeled at the same time *)
 + rewrite H0 in H1. inversion H1.
 + destruct H2.
 ++ left; eauto.  intuition.
 ++ intuition.
 (* prove with hypothesis s0 steps to s''*)
 +++ right. exists s0; repeat split; eauto.
 ++++ eapply star_trans; eauto.
      eapply star_refl.
 (* now with hypothesis there is some intermediate step *)
 +++ destruct H2. right; intuition.
     exists s0; repeat split; eauto.
     eapply star_trans with (s' := s'); eauto.
Qed.    

(* if you've taken 0 or more steps from a silent state to a labeled state
 * then you've taken one or more steps *)
Lemma silentstar_slientplus : forall LTS sil lab a,
 silentstar LTS sil lab ->
 LTS.(l) sil = inr silentlabel ->
 LTS.(l) lab = inl a ->
 silentplus LTS sil lab.
Proof.
  intros. induction H.
  + rewrite H1 in H0. inversion H0.
  + destruct H2.
  ++ apply star_single with (a := a); eauto; intuition.
  ++ eapply star_tran with (s' := s0); eauto; intuition.
Qed. 

Lemma silentplus_silentstar : forall LTS s s', 
 silentplus LTS s s' -> 
 silentstar LTS s s'.
Proof.
  intros. induction H; intuition; apply star_trans with (s' := s'); intuition; econstructor.
Qed. 

(* somethings not right because we should be able 
   to prove this. 
Lemma silentstar_imples_step : forall LTS q,
 LTS.(l) q = inr silentlabel ->
 forall x, silentstar LTS sil x ->
 step LTS sil sil.
Proof.
  intros. induction H.
  + admit. 
  + destruct H3.
  ++ apply star_single with (a := a); eauto.
  ++ eapply star_tran with (s' := s0); eauto; intuition.
Qed. *)

(**********************************************
* REASONING ABOUT PROPERTIES OVER LTS   
**********************************************)

(* transitive reflexive closure of the states *)
Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TrcRefl : forall x, trc R x x
| TrcFront : forall x y z, R x y -> trc R y z -> trc R x z.

(* A useful general notion for transition systems: reachable states *)
Inductive reachable (sys : LTS) st1 : Prop :=
| Reachable : forall st0, sys.(initial) st0 -> trc sys.(step) st0 st1-> reachable sys st1.

(* We want to say any state is reachable *)
Theorem reachable_by_init : forall sys s1, reachable sys s1.
Proof.
  intros sys s1. specialize LTS_init with sys s1.
  destruct LTS_init.
Admitted. 

(* May need to rely on invariants for transition systems *)
Definition invariantFor (sys : LTS) (invariant : sys.(st) -> Prop) :=
  forall s, sys.(initial) s
            -> forall s', trc sys.(step) s s' -> invariant s'. 

(**********************************************
* DEFINING WEAK SIMULATION  
**********************************************)

(* Our definition of weak simulation. 
 * This is a one-way relation between two LTS.
 * There are three cases.  *)
Definition weakSimulation (S1 S2 : LTS) (R: S1.(st) -> S2.(st) -> Prop) := 

    (* initial case 
     * with added detail to reason about silent labels *)
    (forall (s : S1.(st)), S1.(initial) s -> 
    (exists (r : S2.(st)), S2.(initial) r /\ R s r /\ S1.(l) s = S2.(l) r) \/ 
    (exists (r : S2.(st)),  S2.(initial) r /\ R s r /\ S2.(l) r = inr silentlabel /\ 
     exists (r' : S2.(st)), (silentstar S2 r r' /\ S2.(l) r' = S1.(l) s )))
    /\ 

    (* if there is a silent step in S1 then there exists some related silent step in S2 *)
    ( forall p q, R p q -> forall p', S1.(step) p p' /\ S1.(l) p = inr silentlabel -> 
    ( exists q', silentstar S2 q q' /\ R p' q' /\ S1.(l) p' = S2.(l) q') )
    /\ 
    
    (* if there is some labeled step in S1 then there exists some labeled transition in S2 that may include silent states *)
    (forall p q, R p q -> forall p' a, S1.(step) p p' /\ S1.(l) p = inl a -> 
     exists q1 q2 q', silentstar S2 q q1 /\ S2.(step) q1 q2 /\ S2.(l) q1 = inl a /\ silentstar S2 q2 q' /\ R p' q'). 

(* use weak simulation as a partial order *)
Notation "x <= y" := (weakSimulation x y) (at level 70).

(**********************************************
* PROPERTIES OF WEAK SIMULATION    
**********************************************)

(* Prove that a weak simulation is reflexive *)
Theorem WS_refl : forall x, exists r , (x <= x) r.
Proof. 
     intros.
    (* exists r : st x -> st x -> Prop, *) 
    exists eq.  
    unfold weakSimulation. split.
    + intros. left. exists s; eauto.
    + split.
    ++ intros. exists p'. split; eauto.
    +++ apply star_trans with (s' := p'); try (rewrite <- H; destruct H0 as [H0 H1]; eauto). apply star_refl.
    ++ intros. exists p. exists p'. exists p'; repeat split.
    +++ rewrite <- H; econstructor.
    +++ inversion H0; eauto.
    +++ inversion H0; eauto. 
    +++ apply star_refl. 
Qed. 

(* two ways of defining relational composition *)
(* Inductive relation_comp {A B C : Type} (R1 : A -> B -> Prop ) (R2 : B -> C -> Prop ) : A -> C -> Prop :=
| rc : forall a b c, R1 a b -> R2 b c -> relation_comp R1 R2 a c. *)

Definition rel_dot n m p (x: n -> m -> Prop) (y: m -> p -> Prop): n -> p -> Prop :=
  fun i j => exists2 k, x i k & y k j.

Inductive relation_comp {A B C : Type} (R1 : A -> B -> Prop ) (R2 : B -> C -> Prop ) : A -> C -> Prop :=
| rc : forall a c, (exists b, R1 a b /\ R2 b c) -> relation_comp R1 R2 a c.

(* Prove that weak simulation is transitive *)
Theorem  WS_trans : forall (x y z : LTS),       
                    ( exists r1, (x <= y) r1 ) -> 
                    ( exists r2, (y <= z) r2 ) -> 
                      exists r3, (x <= z) r3.
Proof. 
    intros X Y Z H H0. 
    destruct H as [ Rxy WBxy ].
    destruct H0 as [ Ryz WByz ].
    exists (rel_dot Rxy Ryz).
    unfold weakSimulation; repeat split.
    (* initial case *)
    + destruct WBxy as [xy_initial xy_other].
      destruct WByz as [yz_initial yz_other].
      destruct xy_other as [xy_sil xy_ns].
      destruct yz_other as [yz_sil yz_ns].
      intros x1.
      intros init_x1.
      specialize xy_initial with x1. 
      destruct xy_initial; auto.
      (* y an initial state with same label as x *)
      ++ destruct H as [y1 H].
         specialize yz_initial with y1.
         destruct yz_initial. 
      +++ destruct H; eauto.
      +++ destruct H0 as [z1 H0].
          left. exists z1. repeat split.
      ++++ destruct H0; eauto.
      ++++ destruct H; destruct H0. destruct H1; destruct H2.
           exists y1; eauto.
      ++++ destruct H; destruct H0. destruct H1; destruct H2.
           rewrite H3; eauto.
      +++ destruct H0 as [z1 H0]. right.
          exists z1. repeat split.
      ++++ destruct H0; eauto.
      ++++ destruct H; destruct H0. destruct H1; destruct H2.
           exists y1; eauto.
      ++++ destruct H; destruct H0. destruct H1; destruct H2.
           destruct H4; eauto.
      ++++ destruct H0. destruct H1. destruct H2. destruct H3 as [z2 H3].
           exists z2. split. 
      +++++ inversion H3; eauto.
      +++++ inversion H3. repeat (destruct H).
            destruct H6. rewrite H7; eauto. 
      (* exists some y with a silent label so there must be some y' that has the same label as x*)
      ++ destruct H as [y1 H].
         destruct H. 
         apply yz_initial in H.
         destruct H; eauto.
      (* left case of initial where labels (y and z) are the same *)
      +++ right. intuition.
          destruct H as [z1].
          exists z1. intuition.
      ++++ exists y1; eauto.
      ++++ rewrite <- H5; eauto.
      ++++ destruct H3 as [y2]. destruct H3. 
           destruct (l Y y2) as [a | sil] eqn:l_y2.
      +++++ assert (H' : silentplus Y y1 y2 ). 
            { apply silentstar_slientplus with (a := a).  assumption. eauto. eauto. }
            clear H1 H2. generalize dependent z1. 
            induction H'.
      ++++++ intros. (* H5 : Ryz s z1 *)  
             apply yz_sil with (p' := s') in H5; repeat split; eauto. 
             destruct H5 as [z2]. intuition. exists z2; repeat split; eauto. 
             rewrite <- H9. rewrite <- H4; eauto.
      ++++++ intros. apply yz_sil with (p' := s') in H5; repeat split; eauto. 
             destruct H5 as [z2]. intuition.
             apply silentplus_silentstar in H'. intuition.
             specialize H8 with z2. intuition. destruct H8 as [z3].
             exists z3; repeat split.
             destruct H8.
             apply silentstar_trans with (y := z2); eauto.
             destruct H8; eauto.
      +++++ destruct sil. exists z1. repeat split; eauto.
      ++++++ apply star_refl.
      ++++++ rewrite <- H5. rewrite H0;  eauto.
      (* right case of initial where z may take silent transitions *) 
      +++ right. intuition.
          destruct H as [z1].
          exists z1. intuition.
      ++++ exists y1; eauto.
      ++++ destruct H3 as [y2]. destruct H3. 
          destruct (l Y y2) as [a | sil] eqn:l_y2.
      +++++ assert (H' : silentplus Y y1 y2 ). 
            { apply silentstar_slientplus with (a := a).  assumption. eauto. eauto. }
            clear H1 H2 H4 H6. generalize dependent z1. 
            induction H'.
      ++++++ intros.  apply yz_sil with (p' := s') in H4; repeat split; eauto. 
             destruct H4 as [z2]. intuition. 
             exists z2; repeat split; eauto. 
             rewrite <- H8. rewrite l_y2. eauto.   
      ++++++ intros.  apply yz_sil with (p' := s') in H4; repeat split; eauto. 
             destruct H4 as [z2]. intuition.
             apply silentplus_silentstar in H'. intuition.
             specialize H7 with z2. intuition. destruct H9 as [z3].
             exists z3; repeat split. destruct H7. 
             apply silentstar_trans with (y := z2); eauto.
             destruct H7; eauto.
      +++++ destruct sil. exists z1. repeat split; eauto.
      ++++++ apply star_refl.
      ++++++ rewrite <- H5. eauto.
      + destruct WBxy as [xy_initial xy_other].
        destruct WByz as [yz_initial yz_other].
        destruct xy_other as [xy_sil xy_ns].
        destruct yz_other as [yz_sil yz_ns]. 
        intros x1 z1 Hxy x2 H.
        destruct H.
        destruct Hxy as [y1 Hxy].
        assert (H' : step X x1 x2 /\ l X x1 = inr silentlabel). { split; eauto. }
        apply xy_sil with (q := y1) in H'; intuition.
        destruct H' as [y2]; intuition.
        destruct (l X x2) as [a |] eqn:l_x2.
      ++ (* x2 is labeled *) 
        destruct (l Y y1) as [b |] eqn:l_y1.
      +++ (* y1 is labeled *)
          induction H3 as [y1 | ].
      ++++ destruct (label_dec a b); subst. 
      +++++  destruct left_total with (lts := Y) (s := y1) as [y2].
             apply yz_ns with (p' := y1) (a := b) in H1; eauto.
           destruct H1 as [z2 H1]; destruct H1 as [z3 H1]; destruct H1 as [z' H1]; intuition.
           exists z'; intuition; eauto.
      ++++++ admit.
      ++++++ exists y1; eauto.
      ++++++   
           
      +++    
        
  
 
     Admitted. 

(* potentially we need to say more about the states. Maybe a finite set?? 
 * WB for LTS weighted over simirings: https://arxiv.org/pdf/1310.4106.pdf 
 * verification on infinite structures : 
   https://www.sciencedirect.com/science/article/abs/pii/B9780444828309500278 *)

(* need to define equal... and prove that it's an equivalence relation 
 * maybe isomorphism as equivalence ...?
 * Here: https://github.com/coq-contribs/ccs/blob/master/Trans_Sys.v 
 * different equivalence's are defined over transition systems  *)

(* consider redefining bisimulation like this... http://lmf.di.uminho.pt/ac-1718/slides/AC1718-2-LTS.pdf *)

Lemma WB_antisym : forall x y, 
                    ( exists r1, weakBisimulation x y r1 ) -> 
                    ( exists r2, weakBisimulation y x r2 ) -> 
                      x = y.

(* Three cases for graph comparison 
 * 1. <= /\ = -> = 
 * 2. <= /\ <> -> < 
 * 3. incomparable *)

(* Consider sets of graph comparison *)

(* check out: Algorithms for Computing Weak Bisimulation Equivalence *)
