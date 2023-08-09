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

Module TransitionSystem. 

Context {label L: Set}.  

(* First, define Labeled Transition System
 * Given a set of states and labels, 
 * define a transition relation and initial state.  *)

(* Formally, a labeled transition system is defined as 
 * 1. A set of states 
 * 2. A set of labels (or actions) 
 * 3. A transition relation *)

Record TS (state : Type) : Type := {
    initial_ts : state;
    step_ts : state -> label -> state -> Prop 
}.

Check TS.
(* Check TS.(step_ts). *)

Definition relation (X : Type) := X -> X -> Prop.

(* bisimilarity relation for two states 
* type of this relation should be state -> state -> Prop *)
Definition BR_state {state} (sys : TS state) (R: relation state) : Prop := 
    forall q p, R q p /\ forall l q', (sys.(step_ts) q l q') -> 
    (exists p', (sys.(step_ts) p l p') /\ R q' p').

(* simulation is one way *)
Definition simulation {state} (S1 S2 : TS state) (R : relation state) : Prop := 
    forall q p, R q p /\ forall q' l, S1.(step_ts) q l q' -> 
    exists p', (S2.(step_ts) p l p') /\ R q' p'.

(* strong bisimulation is two way *)
Definition bisimulation {state1 state2} (S1: TS state1) (S2: TS state2) (R : state1 -> state2 -> Prop) : Prop := 
    R S1.(initial_ts) S2.(initial_ts) /\
    ( forall q p, R q p /\ forall q' l, S1.(step_ts) q l q' -> 
    exists p', (S2.(step_ts) p l p') /\ R q' p' ) /\
    ( forall q p, R q p /\ forall p' l, S2.(step_ts) p l p' -> 
    exists q', (S1.(step_ts) q l q') /\ R q' p').

End TransitionSystem.

Module LabeledTransitionSystem.

Context {label L: Set}. 
 
(* Redefine Labeled Transition System to include silent labels *)
Inductive sl := 
| silentlabel.

Record LTS : Type := {
    st : Set ; 
    initial : st -> Prop ; 
    step : st -> st -> Prop ;
    l : st -> L + sl
  }.

(* the transitive reflexive closure of silent transitions *)
Inductive silentstar (lts : LTS) : lts.(st) -> lts.(st) -> Prop := 
| star_refl : forall (s : lts.(st)), silentstar lts s s
| star_trans : forall (s s' s'' : lts.(st)), lts.(step) s s' -> 
                lts.(l) s = inr silentlabel -> 
                silentstar lts s' s'' ->  silentstar lts s s''.

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

Theorem silentstar_trans : forall (lts : LTS) x y , 
  silentstar lts x y -> 
  forall z, silentstar lts y z -> 
  silentstar lts x z.
Proof.
  intros lts x y. intros H. intros z. induction H.
  + eauto.
  + intros. apply IHsilentstar in H2. eapply star_trans.
    eauto. eauto. eauto.
Qed.


(* Defining a weak simulation with traditional inital case. *)
Definition weakSimulation' (S1 S2 : LTS) (R: S1.(st) -> S2.(st) -> Prop) := 

(* initial case. The roots are related by R *)
(forall (s : S1.(st)), S1.(initial) s -> 
(exists (r : S2.(st)), S2.(initial) r /\ R s r /\ S1.(l) s = S2.(l) r)) /\ 

(* if there is a silent step in S1 then there exists some related silent step in S2 *)
( forall p q, R p q -> forall p', S1.(step) p p' /\ S1.(l) p = inr silentlabel  -> 
exists q', silentstar S2 q q' /\ R p' q') /\ 

(* if there is some labeled step in S1 then there exists some labeled transition in S2 that may include silent states *)
(forall p q, R p q -> forall p' a, S1.(step) p p' /\ S1.(l) p = inl a -> 
    exists q1 q2 q', silentstar S2 q q1 /\ S2.(step) q1 q2 /\ S2.(l) q1 = inl a /\ silentstar S2 q2 q' /\ R p' q').

(* use weak simulation as a partial order *)
Notation "x =w y" := (weakSimulation' x y) (at level 70).

(* typical weak simulation case is reflexive *)
Lemma  WS_refl' : forall x, exists r , (x =w x) r.
Proof.
    intros. exists eq. unfold "=w". intros; repeat split.
    + intros. exists s. intros. split; eauto.
    + intros. exists p'. split; eauto. destruct H0 as [H1 H2]. apply star_trans with (s' := p').
    ++ rewrite <- H; eauto.
    ++ rewrite <- H; eauto.
    ++ apply star_refl.
    + intros. exists p; exists p'; exists p'; repeat split.
    +++ rewrite H; apply star_refl.
    +++ inversion H0; eauto.
    +++ inversion H0; eauto.
    +++ apply star_refl.
Qed.   

Definition rel_dot n m p (x: n -> m -> Prop) (y: m -> p -> Prop): n -> p -> Prop :=
  fun i j => exists2 k, x i k & y k j.

(* typical weak simulation initial case is transitive  *)
Lemma  WS_trans' : forall (x y z : LTS),       
                    ( exists r1, (x =w y) r1 ) -> 
                    ( exists r2, (y =w z) r2 ) -> 
                      exists r3, (x =w z) r3.
Proof.
    intros x y z. intros Hxy Hyz. destruct Hxy as [Rxy Hxy].
    destruct Hyz as [Ryz Hyz]. exists (rel_dot Rxy Ryz).
    unfold weakSimulation'. repeat split.
    (* initial states are related by R *)
    + intros x' x_init. destruct Hxy as [Hxy Hxy_other].
      destruct Hyz as [Hyz Hyz_other]. 
      clear Hxy_other Hyz_other.
      specialize Hxy with x'. destruct Hxy as [y1 Hxy]. eauto.
      specialize Hyz with y1.
      destruct Hyz as [z1 Hyz]. destruct Hxy. eauto.
      exists z1. repeat split.
    ++ destruct Hyz; eauto.
    ++ unfold rel_dot. destruct Hxy as [Hxy1 Hxy2]. destruct Hxy2 as [Hxy2 Hxy3].
       destruct Hyz as [Hyz1 Hyz2]. destruct Hyz2 as [Hyz2 Hyz3].
       exists y1; eauto.
    ++ destruct Hxy as [Hxy1 Hxy2]. destruct Hxy2 as [Hxy2 Hxy3].
       destruct Hyz as [Hyz1 Hyz2]. destruct Hyz2 as [Hyz2 Hyz3].
       rewrite <- Hyz3. eauto.
    (* some silent step in S1 there must be a corresponding silent step in S2. *)
    + intros x1 z1 rel x2. intros. destruct Hxy as [Hxy_initial Hxy_other]. destruct Hxy_other as [Hxy_silent Hxy_ns].
      destruct Hyz as [Hyz_initial Hyz_other]. destruct Hyz_other as [Hyz_silent Hyz_ns]. 
Abort.   

(* Our definition of weak simulation. This is a one-way relation between two LTS.
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
    ( forall p q, R p q -> forall p', S1.(step) p p' /\ S1.(l) p = inr silentlabel  -> 
    exists q', silentstar S2 q q' /\ R p' q' /\ S1.(l) p' = S2.(l) q' ) /\ 
    
    (* if there is some labeled step in S1 then there exists some labeled transition in S2 that may include silent states *)
    (forall p q, R p q -> forall p' a, S1.(step) p p' /\ S1.(l) p = inl a -> 
     exists q1 q2 q', silentstar S2 q q1 /\ S2.(step) q1 q2 /\ S2.(l) q1 = inl a /\ silentstar S2 q2 q' /\ R p' q' /\ S1.(l) p' = S2.(l) q' ). 

(* use weak simulation as a partial order *)
Notation "x <= y" := (weakSimulation x y) (at level 70).

Lemma eqL_dec : forall a b : L, {a = b} + {a <> b }.
  intros.
Abort.

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
  + destruct (l lts s') as [b | ].
  (* case where s' is a label *)
  ++ assert (eqL_dec : {a = b} + {a <> b}). { repeat decide equality. }  
Admitted.

Lemma silentstar_stepfirst : forall LTS sil lab a,
  silentstar LTS sil lab ->
  LTS.(l) sil = inr silentlabel ->
  LTS.(l) lab = inl a ->
  (LTS.(step) sil lab) \/ (exists int, LTS.(step) sil int /\ LTS.(l) int = inr silentlabel /\ silentstar LTS int lab).
Proof. Admitted. 

Lemma silentstar_slientplus : forall LTS sil lab a,
  silentstar LTS sil lab ->
  LTS.(l) sil = inr silentlabel ->
  LTS.(l) lab = inl a ->
  silentplus LTS sil lab.
Proof. Admitted. 

Lemma silentplus_silentstar : forall LTS s s', 
  silentplus LTS s s' -> 
  silentstar LTS s s'.
Proof. Admitted.  

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
    +++ rewrite H. apply star_refl.
    +++ inversion H0; eauto.
    +++ inversion H0; eauto.
    +++ apply star_refl. 
Qed.   

Print eq.
(* Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x. *) 
Print transitivity.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Inductive relation_comp {A B C : Type} (R1 : A -> B -> Prop ) (R2 : B -> C -> Prop ) : A -> C -> Prop :=
| rc : forall a b c, R1 a b -> R2 b c -> relation_comp R1 R2 a c.

Definition R (X : Type) := X -> X -> Prop.

Theorem  WB_trans : forall (x y z : LTS),       
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
      + 
        
 
     Admitted. 

(* potentially we need to say more about the states. Maybe a finite set?? 
 * WB for LTS weighted over simirings: https://arxiv.org/pdf/1310.4106.pdf 
 * verification on infinite structures : 
   https://www.sciencedirect.com/science/article/abs/pii/B9780444828309500278 *)

(* need to define equal... and prove that it's an equivalence relation 
 * maybe isomorphism as equivalence ...?
 * Here: https://github.com/coq-contribs/ccs/blob/master/Trans_Sys.v 
 * different equivalence's are defined over transition systems  *)

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
