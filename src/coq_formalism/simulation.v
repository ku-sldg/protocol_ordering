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
 * define a transition relation and initial state.
 * A label may either be a label or the silent label.  *)

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

Lemma  WS_trans' : forall (x y z : LTS),       
                    ( exists r1, (x =w y) r1 ) -> 
                    ( exists r2, (y =w z) r2 ) -> 
                      exists r3, (x =w z) r3.
Proof.
    intros x y z. intros Hxy Hyz. destruct Hxy as [Rxy Hxy].
    destruct Hyz as [Ryz Hyz]. exists (rel_dot Rxy Ryz).
    unfold weakSimulation'. repeat split.
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
    + admit.
    + admit.
Admitted.   

(* Defining a weak simulation. This is a one-way relation between two LTS.
 * There are three cases.  *)
Definition weakSimulation (S1 S2 : LTS) (R: S1.(st) -> S2.(st) -> Prop) := 

    (* initial case *)
    (forall (s : S1.(st)), S1.(initial) s -> 
    (exists (r : S2.(st)), S2.(initial) r /\ R s r /\ S1.(l) s = S2.(l) r) \/ 
    (exists (r : S2.(st)), S2.(initial) r /\ R s r /\ S2.(l) r = inr silentlabel /\ 
     exists (r' : S2.(st)), (silentstar S2 r r' /\ S2.(l) r' = S1.(l) s ))) 
    /\ 

    (* if there is a silent step in S1 then there exists some related silent step in S2 *)
    ( forall p q, R p q -> forall p', S1.(step) p p' /\ S1.(l) p = inr silentlabel  -> 
    exists q', silentstar S2 q q' /\ R p' q') /\ 
    
    (* if there is some labeled step in S1 then there exists some labeled transition in S2 that may include silent states *)
    (forall p q, R p q -> forall p' a, S1.(step) p p' /\ S1.(l) p = inl a -> 
     exists q1 q2 q', silentstar S2 q q1 /\ S2.(step) q1 q2 /\ S2.(l) q1 = inl a /\ silentstar S2 q2 q' /\ R p' q'). 

(* use weak simulation as a partial order *)
Notation "x <= y" := (weakSimulation x y) (at level 70).

(* Prove that a weak simulation is reflexive *)
Lemma  WS_refl : forall x, exists r , (x <= x) r.
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

Definition rel_dot n m p (x: n -> m -> Prop) (y: m -> p -> Prop): n -> p -> Prop :=
  fun i j => exists2 k, x i k & y k j.

Lemma  WB_trans : forall (x y z : LTS),       
                    ( exists r1, (x <= y) r1 ) -> 
                    ( exists r2, (y <= z) r2 ) -> 
                      exists r3, (x <= z) r3.
Proof. 
    intros.
    destruct H as [Rxy Hxy].
    destruct H0 as [Ryz Hyz].
    exists (rel_dot Rxy Ryz).
    destruct Hxy as [Hxy_initial Hxy].
    destruct Hxy as [Hxy_silent Hxy_ns].
    destruct Hyz as [Hyz_initial Hyz].
    destruct Hyz as [Hyz_silent Hyz_ns].
    unfold weakSimulation. 
    repeat split. 
    + (* initial case *)
      intros x' initial_x_x'. 
      specialize Hxy_initial with x'. destruct Hxy_initial; eauto;
      destruct H as [y' H];  specialize Hyz_initial with y'; destruct Hyz_initial;
      destruct H; eauto; destruct H1 as [H1 H2];
      destruct H0 as [z' H3]; destruct H3 as [H3 H4]; destruct H4 as [H4 H5].
    (* initial y y' , Rxy x' y' , l x x' = l y y'
       initial z z' , Ryz y' z' , l y y' = l z z' *)
    ++ left. exists z'; repeat split; eauto.
    +++ unfold rel_dot. exists y'; eauto.
    +++ rewrite H2. eauto.
    (* now... z' is a silent label 
       l z z' = inr silentlabel /\
       (exists r' : st z, silentstar z z' r' /\ l z r' = l y y') *)
    ++ right. exists z'; repeat split; eauto.
    +++ unfold rel_dot. exists y'; eauto. 
    +++ destruct H5 as [H5 H6]; eauto.
    +++ destruct H5 as [H5 H6]; eauto.
        destruct H6 as [z'' H6].
        destruct H6 as [H6 H7].
        exists z''; split; eauto. rewrite H7. eauto.
    (* here is where we struggle. 
       now... y' is a silent label 
       l y y' = inr silentlabel /\
       (exists r' : st y, silentstar y y' r' /\ l y r' = l x x')
    *)
    ++ admit. (*  destruct H2. destruct H2 as [y'' H2]. destruct H2.
       right. exists z'. repeat split; eauto.
    +++ unfold rel_dot. exists y'; eauto.
    +++ rewrite <- H5. eauto.
    +++ induction H2. 
    ++++ exists z'; split.
    +++++ apply star_refl.
    +++++ rewrite <- H5. eauto.
    ++++ apply Hyz_silent with (p' := s') in H4; try (split; eauto).
         destruct H4 as [z'' H4]. destruct H4 as [H4 H9]. 
         exists z''; split.
    +++++ eauto.
    +++++ clear H0.  rewrite <- H6. clear H6.
          destruct (l y s') as [a|].
    ++++++ apply Hyz_ns with (p' := s'') (a := a) in H9; try (split; eauto).
    +++++++ destruct H9. destruct H0. destruct H0. destruct H0.
          destruct H6. destruct H10.
          destruct H4. subst.   destruct H9.   
         apply IHsilentstar. inversion H0. *)
    (* now z' and y' are silent labels 
       l z z' = inr silentlabel /\
       (exists r' : st z, silentstar z z' r' /\ l z r' = l y y')
       l y y' = inr silentlabel /\
       (exists r' : st y, silentstar y y' r' /\ l y r' = l x x')
    *)
    ++ right. 
        
 
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

(* check out: Algorithms for Computing Weak Bisimulation Equivalence for algorithms in practice *)
