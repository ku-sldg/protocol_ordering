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

Context {label L: Set}.  

(* First, define Labeled Transition System
 * Given a set of states and labels, 
 * define a transition relation and initial state.
 * A label may either be a label or the silent label.  *)

Record LTS (state : Type) : Type := {
    initial : state;
    step : state -> label -> state -> Prop 
}.

Check LTS.
(* Check LTS.(step). *)

Definition relation (X : Type) := X -> X -> Prop.

(* bisimilarity relation for two states 
* type of this relation should be state -> state -> Prop *)
Definition BR_state {state} (sys : LTS state) (R: relation state) : Prop := 
    forall q p, R q p /\ forall l q', (sys.(step) q l q') -> 
    (exists p', (sys.(step) p l p') /\ R q' p').

(* simulation is one way *)
Definition simulation {state} (S1 S2 : LTS state) (R : relation state) : Prop := 
    forall q p, R q p /\ forall q' l, S1.(step) q l q' -> 
    exists p', (S2.(step) p l p') /\ R q' p'.

(* strong bisimulation is two way *)
Definition bisimulation {state1 state2} (S1: LTS state1) (S2: LTS state2) (R : state1 -> state2 -> Prop) : Prop := 
    R S1.(initial) S2.(initial) /\
    ( forall q p, R q p /\ forall q' l, S1.(step) q l q' -> 
    exists p', (S2.(step) p l p') /\ R q' p' ) /\
    ( forall q p, R q p /\ forall p' l, S2.(step) p l p' -> 
    exists q', (S1.(step) q l q') /\ R q' p').

 
(* Redefine Labeled Transition System to include silent labels *)

Inductive sl := 
| silentlabel.

Record LTS' : Type := {
    st : Set ; 
    initial' : st -> Prop ; 
    step' : st -> st -> Prop ;
    l : st -> L + sl
  }.

(* the transitive reflexive closure of silent transitions *)
Inductive silentstar (lts : LTS') : lts.(st) -> lts.(st) -> Prop := 
| star_refl : forall (s : lts.(st)), silentstar lts s s
| star_trans : forall (s s' s'' : lts.(st)), lts.(step') s s' -> 
                lts.(l) s = inr silentlabel -> 
                silentstar lts s' s'' ->  silentstar lts s s''.

(* Defining a weak simulation. This is a one-way relation between two LTS'.
 * There are three cases.  *)
Definition weakSimulation (S1 S2 : LTS') (R: S1.(st) -> S2.(st) -> Prop) := 

    (forall (s : S1.(st)), S1.(initial') s -> 
    (exists (r : S2.(st)), S2.(initial') r /\ R s r /\ S1.(l) s = S2.(l) r) \/ 
    (exists (r : S2.(st)), S2.(initial')r /\ R s r /\ S2.(l) r = inr silentlabel /\ 
    exists (r' : S2.(st)), (silentstar S2 r r' /\ S2.(l) r' = S1.(l) s )))
    
    
    /\ 

    (* if there is a silent step in S1 then there exists some related silent step in S2 *)
    ( forall p q, R p q -> forall p', S1.(step') p p' /\ S1.(l) p = inr silentlabel  -> 
    exists q', silentstar S2 q q' /\ R p' q') /\ 
    
    (* if there is some labeled step in S1 then there exists some labeled transition in S2 that may include silent states *)
    (forall p q, R p q -> forall p' a, S1.(step') p p' /\ S1.(l) p = inl a -> 
     exists q1 q2 q', silentstar S2 q q1 /\ S2.(step') q1 q2 /\ S2.(l) q1 = inl a /\ silentstar S2 q2 q' /\ R p' q'). 

(* use weak simulation as a partial order *)
Notation "x <= y" := (weakSimulation x y) (at level 70).

(* Prove that a weak simulation is reflexive *)
Lemma  WS_refl : forall x, exists r , (x <= x) r.
Proof.
    intros.
    (* exists r : st x -> st x -> Prop, *) 
    exists eq.  
    unfold weakSimulation. split.
    + intros. Admitted. (*  exists s; eauto.
    + split.
    ++ intros. exists p'. split; eauto.
    +++ apply star_trans with (s' := p'); try (rewrite <- H; destruct H0 as [H0 H1]; eauto). apply star_refl.
    ++ intros. exists p. exists p'. exists p'; repeat split.
    +++ rewrite H. apply star_refl.
    +++ inversion H0; eauto.
    +++ inversion H0; eauto.
    +++ apply star_refl.         
Qed. *)

Print eq.
(* Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x. *) 
Print transitivity.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Inductive clos_trans : LTS' -> LTS' -> Prop :=
| t_step (x y : LTS') r : (x <= y) r -> clos_trans x y
| t_trans ( x y z : LTS') : clos_trans x y -> clos_trans y z -> clos_trans x z.

Inductive relation_comp {A B C : Type} (R1 : A -> B -> Prop ) (R2 : B -> C -> Prop ) : A -> C -> Prop :=
| rc : forall a b c, R1 a b -> R2 b c -> relation_comp R1 R2 a c.

Definition R (X : Type) := X -> X -> Prop.

Definition rel_dot n m p (x: n -> m -> Prop) (y: m -> p -> Prop): n -> p -> Prop :=
  fun i j => exists2 k, x i k & y k j.

Lemma  WB_trans : forall (x y z : LTS'),       
                    ( exists r1, (x <= y) r1 ) -> 
                    ( exists r2, (y <= z) r2 ) -> 
                      exists r3, (x <= z) r3.
Proof. 
    intros.
    destruct H as [Rxy Hxy].
    destruct H0 as [Ryz Hyz].
    exists (relation_comp Rxy Ryz).
    destruct Hxy as [Hxy_initial Hxy].
    destruct Hxy as [Hxy_silent Hxy_ns].
    destruct Hyz as [Hyz_initial Hyz].
    destruct Hyz as [Hyz_silent Hyz_ns].
    split. 
    + clear Hxy_ns Hyz_ns Hxy_silent Hyz_silent. intros x' initial_x_x'. 
      specialize Hxy_initial with x'. 
    ++ destruct Hxy_initial.
    +++  eauto.
    +++ destruct H as [y' H].  specialize Hyz_initial with y'. destruct Hyz_initial.
    ++++ inversion H; eauto.
    ++++ destruct H0 as [z' H0]. left. exists z'; repeat split.
    +++++ destruct H0; eauto.
    +++++ apply rc with (b := y').
    ++++++ destruct H. destruct H1. eauto.
    ++++++ destruct H0. destruct H1. eauto.
    +++++ destruct H as [H H']. destruct H' as [H' H''].
        destruct H0 as [H0 H0']. destruct H0' as [H0' H0''].
        rewrite H''. eauto.
    ++++ destruct H0 as [z' H0]. right; exists z'; repeat split.
    +++++ destruct H0. eauto.
    +++++ apply rc with (b := y'). 
    ++++++ destruct H as [H H']. destruct H' as [H' H'']. eauto.
    ++++++ destruct H0 as [H0 H0']. destruct H0' as [H0' H0'']. eauto.
    +++++ destruct H0 as [H0 H0']. destruct H0' as [H0' H0''].
        destruct H0'' as [H0'' H0''']. eauto.
    +++++ destruct H0 as [H0 H0']. destruct H0' as [H0' H0''].
    destruct H0'' as [H0'' H0''']. destruct H0''' as [z'' H0'''].
    exists z''. split.
    ++++++ destruct H0'''. eauto.
    ++++++ destruct H0'''. rewrite H2. destruct H as [H H']. destruct H' as [H' H'']. eauto.
    +++ destruct H as [y' H].  specialize Hyz_initial with y'. destruct Hyz_initial. left. destruct H. exists z'; repeat split.
    +++ destruct H0; eauto.
    +++ apply rc with (b := y').
    ++++ destruct H. destruct H1. eauto.
    ++++ destruct H0. destruct H1. eauto.
    +++ destruct H as [H H']. destruct H' as [H' H''].
        destruct H0 as [H0 H0']. destruct H0' as [H0' H0''].
        rewrite H''. eauto.
    ++ destruct H0 as [z' H0]. right; exists z'; repeat split.
    +++ destruct H0. eauto.
    +++ apply rc with (b := y'). 
    ++++ destruct H as [H H']. destruct H' as [H' H'']. eauto.
    ++++ destruct H0 as [H0 H0']. destruct H0' as [H0' H0'']. eauto.
    +++ destruct H0 as [H0 H0']. destruct H0' as [H0' H0''].
        destruct H0'' as [H0'' H0''']. eauto.
    +++ destruct H0 as [H0 H0']. destruct H0' as [H0' H0''].
    destruct H0'' as [H0'' H0''']. destruct H0''' as [z'' H0'''].
    exists z''. split.
    ++++ destruct H0'''. eauto.
    ++++ destruct H0'''. rewrite H2. destruct H as [H H']. destruct H' as [H' H'']. eauto.
        eauto. eauto.     

    
    




    exists (relation_comp Rxy Ryz).
    destruct Hxy as [Hxy_initial Hxy].
    destruct Hxy as [Hxy_silent Hxy_ns].
    destruct Hyz as [Hyz_initial Hyz].
    destruct Hyz as [Hyz_silent Hyz_ns].
    split. 
    + clear Hxy_ns Hyz_ns Hxy_silent Hyz_silent.
      intros x' initial_x_x'. specialize Hxy_initial with x'. destruct Hxy_initial as [y' Hxy_initial]. eauto. 
      specialize Hyz_initial with y'.
      destruct Hxy_initial. destruct Hyz_initial.
      destruct H0.      


    exists transitivity.
    exists (fun x => gyz (fxy (x))).
    exists eq_trans.
    exists (transitive weakSimulation) .

    destruct Hxy as [Hxy_initial Hxy].
    destruct Hxy as [Hxy_slient Hxy_ns].
    destruct Hxy_initial.
 
     Admitted. 

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
