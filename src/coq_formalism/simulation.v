(******************************
    Looking into the following simulations relations 
    - Bisimulation 
    - Weak Bisimulation 
    - Branching Bisimulation 
    
    By: Anna Fritz
    Date: August 2, 2023 *)

Require Import Coq.Relations.Relation_Definitions.
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

 
(* Redefine Label transition system to include silent labels *)

Inductive sl := 
| silentlabel.

Record LTS' := {
    st : Set ; 
    inital : st -> Prop ; 
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
    (* inital condition. All start states in one graph must be present in the other. *)
    (forall (s : S1.(st)), S1.(inital) s -> 
    exists (r : S2.(st)), R s r /\ S1.(l) s = S2.(l) r) /\ 

    (* if there is a silent step in S1 then there exists some related silent step in S2 *)
    ( forall p q, R p q -> forall p', S1.(step') p p' /\ S1.(l) p = inr silentlabel  -> 
    exists q', silentstar S2 q q' /\ R p' q') /\ 
    
    (* if there is some labeled step in S1 then there exists some labeled transition in S2 that may include silent states *)
    (forall p q, R p q -> forall p' a, S1.(step') p p' /\ S1.(l) p = inl a -> 
     exists q1 q2 q', silentstar S2 q q1 /\ S2.(step') q1 q2 /\ S2.(l) q1 = inl a /\ silentstar S2 q2 q' /\ R p' q'). 

Notation "x <= y" := (weakSimulation x y) (at level 70).

(* Prove that a weak simulation is reflexive *)
Lemma  WS_refl : forall x, exists r , (x <= x) r.
Proof.
    intros. exists eq. 
    unfold weakSimulation. split.
    + intros. exists s; eauto.
    + split.
    ++ intros. exists p'. split; eauto.
    +++ apply star_trans with (s' := p'); try (rewrite <- H; destruct H0 as [H0 H1]; eauto). apply star_refl.
    ++ intros. exists p. exists p'. exists p'; repeat split.
    +++ rewrite H. apply star_refl.
    +++ inversion H0; eauto.
    +++ inversion H0; eauto.
    +++ apply star_refl.         
Qed. 

Lemma  WB_trans : forall x y z,       
                    ( exists r1, weakBisimulation x y r1 ) -> 
                    ( exists r2, weakBisimulation y z r2 ) -> 
                      exists r3, weakBisimulation x z r3.
Proof. Admitted. 

(* need to define equal... maybe isomorphism as equivalence ...? *)

Lemma WB_antisym : forall x y, 
                    ( exists r1, weakBisimulation x y r1 ) -> 
                    ( exists r2, weakBisimulation y x r2 ) -> 
                      x = y.






(* Define transitive reflexive closure *)
Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TrcRefl : forall x, trc R x x
| TrcTrans : forall x y z, R x y -> trc R y z -> trc R x z.

(* Might be useful to define reachable states *)
Inductive reachable {state} (sys : LTS state) (st : state) : Prop :=
| Reachable : forall st0, sys.(initial) st0 -> trc sys.(step) st0 _ st -> reachable sys st.
