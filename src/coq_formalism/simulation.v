(******************************
    Looking into the following simulations relations 
    - Bisimulation 
    - Weak Bisimulation 
    - Branching Bisimulation 
    
    By: Anna Fritz
    Date: August 2, 2023 *)

    Set Implicit Arguments.


Inductive sl := 
| silentlabel.

(* First, define Labeled Transition System
 * Given a set of states and labels, 
 * define a transition relation and initial state.
 * A label may either be a label or the silent label.  *)

Record LTS (state label : Type) : Type := {
    initial : state -> Prop;
    step : state -> label + sl -> state -> Prop 
}.

Check LTS.
(* Check LTS.(step). *)

Definition relation (X : Type) := X -> X -> Prop.

(* bisimilarity relation for two states 
* type of this relation should be state -> state -> Prop *)
Definition BR_state {state label} (sys : LTS state label) (R: relation state) : Prop := 
    forall q p, R q p /\ forall l q', (sys.(step) q l q') -> 
    (exists p', (sys.(step) p l p') /\ R q' p').

(* simulation is one way *)
Definition simulation {state label} (S1 S2 : LTS state label) (R : relation state) : Prop := 
    forall q p, R q p /\ forall q' l, S1.(step) q l q' -> 
    exists p', (S2.(step) p l p') /\ R q' p'.

Definition bisimulation {state label} (S1 S2 : LTS state label) (R : relation state) : Prop := 
    ( forall q p, R q p /\ forall q' l, S1.(step) q l q' -> 
    exists p', (S2.(step) p l p') /\ R q' p' ) /\
    ( forall q p, R q p /\ forall p' l, S2.(step) p l p' -> 
    exists q', (S1.(step) q l q') /\ R q' p').



(* Define transitive reflexive closure *)
Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TrcRefl : forall x, trc R x x
| TrcTrans : forall x y z, R x y -> trc R y z -> trc R x z.

(* Might be useful to define reachable states *)
Inductive reachable {state label} (sys : LTS state label) (st : state) : Prop :=
| Reachable : forall st0, sys.(initial) st0 -> trc sys.(step) st0 st -> reachable sys st.
