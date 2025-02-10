Require Import Coq.Lists.List.

(*************************
 ** ATTACK TREES
 **
 ** A record containing a set of events, a set
 ** of directed edges representing chronological
 ** time, and an event labeling function. *)


(** (ms C1 C2) denotes the measurement of 
 ** component C2 by component C1. *)
Inductive measLabel (comp : Type) : Type :=
| msp : comp -> comp -> measLabel comp
| ms : measLabel comp.


(** (cor C) and (rep C) denotes the corruption
 ** and repair respectively of component C. *)
Inductive advLabel (comp : Type) : Type :=
| cor : comp -> advLabel comp
| rep : comp -> advLabel comp.


Record attacktree (components : Type) : Type :=
{
  event : Type ;
  edges : list (event * event) ;
  label : event -> (measLabel components) + (advLabel components) ;

  eqDec_event :  forall (x y : event), {x = y} + {x <> y} ;
  eqDec_components : forall (x y : components), {x = y} + {x <> y}
}.


Section Notations.

    Context {components : Type}.
    Definition myEvent (A : attacktree components) := A.(event _).
    Definition myEdges (A : attacktree components) := A.(edges _).
    Definition myLabel (A : attacktree components) := A.(label _).
    Definition myEqDec_event (A : attacktree components) := A.(eqDec_event _).
    Definition myEqDec_components (A : attacktree components) := A.(eqDec_components _).

    Definition eventT (A : attacktree components) := A.(event _).
    Definition edgesT (A : attacktree components) := list (eventT A * eventT A).
    Definition labelT (A : attacktree components) := (eventT A) -> (measLabel components) + (advLabel components).

    Lemma myEqDec_labels : forall (A : attacktree components),
        forall (x y : (measLabel components) + (advLabel components)),
        {x = y} + {x <> y}.
    Proof.
        intros A x y. destruct x as [m|a], y as [m'|a'];
        try (right; intros contra; inversion contra; contradiction).
        - destruct m as [c1 c2|], m' as [c1' c2'|];
          try (right; intros contra; inversion contra; contradiction);
          try (destruct (myEqDec_components A c1 c1'), (myEqDec_components A c2 c2'); subst);
          try (right; intros contra; inversion contra; contradiction);
          left; auto.
        - destruct a as [c|c], a' as [c'|c'];
          try (right; intros contra; inversion contra; contradiction);
          destruct (myEqDec_components A c c'); subst;
          try (right; intros contra; inversion contra; contradiction);
          left; auto.
    Qed.
    
End Notations.