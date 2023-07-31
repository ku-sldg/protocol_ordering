(********* 
   Properties of binary relations 
                        ***********)

Require Import Coq.Classes.RelationClasses.

Definition relation (X : Type) := X -> X -> Prop.

(* Preorder defined using `Definition` *)                        
Module Preorder. 

  (* preorder is reflexive and transitive *)
  Class preorder {X : Type} (R : relation X) := {
    reflexive := forall a : X, R a a ; 
    transitive := forall a b c: X, R a b -> R b c -> R a c 
  }.
    
End Preorder.

Module Equivalence. 

  (* equivalence is reflexive, symmetric, and transitive *)
  Class equivalence {X : Type} (R : relation X) := {
    reflexive := forall a : X, R a a ; 
    symmetric := forall a b : X, R a b -> R b a ;
    transitive := forall a b c: X, R a b -> R b c -> R a c 
  } . 

End Equivalence.

(* A Partial order is reflexive, antisymmetric, and transitive. *)
Module PartialOrder. 

  Class partial_order {X : Type} (R : relation X) := {
    reflexive := forall a : X, R a a ; 
    antisymmetric := forall a b : X, R a b -> R b a ;
    transitive := forall a b c: X, R a b -> R b c -> R a c 
  }. 

End PartialOrder. 

(* Order (le) defined using class system *)
Section Order. 

Class Eqc A := {
    eqb : A -> A -> bool; 
}.

Class Ord A `{Eqc A} : Type := {
    le : A -> A -> bool
}.

Definition max {A : Type} `{Eqc A} `{Ord A} (x y : A) : A := 
    if le x y then y else x.

(* if Eqc constraint is left out of the definition then max' still type checks because the ord class inherits from the eq class *)
Definition max' {A : Type} `{Ord A} (x y : A) : A := 
    if le x y then y else x.

Class Ord' A `{Eqc A} : Type := {
    le' : A -> A -> bool; 
    gt' : A -> A -> bool
}.

(* you can just call one member of the class *)
Definition max'' {A : Type} `{Ord' A} (x y : A) : A := 
    if le' x y then y else x.

End Order.

Section Order'.

Context {A : Type}. 

(* Interesting... Names exist outside the sections *)
Class Eqc' := {
    eqb' : A -> A -> bool; 
}.

End Order'.

Require Import Coq.Sets.Ensembles. 

    Section EnsemblePlayground.

    Definition H := Ensemble nat. 
    Definition one : H := Singleton _ 1.
    Definition two : H := Add _ one 2.

    (* say one is a subset of two *)
    Lemma incl : Included _ one two.
    Proof.
        unfold Included. intros.
        unfold two. unfold one in H0.
        unfold one. unfold Add. unfold In.
        apply Union_introl. apply H0.
    Qed.

End EnsemblePlayground.






