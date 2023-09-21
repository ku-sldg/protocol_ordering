(********* 
   Properties of various relations 
                        ***********)

Require Import Coq.Classes.RelationClasses.

Definition relation (X : Type) := X -> X -> Prop.

(* Preorder *)                        
Module Preorder. 

  Class preorder {X : Type} (R : relation X) := {
    reflexive := forall a : X, R a a ; 
    transitive := forall a b c: X, R a b -> R b c -> R a c 
  }.
    
End Preorder.

(* Strint Preorder*)
Module StrictPreorder.

  Class strictpreorder {X : Type} (R : relation X) := {
    irreflexive := forall a : X, ~ R a a ; 
    transitive := forall a b c: X, R a b -> R b c -> R a c 
  }.
    
End StrictPreorder.

(* Equivalence *)
Module Equivalence. 

  Class equivalence {X : Type} (R : relation X) := {
    reflexive := forall a : X, R a a ; 
    symmetric := forall a b : X, R a b -> R b a ;
    transitive := forall a b c: X, R a b -> R b c -> R a c 
  } . 

End Equivalence.

(* Partial Order *)
Module PartialOrder. 

  Class partial_order {X : Type} (R : relation X) := {
    reflexive := forall a : X, R a a ; 
    antisymmetric := forall a b : X, R a b -> R b a ;
    transitive := forall a b c: X, R a b -> R b c -> R a c 
  }. 

End PartialOrder. 

(* Strict Partial Order *)
Module StrictPartialOrder. 

  Class strict_partial_order {X : Type} (R : relation X) := {
    irreflexive := forall a : X, ~ R a a ; 
    asymmetric := forall a b : X, R a b -> ~ R b a ;
    transitive := forall a b c: X, R a b -> R b c -> R a c 
  }. 

End StrictPartialOrder. 

(* Building ordering operations *)
Module Order. 

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

(* Playing with Ensembles *)
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

From Coq Require Import Description.

Definition strange1: forall T:Type, 0>0 -> T.
  intros T H. 
  assert (exists! t:T, True) as H0. { inversion H. }
  apply constructive_definite_description in H0.
  destruct H0 as [x ?].
  exact x.
Defined.






