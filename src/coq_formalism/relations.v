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
    antisymmetric := forall a b : X, R a b -> R b a -> a = b;
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


(* here we play around with rewriting *)
Module RewritingPlayground. 
(* example taken from: 
 * https://rand.cs.uchicago.edu/vqc/Matrix.html#lab15*)

Require Import Psatz.
Require Import Setoid.
Require Import Arith.
Require Import Bool.
Require Import Program.

Definition Matrix (m n : nat) := nat -> nat -> Type.
Notation Vector n := (Matrix n 1).
Notation Square n := (Matrix n n).

Definition mat_equiv {m n : nat} (A B : Matrix m n) : Prop :=
  forall i j, i < m -> j < n -> A i j = B i j.

  Infix "==" := mat_equiv (at level 80). 

Lemma mat_equiv_refl : forall {m n} (A : Matrix m n), A == A.
Proof. intros m n A i j Hi Hj. reflexivity. Qed.
Lemma mat_equiv_sym : forall {m n} (A B : Matrix m n), A == B -> B == A.
Proof.
  intros m n A B H i j Hi Hj.
  rewrite H; easy.
Qed.
Lemma mat_equiv_trans : forall {m n} (A B C : Matrix m n),
    A == B -> B == C -> A == C.
Proof.
  intros m n A B C HAB HBC i j Hi Hj.
  rewrite HAB; trivial.
  apply HBC; easy.
Qed.

Add Parametric Relation m n : (Matrix m n) (@mat_equiv m n)
  reflexivity proved by mat_equiv_refl
  symmetry proved by mat_equiv_sym
  transitivity proved by mat_equiv_trans
    as mat_equiv_rel.

Lemma mat_equiv_trans2 : forall {m n} (A B C : Matrix m n),
A == B -> A == C -> B == C.
Proof.
  intros m n A B C HAB HAC.
  rewrite <- HAB.
  apply HAC.
Qed.

End RewritingPlayground.



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

End EnsemblePlayground. 





