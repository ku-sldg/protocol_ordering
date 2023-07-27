(**** Protocol Ordering using Labeled Graph Homomorphism 
      By: Anna Fritz 
      Date: July 27, 2023 
      
      Attempting to build off findings from Paul Rowe's paper, 
      "On Orderings in Security Models",
      to introduce an ordering over protocols  *)


(* Need to make the set of nodes of the graph finite to prove that the homomorphism is a partial order
 * (ie : reflexive : a <= a 
 *       antisymmetric : a <= b & b <= a -> a = b 
         transitive : a <= b & b <= c -> a <= c ) *)

(* As stated from Paul : 
 * If we only allow injective homomorphisms, then the preorder is actually a partial order (up to isomorphism) because injective homomorphisms in both directions between (finite) graphs G and H imply that G and H are isomorphic. *)

Require Import Coq.Classes.RelationClasses. 
From mathcomp Require Import ssreflect.
From mathcomp Require Import fintype.
Check finType.

Set Bullet Behavior "Strict Subproofs".

Module relations. 

  Print PreOrder. 

  Definition relation (X : Type) := X -> X -> Prop.

  (* equivalence is reflexive, symmetric, and transitive *)
  Class equivalence {X : Type} (R : relation X) := {
    reflexive := forall a : X, R a a ; 
    symmetric := forall a b : X, R a b -> R b a ;
    transitive := forall a b c: X, R a b -> R b c -> R a c 
  } . 

  (* preorder is reflexive and transitive *)
  Class preorder {X : Type} (R : relation X) := {
    reflexive' := forall a : X, R a a ; 
    transitive' := forall a b c: X, R a b -> R b c -> R a c 
  }.

  Class partial_order {X : Type} (R : relation X) := {
    reflexive'' := forall a : X, R a a ; 
    antisymmetric'' := forall a b : X, R a b -> R b a ;
    transitive'' := forall a b c: X, R a b -> R b c -> R a c 
  } . 
 
End relations. 

Module finite_homomorphism.
 
 Context {L : Set}.  
 
  (* could make L implicit since it exists in the context... maybe should optimize once finished *)
  Class graph := {
    N : finType ; 
    E : N -> N -> Prop ;
    l : N -> L
  }.
  
(* Properties over the function *)
Definition injective (G : graph) (H: graph) (f : G.(N) -> H.(N)) := forall x y : N, (f x = f y) -> x = y. 
Definition surjective (G : graph) (H: graph) (f : G.(N) -> H.(N)) := forall x, exists y,  x = f y. 
Definition bijective (G : graph) (H: graph) (f : G.(N) -> H.(N)) := injective G H f /\ surjective G H f. 

(* preorder over graphs  *)
Definition homomorphism (G : graph) (H : graph) (f : G.(N) -> H.(N)) : Prop := 
    injective G H f /\  
    forall v v', E v v' -> E (f v) (f v') /\
    forall n, l n = l (f n).

(* An isomorphism is a bijection that is also a homomorphism *)
Definition isomorphism (G : graph) (H : graph) (f : G.(N) -> H.(N)) : Prop := 
  surjective G H f /\ homomorphism G H f.

Notation "x <= y" := (homomorphism x y) (at level 70).
Notation "x h= y" := (isomorphism x y) (at level 70).

Theorem isomorphism_refl : forall x, exists (f : N -> N), (x h= x) f .
Proof.
  unfold isomorphism. intros.
  exists (fun x => x). split.
  - unfold surjective. intros. eexists; eauto.
  - unfold homomorphism; split.
  -- unfold injective. intros. eauto.
  -- intros; split; eauto.
Qed. 

Theorem inverse_is_isomorphism: .
Proof.
  
Qed.


Theorem isomorphism_sym : forall x y, 
  exists (f : N -> N), (x h= y) f -> 
  exists (g : N -> N), (y h= x) g.
  Proof. 
    intros. unfold isomorphism. unfold homomorphism.
    exists (fun x => y). 
  
Lemma isomorphism_trans : forall x y z, 
    ( exists (fxy: N-> N), (x h= y) fxy ) -> 
    ( exists (gyz: N-> N), (y h= z) gyz ) -> 
      exists (hxz: N-> N), (x h= z) hxz.
Proof. Admitted. 

(* Properties over homomorphisms. Would like to prove homomorphism is a partial order up to isomorphism  *)
Lemma  homomorphism_refl : forall x, exists (f : N -> N), (x <= x) f .
Proof.
    intros. unfold homomorphism. exists (fun x => x). split; intros; eauto.
    unfold injective.
    intros. eauto. 
Qed.   

Lemma  homomorphism_trans : forall x y z, 
    ( exists (fxy: N-> N), (x <= y) fxy ) -> 
    ( exists (gyz: N-> N), (y <= z) gyz ) -> 
    exists (hxz: N-> N), (x <= z) hxz.
Proof.
    intros x y z Hxy Hyz. 
    intros.
    destruct Hxy as [fxy xy]. destruct Hyz as [gyz yz].
    unfold homomorphism in *. 
    exists (fun x => gyz (fxy (x))).
    split.
    + inversion xy. inversion yz.
      unfold injective in *.
      intros. clear H0. clear H2.
      apply H. specialize H1 with (fxy x0) (fxy y0).
      apply H1. eauto.
    + intros v v'' H; split; destruct xy as [ H1 xy]; clear H1; destruct yz as [H2 yz]; clear H2.
    ++ specialize xy with v v''.
      destruct xy. eauto.
      specialize yz with (fxy v) (fxy v'').
      destruct yz. eauto.
      eauto.  
    ++ intros. 
      specialize xy with v v''.
      destruct xy. eauto.
      specialize H1 with n. rewrite H1. 
      specialize yz with (fxy v) (fxy v'').
      destruct yz. eauto.
      specialize H3 with (fxy n).
      rewrite H3.
      eauto.  
  Qed.   

Theorem isomorphism_is_equivlance :  .
Proof.
  
Qed.

      
Lemma homomorphism_antisym : forall x y, 
      ( exists f, (x <= y) f ) ->  
      ( exists g, (y <= x) g ) -> 
      exists h, (x h= y) h.
  Proof.
    unfold homomorphism. unfold isomorphism.
    intros.
    destruct H as [fxy H].
    destruct H as [fxy_inj H].
    destruct H0 as [gyx H0].
    destruct H0 as [gyx_inj H0].
    unfold surjective. unfold homomorphism.
    exists fxy. split.
    + clear H. clear H0.  unfold injective in *.
      intros y0.
      assert (Hinv : exists fxy_inv, (forall x, fxy_inv (fxy x) = x) /\ (forall y, fxy (fxy_inv y) = y) ).
      { 

      }
      remember (gyx x0) as y0. exists y0. subst.
      specialize fxy_inj with b (gyx b).   

    eauto.
    split.
    split.

    destruct fxy_inj.
    destruct H as [fxy_edge fxy_lab].  
    
        
(* TO DOs:  Prove supports and covers are a preorder *)
 
 