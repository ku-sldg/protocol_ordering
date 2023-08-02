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
Require Import Coq.Logic.FinFun.
From mathcomp Require Import ssreflect.
From mathcomp Require Import fintype.
Check finType. 

Set Bullet Behavior "Strict Subproofs".

Require Import Coq.Logic.IndefiniteDescription.

(* should be automatically derivable for functions with finite domains *)
Definition im_dec {A} {B} (f : A -> B) := forall b, { a | f a = b } + ~(exists a, f a = b).
(* will have to prove if you give it an f *)

Definition im_dec'' : forall {A:finType} {B:finType} (f : A -> B) b, 
 { a | f a = b } + ~(exists a, f a = b).
Proof.
  intros. inversion A. inversion class. inversion choice_hasChoice_mixin.  unfold finType in *. 

Definition im_dec' : forall {A} {B} (f : A -> B) b, 
Finite A -> { a | f a = b } + ~(exists a, f a = b).
Proof.
  intros.
  unfold Finite in H.
  apply constructive_indefinite_description in H.
  inversion H.
  induction x.
  + right. unfold not. intros Hcontra.
    inversion Hcontra. unfold Full in H0.
    specialize H0 with x. inversion H0.
  + assert (adec : forall (a a0: A), {a = a0} + {a <> a0}). { admit. }
    apply IHx. unfold Full in *. intros.
    specialize adec with a a0. inversion adec.
  ++ inversion H.  inversion H0. inversion H. unfold Full in H1.  specialize H1 with a0. apply 

Module finite_homomorphism.
 
 Context {L : Set}.  
 
  (* could make L implicit since it exists in the context... maybe should optimize once finished *)
  Record graph : Type := {
    N : finType ; 
    E : N -> N -> Prop ;
    l : N -> L
  }.
  
(* Properties over the function *)


Print ssrfun.injective. 
(* ssrfun.injective = 
fun (rT aT : Type) (f : aT -> rT) =>
forall x1 x2 : aT, f x1 = f x2 -> x1 = x2
	 : forall rT aT : Type, (aT -> rT) -> Prop

Arguments ssrfun.injective [rT aT]%type_scope f%function_scope *)

Print ssrfun.cancel. 
(* ssrfun.cancel = 
fun (rT aT : Type) (f : aT -> rT) (g : rT -> aT) =>
forall x : aT, g (f x) = x
	 : forall rT aT : Type, (aT -> rT) -> (rT -> aT) -> Prop

Arguments ssrfun.cancel [rT aT]%type_scope (f g)%function_scope*)


Print ssrfun.bijective.
(* Variant bijective (A B : Type) (f : B -> A) : Prop :=
	Bijective : forall g : A -> B,
                ssrfun.cancel f g -> ssrfun.cancel g f -> ssrfun.bijective f.

Arguments ssrfun.bijective [A B]%type_scope f%function_scope
Arguments ssrfun.Bijective [A B]%type_scope [f g]%function_scope _ _*)

Print ssrfun.Bijective. 


Definition injective := ssrfun.injective. 

(* injective = one-to-one*)
Definition injective' `{G : graph} `{H: graph} (f : G.(N) -> H.(N)) := forall x y, (f x = f y) -> x = y. 
(* surjective = onto *)
Definition surjective `{G : graph} `{H: graph} (f : G.(N) -> H.(N)) := forall x, exists y,  x = f y. 
Definition bijective `{G : graph} `{H: graph} (f : G.(N) -> H.(N)) := injective _ _ f /\ surjective f.

Check bijective. 

(* preorder over graphs  *)
Definition homomorphism (G : graph) (H : graph) (f : G.(N) -> H.(N)) : Prop :=  
    forall v v', G.(E) v v' -> H.(E) (f v) (f v') /\
    forall n, G.(l) n = H.(l) (f n).

(* An isomorphism is a bijection that is also a homomorphism *)
Definition isomorphism (G : graph) (H : graph) (f : G.(N) -> H.(N)) : Prop := 
  surjective f /\ homomorphism G H f.

Notation "x <= y" := (homomorphism x y) (at level 70).
Notation "x = y" := (isomorphism x y) (at level 70).

Theorem isomorphism_refl : forall x, exists (f : N -> N), (x = x) f .
Proof.
  unfold isomorphism. intros.
  exists (fun x => x). split.
  - unfold surjective. intros. eexists; eauto.
  - unfold homomorphism; split.
  -- unfold injective. intros. eauto.
  -- intros; split; eauto.
Qed.  

(* looking at inverse because they did here: 
    https://coq.inria.fr/library/Coq.Logic.FinFun.html#Surjective_inverse 
    
   maybe a better way to go about it is like this? 
   https://gist.github.com/pedrominicz/0d9004b82713d9244b762eb250b9c808 
   
   *)

  Definition left_inverse `{G : graph} `{H : graph} (f: N -> N) g := forall a, g (f a) = a.

  Theorem left_inverse_injective : 
  forall `{G : graph} `{H : graph} f,
  (exists g, left_inverse f g) -> injective f.
  Proof.
    unfold injective, left_inverse.
    intros A B f [g H] a1 a2 eq.
    apply f_equal with (f := g) in eq.
    repeat rewrite H in eq.
    assumption.
  Qed. 

  Lemma surjective_inverse `{G : graph} `{H : graph} : 
    forall f, (surjective f) -> 
    exists g , forall x, f (g x) = x.
  Proof.
    intros f.  unfold surjective.
    intros. destruct G as [Ng Eg lg]. destruct H as [Nh Eh lh].
    (* here's where you need to say there exists some inverse *)
    exists f.
    intros.
    specialize H0 with x.
    inversion H0.   
  Abort. 

  Check invF.
  (* forall (T : finType) (f : T -> T),
       ssrfun.injective f -> eqtype.Equality.sort T -> T *)
  Check ssrfun.injective.


(* difficult proof *)
Theorem isomorphism_sym : forall x y, 
  ( exists (f : N -> N), (x = y) f ) -> 
  exists (g : N -> N), (y = x) g.
  Proof.
    intros.
    destruct H as [f H].
    (* inverting the isomorphsim  *)
    destruct H as [Hsur Hh].
    destruct Hh as [Hinj H].
    unfold injective, surjective in *.
    (* need to say there exists finverse *)
    destruct x as [xn xe xl].
    destruct y as [yn ye yl].
    destruct Hinj.
    destruct H as [Hedge Hlab]. 




    exists (fun x => y). 
  
Lemma isomorphism_trans : forall x y z, 
    ( exists (fxy: N-> N), (x h= y) fxy ) -> 
    ( exists (gyz: N-> N), (y h= z) gyz ) -> 
      exists (hxz: N-> N), (x h= z) hxz.
Proof. Admitted. 

(* Properties over homomorphisms. Would like to prove homomorphism is a partial order up to isomorphism  *)
Lemma  homomorphism_refl : forall x, exists (f : N -> N), (x <= x) f .
Proof.
    intros. unfold homomorphism. 
    exists (fun x => x). split; intros; eauto.
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
 
 