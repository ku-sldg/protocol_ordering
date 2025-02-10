
(*************************
 ** EQUIVALENCE 
 ** OVER INDIVIDUAL ATTACK TREES 
 ** $\simeq$
 **
 ** Attack trees are equivalent if they 
 ** are isomorphic. *)

Require Import Coq.Lists.List.
Require Import Coq.Logic.Description.

Require Import Order.utilities.ltacs.
Require Import Order.utilities.lists.
Require Import Order.utilities.existsb.
Require Import Order.utilities.labelSubsets.

Require Import Order.attacktree.
Require Import Order.attacktree_normalization.


Set Implicit Arguments. 

Section AttackTreeEquivalence. 
    Context {components : Type}.


(** isomorphism
 ** 
 ** There exists a bijection between the events of 
 ** attack trees that preverves edges and labels. *)

    Definition injective {X Y : Type} (f : X -> Y) : Prop := 
        forall x1 x2, f x1 = f x2 -> x1 = x2.
    Definition surjective {X Y : Type} (f : X -> Y) : Prop := 
        forall y, exists x, f x = y.
    Definition bijective {X Y : Type} (f : X -> Y) : Prop := 
        injective f /\ surjective f.

    Definition edgePreserving {A B : attacktree components} (f : eventT A -> eventT B) : Prop := 
        forall ev1 ev2, In (ev1, ev2) (myEdges A) <-> In (f ev1, f ev2) (myEdges B).
    Definition labelPreserving {A B : attacktree components} (f : eventT A -> eventT B) : Prop :=
        forall ev, myLabel A ev = myLabel B (f ev).

    Definition isomorphic (A B : attacktree components) (f : eventT A -> eventT B) : Prop := 
        bijective f /\edgePreserving f /\ labelPreserving f.
    Definition isomorphism (A B : attacktree components)  : Prop :=
        exists f, isomorphic A B f.

    Hint Unfold bijective : core.
    Hint Unfold injective : core.
    Hint Unfold surjective : core.
    Hint Unfold edgePreserving : core.
    Hint Unfold labelPreserving : core.
    Hint Unfold isomorphic : core.
    Hint Unfold isomorphism : core.

    (** A function is bijective if and only if
     ** it is invertible. *)

    Definition leftInverse {X Y : Type} (f : X -> Y) g : Prop := 
        forall x, g (f x) = x.
    Definition rightInverse {X Y : Type} (f : X -> Y) g : Prop := 
        forall y, f (g y) = y.
    Definition inverse {X Y : Type} (f : X -> Y) g : Prop := 
        leftInverse f g /\ rightInverse f g.

    Lemma inverse_symmetric : forall X Y (f : X -> Y) g,
        inverse f g -> inverse g f.
    Proof.
        intros X Y f g HInv; destruct HInv as [HL HR]; split; auto.
    Qed.

    Lemma bijective_inverse : forall X Y (f : X -> Y),
        bijective f <-> exists g, inverse f g.
    Proof.
        intros X Y f; split.
        - intros HBij; destruct HBij as [HInj HSur].
          assert (HUniq : forall y, exists! x, f x = y).
          { intros y; destruct (HSur y);
            exists x; split; auto;
            intros x' H'; apply HInj;
            rewrite H'; auto. }
          assert (HSig : forall y, { x | f x  = y}).
          { intros y; apply constructive_definite_description; apply HUniq. }
          exists (fun y => proj1_sig ((HSig y))); split.
        -- intros x; destruct (HSig (f x)); auto.
        -- intros y; destruct (HSig y); auto.
        - intros HInv; destruct HInv as [g HInv]; destruct HInv as [HL HR];
          split.
        -- intros x1 x2 H; eapply f_equal with (f:=g) in H;
           repeat rewrite HL in H; auto.
        -- intros y; exists (g y); auto.
    Qed.


(** Isomophism is an equivalence relation. *)

    Theorem isomorphism_reflexive : forall A, 
        isomorphism A A.
    Proof.
      intros; exists (fun x => x); repeat split; eauto.
    Qed.
  
    Theorem isomorphism_symmetric : forall A B, 
    isomorphism A B -> 
    isomorphism B A.
    Proof.
        intros A B HIso; destruct_iso HIso.
        assert (HInv : exists g, inverse f g).
        { apply bijective_inverse; auto. }
        destruct HInv as [g HInv]; pose proof HInv as HInv';
        destruct HInv' as [HL HR].
        apply inverse_symmetric in HInv; assert (HBij : bijective g).
          { apply bijective_inverse; exists f; auto. }
        exists g; repeat split; intros. 
        - destruct HBij; auto.
        - destruct HBij; auto.
        - apply HEdg; repeat rewrite HR; auto.
        - apply HEdg in H; repeat rewrite HR in H; auto.
        - intros ev; rewrite HLab; rewrite HR; auto.
    Qed.
  
    Theorem isomorphism_transitive : forall A B C, 
    isomorphism A B -> 
    isomorphism B C ->
    isomorphism A C .
    Proof.
        intros A B C HAB HBC; destruct HAB as [fAB HAB]; destruct HBC as [fBC HBC];
        destruct HAB as [HBijAB HAB]; destruct HBijAB as [HInjAB HSurAB]; destruct HAB as [HEdgAB HLabAB];
        destruct HBC as [HBijBC HBC]; destruct HBijBC as [HInjBC HSurBC]; destruct HBC as [HEdgBC HLabBC];
        exists (fun x => fBC (fAB (x))); repeat split; intros.
        - autounfold; intros; apply HInjAB; apply HInjBC; auto.
        - unfold surjective in *; intros c; 
            specialize HSurBC with c; destruct HSurBC as [b HSurBC];
            specialize HSurAB with b; destruct HSurAB as [a HSurAB];
            exists a; rewrite HSurAB; rewrite HSurBC; auto.
        - apply HEdgBC; apply HEdgAB; auto.
        - apply HEdgBC in H; apply HEdgAB in H; auto.
        - autounfold; intros; rewrite HLabAB; rewrite HLabBC; auto.
    Qed.  

End AttackTreeEquivalence.

