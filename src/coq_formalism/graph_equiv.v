(**************************
    ATTACK TREE EQUIVALENCE
    By: Anna Fritz and Sarah Johnson
    Date: Sept 10, 2023
 **************************)

 (* Prove an isomomorphism over
  * attack trees is an equivalence 
  * relation *)

Require Import Coq.Logic.Description.
Require Import Coq.Lists.List.
Require Import Order.utilities.
Require Import Order.attack_graph.
Require Import Order.graph_normalization.
Require Import Order.graph_strict_partial_order.

Set Implicit Arguments. 

Section Graph_Equivalence. 

(* We say two attack trees are equivalent if they are isomomorphic. 
 * We assume we are reasoning only over attack trees in their normal form *)

Context {measurement : Type}.
Context {adversary : Type}.

Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
Hypothesis eqDec_adversary : forall (x y : adversary), {x = y} + {x <> y}.
Hypothesis eqDec_event : forall (G : attackgraph measurement adversary) (x y : G.(event _ _)), {x = y} + {x <> y}.

Theorem in_dec_event : forall (G : attackgraph measurement adversary) (a : event measurement adversary G) (l : list (event measurement adversary G)), 
(forall (x y : event measurement adversary G),
{x = y} + {x <> y}) -> 
{In a l} + {~ In a l} .
Proof.
  pose proof In_dec. intros. induction l.
  + right. unfold not. intros. invc H.
  + specialize X0 with a a0. destruct X0.
  ++ subst. left. simp_int.
  ++ invc IHl.
  +++ left. auto with *.
  +++ right. unfold not. intros. invc H0.
  ++++ unfold not in n. apply n. eauto.
  ++++ contradiction.  
Qed.

Theorem in_dec_edges : forall (a : attackgraph measurement adversary) 
(a' : (event measurement adversary a * event measurement adversary a))
(l :list ((event measurement adversary a * event measurement adversary a))), 
(forall x y : (event measurement adversary a * event measurement adversary a),
{x = y} + {x <> y}) -> 
{In a' l} + {~ In a' l} .
Proof.
  intros. induction l.
  + right. unfold not. intros. invc H.
  + specialize X with a' a0. destruct X.
  ++ subst. left. auto with *.
  ++ invc IHl.
  +++ left. auto with *.
  +++ right. unfold not. intros. invc H0.
  ++++ apply n. eauto.
  ++++ contradiction.
Qed.            

Theorem  step_eq_dec : forall (a: attackgraph measurement adversary) (x y : event measurement adversary a * event measurement adversary a), {x = y} + {x <> y}.
Proof.
  intros. destruct x. destruct y.
  destruct (eqDec_event a e e1); subst.
  + destruct (eqDec_event a e0 e2); subst.
  ++ left. reflexivity.
  ++ right. unfold not. intros. inversion H.
     contradiction.
  + right. unfold not. intros. inversion H.
    contradiction.
Qed.       

Lemma list_eq_dec' : forall (a: attackgraph measurement adversary) 
(l l' :list (event measurement adversary a * event measurement adversary a)),
{l = l'} + {l <> l'}.
Proof.
  intros. 
  pose proof (list_eq_dec ). apply X.
  apply step_eq_dec.
Qed. 


(************************
 * DEFINING ISOMORPHISM 
 * event condition and 
 * label condition and
 * injective condition and
 * surjective condition *)
 Definition iso (g1 : attackgraph measurement adversary) (g2: attackgraph measurement adversary) (f : g1.(event _ _) -> g2.(event _ _)) : Prop :=  
    (forall st1 st2, In (st1,st2) g1.(edges _ _) <-> In ((f st1) ,(f st2)) g2.(edges _ _))    
    /\
    (forall st, g1.(label _ _) st = g2.(label _ _) (f st))
    /\
    (forall st1 st2, (f st1) = (f st2) -> st1 = st2)
    /\
    (forall st', exists st, (f st) = st').

Definition isomorphism (g1 : attackgraph measurement adversary) (g2: attackgraph measurement adversary) :=
    exists f, iso g1 g2 f.

(**************************
    First we need to show that 
    a function is bijective
    if and only if
    it is invertible *)

    Definition injection {X Y : Type} (f : X -> Y) := forall x1 x2, f x1 = f x2 -> x1 = x2.
    Definition surjection {X Y : Type} (f : X -> Y) := forall y, exists x, f x = y.
    Definition bijection {X Y : Type} (f : X -> Y) := injection f /\ surjection f.

    Definition left_inverse {X Y : Type} (f : X -> Y) g := forall x, g (f x) = x.
    Definition right_inverse {X Y : Type} (f : X -> Y) g := forall y, f (g y) = y.
    Definition inverse {X Y : Type} (f : X -> Y) g := left_inverse f g /\ right_inverse f g.

    Lemma inverse_sym : forall X Y (f : X -> Y) g,
        inverse f g -> inverse g f.
    Proof.
        intros X Y f g HInv. destruct HInv as [HL HR]. split.
        - intros x. apply HR.
        - intros y. apply HL.
    Qed.

    Lemma bijection_iff_inverse : forall X Y (f : X -> Y),
        bijection f <->
        exists g, inverse f g.
    Proof.
        intros X Y f. split.
        - intros HBij. destruct HBij as [HInj HSur].
          assert (HUniq : forall y, exists! x, f x = y).
          { intros y. destruct (HSur y). 
            exists x. split; auto.
            intros x' H'.
            apply HInj. rewrite H, H'. auto. }
          assert (HSig : forall y, { x | f x  = y}).
          { intros y. apply constructive_definite_description. apply HUniq. }
          exists (fun y => proj1_sig ((HSig y))).
          split.
        -- intros x. destruct (HSig (f x)); auto.
        -- intros y. destruct (HSig y); auto.
        - intros HInv. destruct HInv as [g HInv].
          destruct HInv as [HL HR].
          split.
        -- intros x1 x2 H. eapply f_equal with (f:=g) in H.
           repeat rewrite HL in H; auto.
        -- intros y. exists (g y). apply HR.
    Qed.



(****************************
  We want the isomorphism to be
  an equivalence relation.

  These are the properties:

    Class equivalence {X : Type} (R : relation X) := {
    reflexive := forall a : X, R a a ; 
    symmetric := forall a b : X, R a b -> R b a ;
    transitive := forall a b c: X, R a b -> R b c -> R a c 
    } . *)
    Theorem iso_refl : forall x, isomorphism x x.
    Proof.
      unfold isomorphism, iso. intros. exists (fun x => x). repeat split; eauto.
    Qed.
  
    Theorem iso_sym : forall g1 g2, 
    isomorphism g1 g2 -> 
    isomorphism g2 g1.
    Proof.
      unfold isomorphism. intros g1 g2 H. destruct H as [f H].
      destruct H as [HSt H]. destruct H as [HLab H]. destruct H as [HInj HSur].
      assert (HInv : exists g, inverse f g).
      { apply bijection_iff_inverse. unfold bijection, injection, surjection; auto. }
      destruct HInv as [g HInv]. exists g. repeat split; intros.
      - specialize HSt with (g st1) (g st2). apply HSt. 
        destruct HInv as [HL HR]. repeat rewrite HR. auto.
      - specialize HSt with (g st1) (g st2). apply HSt in H. 
        destruct HInv as [HL HR]. repeat rewrite HR in H. auto.
      - specialize HLab with (g st). rewrite HLab.
        destruct HInv as [HL HR]. rewrite HR. auto.
      - apply inverse_sym in HInv. assert (HBij : bijection g).
        { apply bijection_iff_inverse. exists f; auto. }
        destruct HBij as [HInj' HSur']. apply HInj'. auto.
      - apply inverse_sym in HInv. assert (HBij : bijection g).
        { apply bijection_iff_inverse. exists f; auto. }
        destruct HBij as [HInj' HSur']. apply HSur'.
    Qed.
  
    Theorem iso_trans : forall g1 g2 g3, 
    (isomorphism g1 g2) -> 
    (isomorphism g2 g3) ->
    (isomorphism g1 g3) .
    Proof.
      intros g1 g2 g3 H12 H23. destruct H12 as [f12 H12]. destruct H23 as [f23 H23].
      destruct H12 as [HSt12 H12]. destruct H12 as [HLab12 H12]. destruct H12 as [HInj12 HSur12].
      destruct H23 as [HSt23 H23]. destruct H23 as [HLab23 H23]. destruct H23 as [HInj23 HSur23].
      exists (fun x => f23 (f12 (x))). repeat split; intros.
      - apply HSt12 in H. apply HSt23 in H. auto.
      - apply HSt12. apply HSt23. auto.
      - rewrite HLab12. rewrite HLab23. auto.
      - apply HInj12. apply HInj23. auto.
      - specialize HSur23 with st'. destruct HSur23 as [st'' HSur23].
        specialize HSur12 with st''. destruct HSur12 as [st''' HSur12].
        rewrite <- HSur23. rewrite <- HSur12. exists st'''. auto.
    Qed. 
  
  
    Infix "==" := isomorphism (at level 80).
    
    Add Relation  _ (isomorphism)
      reflexivity proved by iso_refl
      symmetry proved by iso_sym
      transitivity proved by iso_trans
    as myeq.    

  End Graph_Equivalence.