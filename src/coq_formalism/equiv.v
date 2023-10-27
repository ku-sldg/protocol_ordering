(**************************
    EQUIVALENCE
 **************************)

 (* proved an isomorphism between
  * attack graphs is an equivalence 
  * relation *)

Require Import Coq.Lists.List.
Require Import Order.utilities.
Require Import Order.attack_graph.
Require Import Order.reduce.
Require Import Order.strict_partial_order.

(* Require Export Relation_Definitions.*)
Require Import Setoid. 
Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Basics. 
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Description.

Set Implicit Arguments. 

Section Equivalence. 

(* We aim to say two graphs are equivalent if thier reduced forms are isomorphic *)

Context {measurement : Type}.
Context {corruption : Type}.

(* Labels and States must have decidable equality *)
Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
Hypothesis eqDec_corruption : forall (x y : corruption), {x = y} + {x <> y}.
Hypothesis eqDec_state : forall (G : attackgraph measurement corruption) (x y : G.(state _ _)), {x = y} + {x <> y}.


(************************
 * DEFINING HOMOMORPHISM 
 * state condition and 
 * label condition *)
Definition homomorphism (g1 : attackgraph measurement corruption) (g2: attackgraph measurement corruption) (f : g1.(state _ _) -> g2.(state _ _)) : Prop :=  
    (forall st1 st2, In (st1,st2) g1.(steps _ _) -> In ((f st1) ,(f st2)) g2.(steps _ _))    
    /\
    (forall st1 st2, In (st1,st2) g1.(steps _ _) -> 
        g1.(label _ _) st1 = g2.(label _ _) (f st1) /\ g1.(label _ _) st2 = g2.(label _ _) (f st2)).

(* might be helpful to prove homomorphism is reflexive and transitive *)

Lemma homomorphism_refl : forall g1, exists (f : g1.(state _ _) -> g1.(state _ _)), homomorphism g1 g1 f.
Proof.
    intros.
    unfold homomorphism.
    exists (fun g1 => g1). split; intros; eauto.
Qed.

Lemma  homomorphism_trans : forall g1 g2 g3, 
    ( exists f12, (homomorphism g1 g2) f12 ) -> 
    ( exists g23, (homomorphism g2 g3) g23 ) -> 
    exists h13, (homomorphism g1 g3) h13.
Proof.
intros g1 g2 g3 f12 g23. 
destruct f12 as [f12 g1g2]. 
destruct g23 as [g23 g2g3].
unfold homomorphism in *. 
exists (fun x => g23 (f12 (x))).
split; intros.
+ (* step condition *)
  intuition.
+ (* label condition *)
  intuition.
++ specialize H1 with st1 st2. intuition.
   specialize H0 with st1 st2. intuition.
   specialize H2 with (f12 st1) (f12 st2); intuition.
   specialize H3 with (f12 st1) (f12 st2); intuition.
   rewrite  H1. eauto.
++specialize H1 with st1 st2. intuition.
specialize H0 with st1 st2. intuition.
specialize H2 with (f12 st1) (f12 st2); intuition.
specialize H3 with (f12 st1) (f12 st2); intuition.
rewrite  H5. eauto.
Qed. 

Print In_dec. 

Theorem in_dec_state : forall (G : attackgraph measurement corruption) (a : state measurement corruption G) (l : list (state measurement corruption G)), 
(forall (x y : state measurement corruption G),
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

Theorem in_dec_steps : forall (a : attackgraph measurement corruption) 
(a' : (state measurement corruption a * state measurement corruption a))
(l :list ((state measurement corruption a * state measurement corruption a))), 
(forall x y : (state measurement corruption a * state measurement corruption a),
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

Print list_eq_dec. 

Theorem  step_eq_dec : forall (a: attackgraph measurement corruption) (x y : state measurement corruption a * state measurement corruption a), {x = y} + {x <> y}.
Proof.
  intros. destruct x. destruct y.
  destruct (eqDec_state a s s1); subst.
  + destruct (eqDec_state a s0 s2); subst.
  ++ left. reflexivity.
  ++ right. unfold not. intros. inversion H.
     contradiction.
  + right. unfold not. intros. inversion H.
    contradiction.
Qed.       

Lemma list_eq_dec' : forall (a: attackgraph measurement corruption) 
(l l' :list (state measurement corruption a * state measurement corruption a)),
{l = l'} + {l <> l'}.
Proof.
  intros. 
  pose proof (list_eq_dec ). apply X.
  apply step_eq_dec.
Qed. 

(* TODO *)
Theorem homomorphism_dec : forall g1 g2, {exists f, homomorphism g1 g2 f} + {~ exists f, homomorphism g1 g2 f}.
Proof.
  intros. unfold homomorphism. 
  pose proof in_dec_steps g1 as in_g1.  
  pose proof in_dec_steps g2 as in_g2. 
  pose proof step_eq_dec g2 as step_dec_g2.
  pose proof step_eq_dec g1 as step_dec_g1.
  destruct g1 as [g1_state g1_steps g1_lab]. 
  destruct g2 as [g2_state g2_steps g2_lab].
  simpl in *.  
  induction g2_steps.
  (* g2 steps is nil *)
  + simpl. destruct g1_steps eqn:H'.
  (* g1 steps also nil *)
  ++ simpl. left. eexists. split. intros. invc H.
     intros. invc H.
  (* g2 nil and g1 not nil *)
  ++ simpl in *. right. unfold not. intros. invc H. invc H0. subst. destruct p.
     specialize H with g g0. intuition.
  (* g2 steps not nil *)
  +  destruct IHg2_steps.
  ++ left. destruct e. exists x. destruct H. 
     split; intros; auto with *.
  ++ unfold not in n. exfalso. apply n. eexists. split; intros. 
  +++ 
  Restart.
  pose proof (In_dec) as In_dec.
Abort.           


Definition isomorphism (G1 : attackgraph measurement corruption) (G2: attackgraph measurement corruption) : Prop := 
  (exists (f : G1.(state _ _) -> G2.(state _ _)), homomorphism G1 G2 f) /\  
  (exists (g : G2.(state _ _) -> G1.(state _ _)), homomorphism G2 G1 g).


(****************************
  We want the isomorphism to be
  and equivlance relation.

  These are the properties:

    Class equivalence {X : Type} (R : relation X) := {
    reflexive := forall a : X, R a a ; 
    symmetric := forall a b : X, R a b -> R b a ;
    transitive := forall a b c: X, R a b -> R b c -> R a c 
    } . *)
  
  Theorem isomorphism_refl : forall x, isomorphism x x .
  Proof.
    unfold isomorphism. intros. split; exists (fun x => x); eexists; eauto.
  Qed.

  Theorem isomorphism_sym : forall g1 g2, 
  isomorphism g1 g2 -> 
  isomorphism g2 g1.
  Proof.
    intros. destruct H as [H1 H2]. destruct H1 as [f12].
    destruct H2 as [f21]. unfold isomorphism; split; eexists; eauto.
  Qed.

  Theorem isomorphism_trans : forall g1 g2 g3, 
  (isomorphism g1 g2) -> 
  (isomorphism g2 g3) ->
  (isomorphism g1 g3) .
  Proof.
    intros. destruct H. destruct H0.  
    unfold isomorphism. split; pose proof homomorphism_trans as H3; eapply H3; eauto.
  Qed. 

  (* TODO *)
  Theorem isomorphism_dec : forall g1 g2, {isomorphism g1 g2} + {~ isomorphism g1 g2}.
  Proof.
    intros. generalize dependent g1. unfold isomorphism. destruct g2. induction steps.
    + intros. destruct g1. induction steps.
    ++ left. unfold isomorphism. unfold homomorphism. split.
    +++ eexists. split; intros.
    ++++ simpl in H. intuition.
    ++++ simpl in H. intuition.
    +++ eexists. split; intros; simpl in H; intuition.
    ++ right.         
  Abort.

  Infix "==" := isomorphism (at level 80).
  
  Add Relation  _ (isomorphism)
    reflexivity proved by isomorphism_refl
    symmetry proved by isomorphism_sym
    transitivity proved by isomorphism_trans
  as myeq.

  End Equivalence.

  (*******************************
   * Want to check equivalence of 
   * reduced graphs *)
  (******************)
  (* TODO two graphs are equal if you first reduce then prove isomorphic 
   * reduce x to y 
   * reduce a to b 
   * prove the reduced form is also isomorphic *)

Section Reducer_Equivalence. 

  Import Equivalence.

  Context {measurement : Type}.
  Context {corruption : Type}.
  Context {G1 : attackgraph measurement corruption}.
  Context {G2 : attackgraph measurement corruption}.

  (* Labels and States must have decidable equality *)
  Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
  Hypothesis eqDec_corruption : forall (x y : corruption), {x = y} + {x <> y}.
  Hypothesis eqDec_state1 : forall (x y : G1.(state _ _)), {x = y} + {x <> y}.
  Hypothesis eqDec_state2 : forall (x y : G2.(state _ _)), {x = y} + {x <> y}.
  
  Print reducer.
  
  (* isomorphism of reduced graphs *) 
  Definition reducer_isomorphism (y : list(G1.(state _ _) * G1.(state _ _))) 
                                 (b : list(G2.(state _ _) * G2.(state _ _))) := 
  ((reducer eqDec_state1 (G1.(steps _ _)) y) /\ reducer eqDec_state2 (G2.(steps _ _)) b) ->
  isomorphism (step_update G1 y) (step_update G2 b).

  (* want to prove this is also an equivalence relation *)
  (* Theorem reducer_isomorphism_refl : forall b z, reducer_isomorphism b b.
  Proof.
    intuition. 
  Abort.
  
  Theorem reducer_isomorphism_sym : forall a b, reducer_isomorphism a b -> reducer_isomorphism b a.
  Proof.
  Abort. 
  
  
  Theorem reducer_isomorphism_trans : forall G1 G2 G3 a b c, (reducer_isomorphism G1 G2 a b /\ reducer_isomorphism G2 G3 b c) -> reducer_isomorphism G1 G3 a c.
  Proof.
    intuition.
    unfold reducer_isomorphism in *.
    intuition. simpl in *.
    (* we have nothing about the fact that G2 actually reduces to b *)
    (* I'm not sure how to solve this problem ... *)
  Abort. *) 

End Reducer_Equivalence.

