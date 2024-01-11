(**************************
    GRAPH EQUIVALENCE
    By: Anna Fritz and Sarah Johnson
    Date: Sept 10, 2023
 **************************)

 (* proved an bidirectional homomorphism between
  * attack graphs is an equivalence 
  * relation *)

Require Import Coq.Lists.List.
Require Import Order.utilities.
Require Import Order.attack_graph.
Require Import Order.graph_normalization.
Require Import Order.graph_strict_partial_order.

Set Implicit Arguments. 

Section Graph_Equivalence. 

(* We aim to say two graphs are equivalent if they are bidirectionally homomorphic. 
 * We assume we are reasoning over the reduced graph form *)

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
    
(************************
 * DEFINING BIDIRECTIONAL HOMOMORPHISM 
 * state condition and 
 * label condition *)
Definition bidir_homo (G1 : attackgraph measurement corruption) (G2: attackgraph measurement corruption) : Prop := 
  (exists (f : G1.(state _ _) -> G2.(state _ _)), homomorphism G1 G2 f) /\  
  (exists (g : G2.(state _ _) -> G1.(state _ _)), homomorphism G2 G1 g).


(****************************
  We want the bidir_homo to be
  and equivlance relation.

  These are the properties:

    Class equivalence {X : Type} (R : relation X) := {
    reflexive := forall a : X, R a a ; 
    symmetric := forall a b : X, R a b -> R b a ;
    transitive := forall a b c: X, R a b -> R b c -> R a c 
    } . *)
  
  Theorem bidir_homo_refl : forall x, bidir_homo x x .
  Proof.
    unfold bidir_homo. intros. split; exists (fun x => x); eexists; eauto.
  Qed.

  Theorem bidir_homo_sym : forall g1 g2, 
  bidir_homo g1 g2 -> 
  bidir_homo g2 g1.
  Proof.
    intros. destruct H as [H1 H2]. destruct H1 as [f12].
    destruct H2 as [f21]. unfold bidir_homo; split; eexists; eauto.
  Qed.

  Theorem bidir_homo_trans : forall g1 g2 g3, 
  (bidir_homo g1 g2) -> 
  (bidir_homo g2 g3) ->
  (bidir_homo g1 g3) .
  Proof.
    intros. destruct H. destruct H0.  
    unfold bidir_homo. split; pose proof homomorphism_trans as H3; eapply H3; eauto.
  Qed. 

  (* TODO *)
  Theorem bidir_homo_dec : forall g1 g2, {bidir_homo g1 g2} + {~ bidir_homo g1 g2}.
  Proof.
    intros. generalize dependent g1. unfold bidir_homo. destruct g2. induction steps.
    + intros. destruct g1. induction steps.
    ++ left. unfold bidir_homo. unfold homomorphism. split.
    +++ eexists. split; intros.
    ++++ simpl in H. intuition.
    ++++ simpl in H. intuition.
    +++ eexists. split; intros; simpl in H; intuition.
    ++ right.         
  Abort.

  Infix "==" := bidir_homo (at level 80).
  
  Add Relation  _ (bidir_homo)
    reflexivity proved by bidir_homo_refl
    symmetry proved by bidir_homo_sym
    transitivity proved by bidir_homo_trans
  as myeq.

  End Graph_Equivalence.