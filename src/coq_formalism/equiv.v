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

Require Export Relation_Definitions.
Require Export Setoids.Setoid. 

Set Implicit Arguments. 

Section Equivalence. 

(* We aim to say two graphs are equivalent if thier reduced forms are isomorphic *)

Context {measurement : Type}.
Context {corruption : Type}.

(* Labels and States must have decidable equality *)
Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
Hypothesis eqDec_corruption : forall (x y : corruption), {x = y} + {x <> y}.
Hypothesis eqDec_state : forall (G : attackgraph measurement corruption) (x y : G.(state _ _)), {x = y} + {x <> y}.

Print reducer.

(* injective = one-to-one*)
Definition injective `{g1 : attackgraph measurement corruption } `{g2: attackgraph measurement corruption} (f : g1.(state _ _) -> g2.(state _ _)) := forall x y, (f x = f y) -> x = y. 
(* surjective = onto *)
Definition surjective `{g1 : attackgraph measurement corruption } `{g2: attackgraph measurement corruption} (f : g1.(state _ _) -> g2.(state _ _)) := forall x, exists y,  x = f y. 
Definition bijective `{g1 : attackgraph measurement corruption } `{g2: attackgraph measurement corruption} (f : g1.(state _ _) -> g2.(state _ _)) := injective f /\ surjective f.

Print existsb_ind.

Definition homomorphism (g1 : attackgraph measurement corruption) (g2: attackgraph measurement corruption) (f : g1.(state _ _) -> g2.(state _ _)) : Prop :=  
    forall st1 st2, In (st1,st2) g1.(steps _ _) -> In ((f st1) ,(f st2)) g2.(steps _ _)    
    /\
    forall st1 st2, In (st1,st2) g1.(steps _ _) -> 
        g1.(label _ _) st1 = g2.(label _ _) (f st1) /\ g1.(label _ _) st2 = g2.(label _ _) (f st2).

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
split.
+ (* step condition *)
  destruct (g1g2 st1 st2); eauto.
  clear H1.
  destruct (g2g3 (f12 st1) (f12 st2)); eauto.
+ (* label condition *)
  intros. destruct (g1g2 st0 st3); eauto.
  destruct (g2g3 (f12 st0) (f12 st3)); eauto.
  destruct (H2 st0 st3); eauto.
  destruct (H4 (f12 st0) (f12 st3)); eauto.
  split.
++ rewrite H5. rewrite H7; eauto.
++ rewrite H6. rewrite H8; eauto.
Qed. 

Definition isomorphism (G1 : attackgraph measurement corruption) (G2: attackgraph measurement corruption) (f : G1.(state _ _) -> G2.(state _ _))  (g : G2.(state _ _) -> G1.(state _ _))  : Prop := 
  homomorphism G1 G2 f /\ homomorphism G2 G1 g.

(****************************
  We want the isomorphism to be
  and equivlance relation.

  These are the properties:

    Class equivalence {X : Type} (R : relation X) := {
    reflexive := forall a : X, R a a ; 
    symmetric := forall a b : X, R a b -> R b a ;
    transitive := forall a b c: X, R a b -> R b c -> R a c 
    } . *)
  
  Theorem isomorphism_refl : forall x, exists f g, isomorphism x x f g.
  Proof.
    unfold isomorphism. intros. exists (fun x => x).
    exists (fun x => x).
    split; simpl; eexists; eauto.
  Qed.

  Theorem isomorphism_sym : forall g1 g2, 
  ( exists f12 f21, (isomorphism g1 g2) f12 f21 ) -> 
  ( exists g21 g12, (isomorphism g2 g1) g21 g12 ).
  Proof.
    intros. destruct H as [f21]. destruct H as [f12].
    exists f12. exists f21.
    destruct H.
    unfold isomorphism. split; eauto.
  Qed.

  Theorem isomorphism_trans : forall g1 g2 g3, 
  ( exists f12 f21, (isomorphism g1 g2) f12 f21 ) -> 
  ( exists g23 g32, (isomorphism g2 g3) g23 g32 ) ->
  ( exists h13 h31, (isomorphism g1 g3) h13 h31 ).
  Proof.
    intros. 
    destruct H as [f12]. destruct H as [f21].
    destruct H0 as [g23]. destruct H0 as [g32].
    inversion H. 
    inversion H0.
    unfold isomorphism.
    exists (fun x => g23 (f12 (x))).
    exists (fun x => f21 (g32 (x))).
    split; simpl.
    + clear H2. clear H4.  unfold homomorphism in *.
      split; eauto.
    ++ destruct (H1 st1 st2); eauto.
       destruct (H3 (f12 st1) (f12 st2)); eauto.
    ++ intros. destruct (H1 st0 st3); eauto.
       destruct (H3 (f12 st0) (f12 st3)); eauto.
       destruct (H6 st0 st3); eauto.
       destruct (H8 (f12 st0) (f12 st3)); eauto.
       split; intuition.
    +++ rewrite H9. rewrite H11. eauto.
    +++ rewrite H10. rewrite H12. eauto.
    + clear H1. clear H3.  unfold homomorphism in *.
      split; eauto.
    ++ destruct (H4 st1 st2); eauto.
      destruct (H2 (g32 st1) (g32 st2)); eauto.
    ++ intros. destruct (H4 st0 st3); eauto.
      destruct (H2 (g32 st0) (g32 st3)); eauto.
      destruct (H6 st0 st3); eauto.
      destruct (H8 (g32 st0) (g32 st3)); eauto.
      split; intuition.
    +++ rewrite H9. rewrite H11. eauto.
    +++ rewrite H10. rewrite H12. eauto.
  Qed.

  Definition myeq' := fun a b => exists f g, isomorphism a b f g.
  Check myeq'. 

  #[global]
  Add Relation _ (fun a b => exists f g, isomorphism a b f g) 
    reflexivity proved by isomorphism_refl
    symmetry proved by isomorphism_sym
    transitivity proved by isomorphism_trans
  as myeq.

  Lemma rewrite_help: forall a b, (exists
  (f : state measurement corruption a -> state measurement corruption b) (g : state measurement corruption b -> state measurement corruption a),
  isomorphism a b f g) -> a = b.
  Proof.
    intros.
    
  (* 
  #[global]
  Declare Instance Equivalence_eq : Equivalence ((fun a b => exists f g, isomorphism a b f g)). *)
  
  Print strict_partial_order.

  Print reducer. 

  (* two graphs are equal if you first reduce then prove isomorphic 
   * reduce x to y 
   * reduce a to b 
   * prove the reduced form is also isomorphic *)
   Check step_update. 


  (* isomorphism of reduced graphs *) 
  Definition reducer_isomorphism_wrong 
  (G1 : attackgraph measurement corruption) (G2: attackgraph measurement corruption) 
  (y : list(G1.(state _ _) * G1.(state _ _))) (b : list(G2.(state _ _) * G2.(state _ _))) := 
  (reducer eqDec_state (G1.(steps _ _)) y /\ reducer eqDec_state (G2.(steps _ _)) b) ->  forall f g, isomorphism (step_update G1 y) (step_update G2 b) f g.

  Print reducer_deterministic.

  Theorem reducer_isomorphism_refl : forall G1 b, reducer_isomorphism_wrong G1 G1 b b.
  Proof.
    intuition. 
    pose proof isomorphism_refl.
    unfold reducer_isomorphism_wrong.
    intros. 
  Abort.
  
  (* isomorphism of reduced graphs *) 
  Definition reducer_isomorphism
  (G1 : attackgraph measurement corruption) (G2: attackgraph measurement corruption) 
  (y : list(G1.(state _ _) * G1.(state _ _))) (b : list(G2.(state _ _) * G2.(state _ _))) := 
  (reducer eqDec_state (G1.(steps _ _)) y /\ reducer eqDec_state (G2.(steps _ _)) b) ->
  exists f g, isomorphism (step_update G1 y) (step_update G2 b) f g.

  Theorem reducer_isomorphism_refl : forall G1 b, reducer_isomorphism G1 G1 b b.
  Proof.
    intuition. 
    pose proof isomorphism_refl.
    unfold reducer_isomorphism.
    intros. specialize H with (step_update G1 b).
    inversion H.
  exists x. exists x. eauto.
  Abort. 
  
  Theorem reducer_isomorphism_sym : forall G1 G2 a b, reducer_isomorphism G1 G2 a b -> reducer_isomorphism G2 G1 b a.
  Proof.
  intuition. 
  pose proof isomorphism_sym.
  unfold reducer_isomorphism in *.
  intuition. Abort. (* 
  destruct H1 as [f_g1_g2 H1].
  destruct H1 as [f_g2_g1 H1].
  specialize H0 with (step_update G1 a) (step_update G2 b).
  destruct H0.
  + exists f_g1_g2. exists f_g2_g1. eauto.
  + destruct H.
  exists x0. exists x.
  eauto.
  Qed.*)
  
  Lemma reducer_iso_helper : forall G1 G3 a c, reducer eqDec_state (steps measurement corruption G1) a 
  /\  reducer eqDec_state (steps measurement corruption G3) c.
  Abort.
  
  Theorem reducer_isomorphism_trans : forall G1 G2 G3 a b c, (reducer_isomorphism G1 G2 a b /\ reducer_isomorphism G2 G3 b c) -> reducer_isomorphism G1 G3 a c.
  Proof.
    intuition.
    unfold reducer_isomorphism in *.
    intuition. simpl in *.
    (* we have nothing about the fact that G2 actually reduces to b *)
    (* I'm not sure how to solve this problem ... *)
  Abort. 

    
    

  (* TODO prove equiv over sets of graphs *)
  

End Equivalence. 