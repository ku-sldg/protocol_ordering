(**************************
    EQUIVALENCE
 **************************)

 (* TODO: prove the isomorphism is an equivalence relation 
         - equivalence to only take into consideration states in the steps *)

Require Import Coq.Lists.List.
Require Import Order.attack_graph.
Require Import Order.reduce.
Require Import Order.strict_partial_order.

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
  
  Theorem isomorphism_refl : forall x, exists f , isomorphism x x f f.
  Proof.
    unfold isomorphism. intros. exists (fun x => x).
    split; simpl; eexists; eauto.
  Qed.

  Theorem isomorphism_sym : forall g1 g2, 
   exists f12 f21, (isomorphism g1 g2) f12 f21-> 
  (isomorphism g2 g1) f21 f12.
  Proof.
    intros. eexists. eexists. intros.
    inversion H. unfold isomorphism. split; eauto.
  Restart.
    intros. 
  Abort. 

  Theorem isomorphism_sym : forall g1 g2, 
  ( exists f12 f21, (isomorphism g1 g2) f12 f21 ) -> 
  ( exists g12 g21, (isomorphism g2 g1) g21 g12 ).
  Proof.
    intros. destruct H as [f12]. destruct H as [f21].
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

End Equivalence. 