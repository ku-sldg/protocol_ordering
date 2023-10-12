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

(* Labels and States must have decidable equality 
Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
Hypothesis eqDec_corruption : forall (x y : corruption), {x = y} + {x <> y}.
Hypothesis eqDec_state : forall (G : attackgraph measurement corruption) (x y : G.(state _ _)), {x = y} + {x <> y}.*)


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

(* Definition isomorphism (G1 : attackgraph measurement corruption) (G2: attackgraph measurement corruption) (f : G1.(state _ _) -> G2.(state _ _))  (g : G2.(state _ _) -> G1.(state _ _))  : Prop := 
  homomorphism G1 G2 f /\ homomorphism G2 G1 g.*)

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
    intros. generalize dependent g1. destruct g2. induction steps.
    + intros. destruct g1. induction steps.
    ++ left. unfold isomorphism. unfold homomorphism. split.
    +++ eexists. split; intros.
    ++++ simpl in H. intuition.
    ++++ simpl in H. intuition.
    +++ eexists. split; intros; simpl in H; intuition.
    ++ right.         
  Abort.
  

  (* #[global]
  Add Relation _ (isomorphism) 
    reflexivity proved by isomorphism_refl
    symmetry proved by isomorphism_sym
    transitivity proved by isomorphism_trans
  as myeq.*)

  Instance iso_equiv : Equivalence isomorphism.
  Proof.
    constructor; auto with *.
    Abort.

  Print relation.

  Infix "==" := isomorphism (at level 80).
  
  Add Relation  _ (isomorphism)
    reflexivity proved by isomorphism_refl
    symmetry proved by isomorphism_sym
    transitivity proved by isomorphism_trans
  as myeq.

  (* another take on transitivity *)
  Lemma isomorphism_trans2 : forall a b c, a == b -> a == c -> b == c. 
  Proof.
    intros a b c Hab Hac.
    (* here rewrite works *)
    rewrite <- Hab.
    eauto.
  Qed.   
  
  Lemma isomorphism_trans2' : forall a b c, a == b -> b == c -> a == c. 
  Proof.
    intros a b c Hab Hac.
    (* here rewrite works *)
    rewrite <- Hac.
    eauto.
  Qed.   

  Instance iso_proper {x : (attackgraph measurement corruption)}: Proper (isomorphism ==> isomorphism) (fun x => x).
  Proof.
    intros.
    unfold Proper. unfold "==>". intros. eauto.
  Qed.     

  (* Generalized rewriting for the 
   * isomorphism relation... this is going
   * to be impossible  *)
  Lemma rewrite_help: forall a b,
  isomorphism a b -> a = b.
  Proof.
    intros a b Heq. eauto. unfold isomorphism in *. 
  Abort. 

  End Equivalence.

  (*******************************
   * Want to check equivalence of 
   * reduced graphs *)
  (******************)
  (* two graphs are equal if you first reduce then prove isomorphic 
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

