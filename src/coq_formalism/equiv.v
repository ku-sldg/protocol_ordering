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

Print reducer.

(* injective = one-to-one*)
Definition injective `{g1 : attackgraph measurement corruption } `{g2: attackgraph measurement corruption} (f : g1.(state _ _) -> g2.(state _ _)) := forall x y, (f x = f y) -> x = y. 
(* surjective = onto *)
Definition surjective `{g1 : attackgraph measurement corruption } `{g2: attackgraph measurement corruption} (f : g1.(state _ _) -> g2.(state _ _)) := forall x, exists y,  x = f y. 
Definition bijective `{g1 : attackgraph measurement corruption } `{g2: attackgraph measurement corruption} (f : g1.(state _ _) -> g2.(state _ _)) := injective f /\ surjective f.

Lemma inverse {X Y : attackgraph measurement corruption} (f : (X.(state _ _)) -> (Y.(state _ _))) :
  bijective f -> {g : (Y.(state _ _)) -> (X.(state _ _)) | (forall x, g (f x) = x) /\
                               (forall y, f (g y) = y) }.
Proof.
intros [inj sur].
apply constructive_definite_description.
assert (H : forall y, exists! x, f x = y).
{ intros y.
  destruct (sur y) as [x xP].
  exists x; split; trivial. eauto.
  intros x' x'P.
  apply inj. rewrite <- xP. eauto. }
exists (fun y => proj1_sig (constructive_definite_description _ (H y))).
split.
- split.
  + intros x.
    destruct (constructive_definite_description _ _).
    simpl.
    now apply inj.
  + intros y.
    now destruct (constructive_definite_description _ _).
- intros g' [H1 H2].
  apply functional_extensionality.
  intros y.
  destruct (constructive_definite_description _ _) as [x e].
  simpl.
  now rewrite <- e, H1.
Qed.

Print existsb_ind.

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

  (************************
   RETRY WITH A DIFFERENT WAY
   TO DEFINE ISOMORPHISM 

   as motivated by 
   https://www.tildedave.com/2019/07/18/formalizing-lagranges-theorem-in-coq.html 
   ************************)

   Definition ListInjective' (A B: Type) (f: A -> B) (l: list A) :=
    (forall x y: A, In x l -> In y l -> f x = f y -> x = y).

   (* Definition ListInjective (g1 : attackgraph measurement corruption) (g2: attackgraph measurement corruption) (f : g1.(state _ _) -> g2.(state _ _)) (l :list (state measurement corruption g1 * state measurement corruption g1))  :=
    (forall x y, In x l -> In y l -> f x = f y -> x = y).*)
  
  Definition ListSurjective' (A B: Type) (f: A -> B) (l: list B) (l': list A) :=
    (forall x: B, In x l -> exists y, In y l' /\ f y = x).

  Definition ListSurjective (g1 : attackgraph measurement corruption) (g2: attackgraph measurement corruption) (f : g1.(state _ _) -> g2.(state _ _)) l l' :=
    (forall x, In x l -> exists y, In y l' /\ f y = x).

  Definition ListLabelPreserve (g1 : attackgraph measurement corruption) (g2: attackgraph measurement corruption) (f : g1.(state _ _) -> g2.(state _ _)) :=  
    (forall st1 st2, In (st1,st2) g1.(steps _ _) -> 
    g1.(label _ _) st1 = g2.(label _ _) (f st1) /\ g1.(label _ _) st2 = g2.(label _ _) (f st2)).
  
  Definition ListIsomorphism' (A B: Type) (f: A -> B) (l1: list A) (l2: list B) :=
    ListInjective' f l1 /\
    ListSurjective' f l2 l1 /\
    (forall d, In d l1 -> In (f d) l2).

  (* Definition ListIsomorphism (g1 : attackgraph measurement corruption) (g2: attackgraph measurement corruption) (f : g1.(state _ _) -> g2.(state _ _)) : Prop :=  (ListInjective g1 g2 f (g1.(steps _ _)) /\
                   ListSurjective g1 g2 f (g2.(steps _ _)) (g1.(steps _ _)) /\
                  (forall d, In d (g1.(steps _ _)) -> In (f d) (g2.(steps _ _))) /\ 
                  ListLabelPreserve g1 g2 f).

  Definition ListIsomorphismRefl : forall g1 l1, exists f, ListIsomorphism g1 g1 f l1 l1.
  Proof.
    intros. unfold ListIsomorphism.
    intros. exists (fun x => x). intuition.
    + unfold ListInjective. intros. eauto.
    + unfold ListSurjective. intros. exists x. split; eauto.
    + unfold ListLabelPreserve. intros.  
  Abort.      *)
    
  Definition isomorphism' (G1 : attackgraph measurement corruption) (G2: attackgraph measurement corruption) : Prop := 
  (exists (f : G1.(state _ _) -> G2.(state _ _)), homomorphism G1 G2 f /\ bijective f).

  Theorem isomorphism'_refl : forall g1, isomorphism' g1 g1.
  Proof.
    intros. unfold isomorphism'. exists (fun x => x).
    split.
    + simpl in *. unfold homomorphism. intros.  eauto. 
    + unfold bijective. unfold injective, surjective.
    split.
    ++ intros.  eauto.
    ++ intros. eexists; eauto.
  Qed.

  Theorem isomorphism'_sym : forall g1 g2, isomorphism' g1 g2 -> isomorphism' g2 g1.
  Proof.
    intros. unfold isomorphism' in *.
    destruct H as [fg1g2 H]. destruct H.
    pose proof (inverse H0). destruct X as [fg2g1 X]. destruct X as [ g1inv g2inv].
    exists fg2g1. split.
    + unfold bijective, homomorphism in *. intuition.
    ++ clear H2.  unfold injective, surjective in *. 
       assert (H' : surjective fg1g2). { eauto. }
       unfold surjective in H'.
       specialize H3 with st1. destruct H3 as [st1'].
       specialize H' with st2. destruct H' as [st2'].
       specialize H1 with st1' st2'.
       intuition. admit.
  Abort.   


  (************************
   FACTS ABOUT REDUCER 
   ************************)

  (* two graphs are equal if you first reduce then prove isomorphic 
   * reduce x to y 
   * reduce a to b 
   * prove the reduced form is also isomorphic *)
   Check step_update. 


  (* isomorphism of reduced graphs *) 
  Definition reducer_isomorphism_wrong 
  (G1 : attackgraph measurement corruption) (G2: attackgraph measurement corruption) 
  (y : list(G1.(state _ _) * G1.(state _ _))) (b : list(G2.(state _ _) * G2.(state _ _))) := 
  (reducer eqDec_state (G1.(steps _ _)) y /\ reducer eqDec_state (G2.(steps _ _)) b) -> isomorphism (step_update G1 y) (step_update G2 b).

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
  isomorphism (step_update G1 y) (step_update G2 b).

  Theorem reducer_isomorphism_refl : forall G1 b, reducer_isomorphism G1 G1 b b.
  Proof.
    intuition. 
    pose proof isomorphism_refl.
    unfold reducer_isomorphism.
    intros. specialize H with (step_update G1 b).
    inversion H.
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

