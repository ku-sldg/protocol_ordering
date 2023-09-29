(**** Labeled Graph Homomorphism 
      By: Anna Fritz 
      Date: July 18, 2023 
      
      Defining supports and covers and other interesting 
      properties taken from Paul Rowe's paper: 
      "On Orderings in Security Models" *)

Require Import Coq.Lists.List.

Require Import Order.attack_graph.
Require Import Order.strict_partial_order.
Require Import Order.reduce.
Require Import Order.equiv.
Require Import Order.utilities.

(* Require Import Coq.Sets.Ensembles.*)

(********** 
    SUPPORTS 
   
    CHASE analysis of a Copland Protocol generates 
    a set of graphs. We want to be able to compare 
    these sets of graphs so we introduce the idea 
    of supports as motivated by Rowe's paper.
    *********)

(* given some reflexive and transitive relation we 
 * know that supports is reflexive and transitive *)

  Definition reflexive {A : Type} (R : A -> A -> Prop) : Prop :=
    forall a, R a a.

  Definition transitive {A : Type} (R : A -> A -> Prop) : Prop :=
    forall a1 a2 a3, R a1 a2 -> R a2 a3 -> R a1 a3.

    (* Supports says: 
    
      * Given two sets of graphs SS and TT, we say
      * that SS supports TT iff for every H in TT
      * there exists some G in SS such that 
      * G < H *)

  Definition Supports {A : Type} (R : A -> A -> Prop) (S : list A) (T : list A) : Prop :=
    forall H, In H T ->
  (exists G, In G S /\ R G H).

  Lemma SupportsTrans : forall {A : Type} (R : A -> A -> Prop),
  transitive R -> transitive (Supports R).
  Proof.
    unfold transitive, Supports.
    intros A R HTran.
    - intros S T U HSup1 HSup2 H HIn.
      apply HSup2 in HIn. destruct HIn as [G' HIn]. destruct HIn as [HIn HR1].
      apply HSup1 in HIn. destruct HIn as [G HIn]. destruct HIn as [HIn HR2].
      exists G. split; [assumption | eapply HTran; eauto].
  Qed.

  Lemma SupportsWrapper : forall {A : Type} (R : A -> A -> Prop),
    reflexive R -> transitive R ->
    reflexive (Supports R) /\ transitive (Supports R).
  Proof.
    unfold reflexive, transitive, Supports.
    intros A R HRefl HTran.
    split.
    - intros S H HIn. specialize HRefl with H. exists H. split; assumption.
    - intros S T U HSup1 HSup2 H HIn.
      apply HSup2 in HIn. destruct HIn as [G' HIn]. destruct HIn as [HIn HR1].
      apply HSup1 in HIn. destruct HIn as [G HIn]. destruct HIn as [HIn HR2].
      exists G. split; [assumption | eapply HTran; eauto].
  Qed.


Section Supports_List. 

Context {measurement : Type}.
Context {corruption : Type}.

 (* Labels and States must have decidable equality *)
 Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
 Hypothesis eqDec_corruption : forall (x y : corruption), {x = y} + {x <> y}.
 Hypothesis eqDec_state : forall (G : attackgraph measurement corruption) (x y : G.(state _ _)), {x = y} + {x <> y}.


 (* prove supports is a strict partial order when the strict partial order
  * relation is applied *)
  Definition supports_spo (SS : list (attackgraph measurement corruption)) (TT : list (attackgraph measurement corruption)) : Prop := 
    forall (H : (attackgraph measurement corruption)), In H TT -> 
    (exists (G : (attackgraph measurement corruption)), In G SS /\ strict_partial_order (G.(steps _ _)) (H.(steps _ _))).

    (* TODO : is this irr? *)
    Theorem supports_spo_irr :forall a, ~ supports_spo a a.
    Proof.
      unfold not. unfold supports_spo.
      intros a spo_a_a. induction a.
      + admit.
      + specialize spo_a_a with a. simpl in *. intuition.
        pose proof (spo_irr a). apply IHa. intros. exists H2. split; eauto.
    Abort.

    Theorem supports_spo_trans : forall x y z, supports_spo x y -> supports_spo y z -> supports_spo x z.
    Proof. 
    unfold supports_spo.
    intros X Y Z. intros HXY HYZ.
    intros A InAZ.
    specialize HYZ with A; intuition.
    destruct H as [B H].
    destruct H as [InBY H].
    specialize HXY with B. intuition.
    destruct H0 as [C H0].
    destruct H0 as [InCX H0]. exists C; intuition.
    pose proof (spo_trans C B A).
    eapply H1; eauto.   
  Qed.

  (* prove supports is an equivalence relation when isomorphism 
   * relation is applied*)
  Definition supports_eq (SS : list (attackgraph measurement corruption)) (TT : list (attackgraph measurement corruption)) : Prop := 
    forall (H : (attackgraph measurement corruption)), In H TT ->
    exists (G : (attackgraph measurement corruption)), In G SS /\ exists f g, isomorphism G H f g.

  (* Prove properties of equivalence relation 
   * reflexive, symmetric, and transitive *)
  Theorem supports_eq_refl: forall x, supports_eq x x .
  Proof.
    intros. unfold supports_eq. intros.
    exists H. intuition.
    pose proof (isomorphism_refl H).
    inversion H1. exists x0; exists x0.
    eauto.     
  Qed.

  (* I don't think this proof is possible. 
   * Maybe all we have is a preorder *)
  Theorem supports_eq_sym : forall x y, supports_eq x y -> supports_eq y x.
  Proof.
    unfold supports_eq. 
    intros X Y HXY.
    intros a InaX.
    specialize HXY with a.
    intuition.  
  Abort. 

  Theorem  supports_eq_trans : forall x y z, supports_eq x y -> supports_eq y z -> supports_eq x z.
  Proof.
    unfold supports_eq.
    intros X Y Z. intros HXY HYZ.
    intros A InAZ.
    specialize HYZ with A; intuition.
    destruct H as [B H].
    destruct H as [InBY H].
    specialize HXY with B. intuition.
    destruct H0 as [C H0].
    destruct H0 as [InCX H0]. exists C; intuition.
    pose proof (isomorphism_trans C B A).
    apply H1; eauto.   
  Qed.


(* Supports is a partial order... defining partial order
  * this way is called the "reflexive kernel" 
  * <= *)
Definition supports (SS : list (attackgraph measurement corruption)) (TT : list (attackgraph measurement corruption)) : Prop := 
  forall (H : (attackgraph measurement corruption)), In H TT ->
  ( exists (G : (attackgraph measurement corruption)), In G SS /\ (strict_partial_order (G.(steps _ _)) (H.(steps _ _)) \/ exists f g, isomorphism G H f g )).
  

 Theorem supports_refl : forall SS,  supports SS SS.
 Proof.
  intros. unfold supports. intros.  
  exists H. split; eauto.
  right.
  pose proof (isomorphism_refl H).
  inversion H1.
  exists x. exists x.
  eauto.  
 Qed.

 (* TODO: what should equality be here? This isn't quite right  *)
 Theorem  supports_antisym : forall x y, supports x y -> supports y x ->  forall xs ys, In xs x /\ In ys y -> exists f g, isomorphism xs ys f g. 
 Proof.
    unfold supports.
    intros X. intros Y.
    intros supXY supYX.
    intros xs ys. intros H. destruct H as [HxsX HysY].
    specialize supYX with xs. intuition.
    specialize supXY with ys; intuition.
    destruct H as [y2 H].
    destruct H. destruct H0 as [x2 H0].
    destruct H0. 
    destruct H1.    
 Abort.
 
 Theorem  supports_trans : forall x y z, supports x y -> supports y z -> supports x z.
 Proof.
    unfold supports. intros X Y Z. intros supXY supYZ.
    intros c IncZ.
    specialize supYZ with c; intuition.
    destruct H as [b].
    destruct H as [InbY].
    specialize supXY with b.
    intuition.
    + destruct H as [a]. destruct H as [InaX]; intuition.
    ++ admit.
    ++ (* TODO: here is the case where you get a = b then b < c... how do they compare? *)
  Abort.      


Section Supports_Ensemble. 

Print homomorphism.

Context {measurement : Type}.
Context {corruption : Type}.

(* Given two sets of graphs SS and TT, we say
 * that SS supports TT iff for every H in TT
 * there exists some G in SS such that 
 * G < H *)
Definition supports (SS : Ensemble (attackgraph measurement corruption)) (TT : Ensemble (attackgraph measurement corruption)) : Prop := 
  forall (H : (attackgraph measurement corruption)), In _ TT H ->
  ( exists (G : (attackgraph measurement corruption)), In _ SS G /\ strict_partial_order (G.(steps _ _)) (H.(steps _ _))).
  
(* TODO *)
Theorem supports_irr : forall SS, ~ supports SS SS.
Proof.
    intros. unfold supports. 
    unfold not. intros.
Abort. 

Theorem supports_trans : forall SS TT PP, supports SS TT -> supports TT PP -> supports SS PP.
Proof.
    unfold supports. intros SS TT PP Hst Htp h' Hh'.
    specialize Htp with h'.
    destruct Htp; eauto.
    specialize Hst with x.
    destruct Hst. destruct H; eauto.
    destruct H. destruct H0.
    exists x0; split; eauto.
    eapply spo_trans; eauto.
Qed. 
 

(* Traditional def of supports. This generates a preorder on attack graphs *)
Definition supports_trad (SS : Ensemble (attackgraph measurement corruption)) (TT : Ensemble (attackgraph measurement corruption)) : Prop := 
    forall (H : (attackgraph measurement corruption)), In _ TT H ->
    ( exists (G : (attackgraph measurement corruption)), In _ SS G /\ exists f, homomorphism G H f ).
  
(* Proving traditional definition of supports is reflexive and transitive 
 * (ie a preorder) *)

Theorem supports_trad_refl : forall SS, supports_trad SS SS.
Proof.
  unfold supports_trad. intros. exists H; split; eauto. apply homomorphism_refl.
Qed.

Theorem supports_trad_trans : forall SS TT PP, supports_trad SS TT -> supports_trad TT PP -> supports_trad SS PP.
Proof.
   unfold supports_trad. intros SS TT PP Hst Htp h' Hh'.
   specialize Htp with h'.
   destruct Htp; eauto.
   specialize Hst with x.
   destruct Hst. destruct H; eauto.
   destruct H. destruct H0.
   exists x0; split; eauto.
   eapply homomorphism_trans; eauto.
Qed. 

End Supports_Ensemble.




(* TODOs:  Prove supports is a strict partial order  *)
