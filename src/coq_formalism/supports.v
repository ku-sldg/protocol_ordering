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

Require Export Relation_Definitions.
Require Import Coq.Classes.Morphisms Setoid. 
Require Import Coq.Classes.SetoidTactics. 
Require Import Coq.Classes.Morphisms_Prop.

Check nil.

(*Set Implicit Arguments.*)

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

  Definition irreflexive {A : Type} (R : A -> A -> Prop) : Prop :=
    forall a, ~ R a a.

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

  Lemma SupportsIrr : forall {A : Type} (R : A -> A -> Prop),
  irreflexive R -> irreflexive (Supports R).
  Proof.
    unfold irreflexive, Supports. 
    intros A R Hirr lista.
    induction lista.
    +  unfold not. intros sup. admit.
    + simpl in *. unfold not. intros. apply IHlista.
      intros. specialize H with a. intuition.
      inversion H.         
  Abort. 

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
    (forall (H : (attackgraph measurement corruption)), In H TT -> 
    (exists (G : (attackgraph measurement corruption)), In G SS /\ strict_partial_order (G.(steps _ _)) (H.(steps _ _)))).

    Lemma nil_supports_nil : supports_spo nil nil.
    Proof.
    
    Abort. 
    (* unfold supports_spo. simpl; intros.
      inversion H1.
    Qed.*)
    
    Lemma SS_supports_nil : forall SS, SS <> nil <-> supports_spo SS nil.
    Proof.
      unfold supports_spo. intros.  simpl in *. split.
      + intros. inversion H1.
      + intros. simpl in *. intuition. subst. simpl in *.  
    Abort.    
         

    (* TODO : is this irr? *)
    Theorem supports_spo_irr :forall a, ~ supports_spo a a.
    Proof.
      unfold not. unfold supports_spo.
      intros a spo_a_a. induction a.
      + simpl in *. Abort.

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
  Definition supports_iso (SS : list (attackgraph measurement corruption)) (TT : list (attackgraph measurement corruption)) : Prop := 
    forall (H : (attackgraph measurement corruption)), In H TT ->
    (exists (G : (attackgraph measurement corruption)), In G SS /\ isomorphism G H).

  (* Prove properties of equivalence relation 
   * reflexive, symmetric, and transitive *)
  Theorem supports_iso_refl: forall x, supports_iso x x.
  Proof.
    intros. unfold supports_iso. intros.
    exists H. intuition.
    pose proof (isomorphism_refl H). eauto.
  Qed.

  (* I don't think this proof is possible. 
   * Maybe all we have is a preorder *)
  Theorem supports_iso_sym : forall x y, supports_iso x y -> supports_iso y x.
  Proof.
    unfold supports_iso. 
    intros X Y HXY.
    intros a InaX.
    (* this issue is here bc there is no attack graph in Y *)
    induction Y.
    + simpl in *. specialize HXY with a. intuition. exists a.
      split. 
    ++ subst. induction X.
    +++ simpl in  *. eauto.
    +++ simpl in *. apply IHX; eauto. intros. intuition.    
  Abort.

  Theorem  supports_iso_trans : forall x y z, supports_iso x y -> supports_iso y z -> supports_iso x z.
  Proof.
    unfold supports_iso.
    intros X Y Z. intros HXY HYZ.
    intros A InAZ.
    specialize HYZ with A; intuition.
    destruct H as [B H].
    destruct H as [InBY H].
    specialize HXY with B. intuition.
    destruct H0 as [C H0].
    destruct H0 as [InCX H0]. 
    exists C; intuition.
    Print isomorphism_trans.
    pose proof (isomorphism_trans eqDec_measurement eqDec_corruption eqDec_state H0 H).
    apply H1; eauto.   
  Qed.

  (* Equivalence over sets of graphs 
     We define this as each graph supports each other *)

  Definition set_eq SS TT :=  supports_iso SS TT /\ supports_iso TT SS.
  
  (* Prove properties of equivalence relation 
   * reflexivity 
   * symmetry
   * transitivity *)

  Theorem set_eq_refl : forall SS, set_eq SS SS .
  Proof.
    intros. unfold set_eq; split;
    apply supports_iso_refl.     
  Qed.

  Theorem set_eq_sym : forall SS TT, set_eq SS TT -> set_eq TT SS.
  Proof.
    intros. unfold set_eq in *; split; destruct H; intuition.
  Qed.
  
  Theorem set_eq_trans : forall SS TT, set_eq SS TT -> forall PP, set_eq TT PP -> set_eq SS PP.
  Proof. 
    unfold set_eq in *. intros SS TT seteqSSTT. destruct seteqSSTT as [seteqSSTT seteqTTSS]. intros PP.
    intros seteqTTPP. destruct seteqTTPP as [seteqTTPP seteqPPTT].
    split.
    + eapply supports_iso_trans; eauto.
    + eapply supports_iso_trans; eauto.
  Qed.
  
(* Proved set equivalence is an equivalence relation *)

(* Supports is a partial order... defining partial order
  * this way is called the "reflexive kernel" 
  * <= *)
Definition supports (SS : list (attackgraph measurement corruption)) (TT : list (attackgraph measurement corruption)) : Prop := 
  forall (H : (attackgraph measurement corruption)), In H TT ->
  ( exists (G : (attackgraph measurement corruption)), In G SS /\ (strict_partial_order (G.(steps _ _)) (H.(steps _ _)) \/ isomorphism G H)).
  

 Theorem supports_refl : forall SS,  supports SS SS.
 Proof.
  intros. unfold supports. intros.  
  exists H. split; eauto.
  right.
  pose proof (isomorphism_refl H).
  eauto.  
 Qed.

 (* TODO: what should equality be here? This isn't quite right  *)
 Theorem  supports_antisym : forall x y, supports x y -> supports y x ->  forall xs ys, In xs x /\ In ys y ->  isomorphism xs ys. 
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
 
 (* Axiom iso_eq : forall (x:attackgraph measurement corruption) y f g, isomorphism x y f g -> x = y.*)
 (* tried this but it didn't work... Axiom equivalence_equiv: Equivalence myeq. *)

 Lemma helper : forall (a b c: attackgraph measurement corruption), isomorphism a b /\ strict_partial_order b.(steps _ _) c.(steps _ _) -> strict_partial_order a.(steps _ _) c.(steps _ _).
 Proof.
  intros. intuition.
  (* generalize dependent a.*)  induction (steps measurement corruption c).
  + destruct H1. destruct H. destruct H1.
  ++ destruct H1. intros. intuition. exfalso. apply H3. econstructor.
  ++ destruct H1. intros. intuition. exfalso. apply H3. econstructor.
  + (* inductive case *)
    simpl in *. unfold strict_partial_order in *.
    intuition.
  
  Restart.
  intros. intuition. unfold strict_partial_order in *. intuition.
  + clear H3. destruct H. clear H1.
    unfold isomorphism in H0. destruct H0. destruct H0 as [fab].
    unfold homomorphism in H0. intuition.
    generalize dependent c. intros c.
    induction (steps measurement corruption c).
  ++ intros. exfalso. apply H2; econstructor.
  ++ intros. 
  
  Restart. (* I think I'm really close here... *)
  intros. intuition. unfold strict_partial_order in *. intuition.
  + clear H3. destruct H. clear H1. induction H.
  ++ generalize dependent H0. induction (steps measurement corruption a).
  +++ econstructor.
  +++ intros. intuition. econstructor; eauto. Search find_cor.

  Restart. 
  intros. intuition. unfold strict_partial_order in *. intuition.
  + clear H3. destruct H. clear H1. generalize dependent H0. induction (steps measurement corruption a).
  ++ econstructor.
  ++ intros. econstructor; eauto. eapply find_cor_helper with (ys := (steps measurement corruption b)); eauto. unfold find_cor. destruct (label measurement corruption a (fst a0)); eauto. induction (steps measurement corruption b).
  +++ admit.
  +++ econstructor. destruct a1.    
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
    ++ eexists; split; eauto. left. pose proof (spo_trans a b c).
       eapply H; eauto.
    ++ (* a = b /\ b < c => a < c *)
    Admitted. 
    


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
