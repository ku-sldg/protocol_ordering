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

(* Given two sets of graphs SS and TT, we say
  * that SS supports TT iff for every H in TT
  * there exists some G in SS such that 
  * G < H *)

  Definition supports_spo' (SS : list (attackgraph measurement corruption)) (TT : list (attackgraph measurement corruption)) : Prop := 
    forall (H : (attackgraph measurement corruption)), In H TT ->
    exists (G : (attackgraph measurement corruption)), In G SS /\ strict_partial_order (G.(steps _ _)) (H.(steps _ _)).

  Inductive supports_spo : list (attackgraph measurement corruption) -> list (attackgraph measurement corruption) -> Prop :=
  | base' : forall SS, SS <> nil -> supports_spo nil SS
  | sup' : forall SS TT  (H : (attackgraph measurement corruption)), In H TT -> 
    (exists (G : (attackgraph measurement corruption)), In G SS /\ strict_partial_order (G.(steps _ _)) (H.(steps _ _))) -> supports_spo SS TT.

  (* want to prove this is a strict partial order too *)

  Theorem supports_spo_irr :forall a, ~ supports_spo a a.
  Proof.
    intros. unfold not. intros.
  Abort.

  (* this is equality *)
  Definition supports_eq' (SS : list (attackgraph measurement corruption)) (TT : list (attackgraph measurement corruption)) : Prop := 
    forall (H : (attackgraph measurement corruption)), In H TT ->
    exists (G : (attackgraph measurement corruption)), In G SS /\ exists f g, isomorphism G H f g.

  Theorem supports_eq_refl': forall x, supports_eq' x x .
  Proof.
    intros. unfold supports_eq'. intros.
    exists H. intuition.
    pose proof (isomorphism_refl H).
    inversion H1. exists x0; exists x0.
    eauto.     
  Qed.

  Inductive supports_eq : list (attackgraph measurement corruption) -> list (attackgraph measurement corruption) -> Prop :=
  | base : supports_eq nil nil
  | sup : forall SS TT  (H : (attackgraph measurement corruption)), In H TT -> 
    (exists (G : (attackgraph measurement corruption)), In G SS /\ exists f g, isomorphism G H f g) -> supports_eq SS TT.

  (* equivalence : reflexive, symmetric, transitive *)

  Theorem  supports_eq_refl : forall x, supports_eq x x.
  Proof.
    intros. induction x.
    + econstructor.
    + apply sup with (H:= a).
    ++ simpl. left.   eauto.
    ++ exists a. split.
    +++ simpl; eauto.
    +++ pose proof (isomorphism_refl a). inversion H.
        exists x0. exists x0. eauto.
  Qed.       
  
  Theorem supports_eq_sym: forall x y, supports_eq x y -> supports_eq y x.
  Proof.
    intros. 
    induction H.
    + econstructor.
    (* + destruct H1 as [G H1]. destruct H1. econstructor; eauto.
      destruct H2 as [f H2]. destruct H2 as [g H2].
      exists H; eauto. split; eauto.
      pose proof (isomorphism_sym G H).
      destruct H3 as [ f' H3 ].
    ++ exists f. exists g. eauto.
    ++ destruct H3 as [g'].
       exists g'. exists f'.
       eauto.
  Qed.*) Abort.
  
  Theorem supports_eq_trans : forall x y, supports_eq x y -> forall z, supports_eq y z -> supports_eq x z.
  Proof.
    intros. induction H.
    + intros. admit.
    + destruct H2. destruct H2. invc H0.
    ++ subst. inversion H1.
    ++ subst. destruct H6. destruct H0.
       econstructor; eauto. exists x; intuition; eauto.
       pose proof (isomorphism_trans x x0 H4).
       destruct H7; eauto.i am  




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
 
 (* TODO *)
Check isomorphism_sym.
Theorem  supports_antisym : forall SS TT, supports SS TT -> supports TT SS -> 
SS = TT.
Proof.
  unfold supports. intuition. induction SS.
  + induction TT; eauto.
    simpl in *. admit.
  +  
  + 

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
