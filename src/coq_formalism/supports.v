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

(*Set Implicit Arguments.*)

(* Require Import Coq.Sets.Ensembles.*)


(**************************************
  partial order with individual graphs
***************************************)

Section PO. 

Context {measurement : Type}.
Context {corruption : Type}.

 (* Labels and States must have decidable equality *)
 Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
 Hypothesis eqDec_corruption : forall (x y : corruption), {x = y} + {x <> y}.
 Hypothesis eqDec_state : forall (G : attackgraph measurement corruption) (x y : G.(state _ _)), {x = y} + {x <> y}.

 Definition strict_partial_order' (g1 g2 : attackgraph measurement corruption) : Prop :=
  (cor_subset_ind (g1.(steps _ _)) (g2.(steps _ _)) /\ time_subset_ind (g1.(steps _ _)) (g2.(steps _ _))) /\ (cor_proper_subset (g1.(steps _ _)) (g2.(steps _ _)) \/ time_proper_subset (g1.(steps _ _)) (g2.(steps _ _))).

Definition partial_order (G1 : attackgraph measurement corruption) (G2 : attackgraph measurement corruption) := 
  isomorphism G1 G2 \/ strict_partial_order' G1 G2.
  
Theorem po_refl : forall G1 G2, isomorphism G1 G2 ->  partial_order G1 G2.
Proof.
  unfold partial_order. intros. left. eauto.
Qed.

Theorem po_anitsym : forall G1 G2, partial_order G1 G2 -> partial_order G2 G1 -> isomorphism G1 G2.
Proof.
  unfold partial_order. intros.
  destruct H; eauto.
  destruct H0; eauto.
  eapply isomorphism_sym. eauto.
  pose proof (spo_asym G1 G2).
  specialize H1 with (G1.(steps _ _)) (G2.(steps _ _)).
  exfalso. apply H1. eauto. eauto.
  Abort.

Lemma cor_meas_label_ : forall  (G3 : attackgraph measurement corruption) (G2 : attackgraph measurement corruption) 
(l : (list (state measurement corruption G3 * state measurement corruption G3))) m (l' : list (state measurement corruption G2 * state measurement corruption G2)) a,  label measurement corruption G3 (fst a) = inl m -> cor_subset_ind l' (a :: l) -> cor_subset_ind l' l.
Proof.
  intros. remember (a::l) as list1.   induction H0.
  + econstructor.   
  + econstructor.
  ++ destruct (label measurement corruption G2 (fst x)) eqn:lab_x.
  +++ destruct x. unfold find_cor. rewrite lab_x. apply I.
  +++ unfold find_cor. rewrite lab_x.
      unfold find_cor in *.
      rewrite lab_x in H0.  
      inversion H0; subst.
  ++++ inversion H3. subst. destruct a. simpl in *. rewrite H in H2. inversion H2.
  ++++ inversion H3. subst.  eauto.
  ++ intuition.
Qed. 

Lemma time_meas_label_ : forall  (G3 : attackgraph measurement corruption) (G2 : attackgraph measurement corruption) 
(l : (list (state measurement corruption G3 * state measurement corruption G3))) m1 m2 c (l' : list (state measurement corruption G2 * state measurement corruption G2)) a,  ((label measurement corruption G3 (fst a) = inl m1 /\ label measurement corruption G3 (snd a) = inl m2) \/  (label measurement corruption G3 (fst a)) = inr c) -> time_subset_ind l' (a :: l) -> time_subset_ind l' l.
Proof.
  intros. remember (a::l) as list1. destruct H as [ms | cs].
  + induction H0.
  ++ econstructor.   
  ++ econstructor.
  +++ unfold find_time. destruct (label measurement corruption G2 (fst x)) eqn:lab_x1;   
     eauto.
     destruct (label measurement corruption G2 (snd (x))) eqn:lab_x2; eauto.
     unfold find_time in H. destruct ms as [m1' m2'].
     rewrite lab_x1 in H. rewrite lab_x2 in H. inversion H; subst.
  ++++ inversion H2; subst. destruct a. simpl in *. destruct H1. rewrite H1 in m2'. inversion m2'.
  ++++ inversion H2. subst. eauto.
  +++ intuition.
  + induction H0.
  ++ econstructor.
  ++ econstructor; intuition.
     unfold find_time. destruct (label measurement corruption G2 (fst x)) eqn:lab_x1; eauto. unfold find_time in H. rewrite lab_x1 in H.
     destruct (label measurement corruption G2 (snd (x))) eqn:lab_x2; eauto.
     inversion H; subst.
  +++ inversion H3; subst. destruct a.  inversion H2; subst. simpl in *. rewrite H5 in cs. inversion cs.
  +++ inversion H3; subst. eauto.
Qed. 

Lemma cor_subset_not_nil_if_c : forall  (G3 : attackgraph measurement corruption) (G2 : attackgraph measurement corruption)  a (l : (list (state measurement corruption G3 * state measurement corruption G3))) (l' : (list (state measurement corruption G2 * state measurement corruption G2))) c, 
l' = nil -> label measurement corruption G3 (fst a) = inr c -> cor_subset_ind (a :: l) l' -> False.
Proof.
  intros. subst. simpl in *. inversion H1; subst.
  unfold find_cor in H3. rewrite H0 in H3. inversion H3.
Qed. 

Theorem po_trans : forall G1 G2 G3, partial_order G1 G2 -> partial_order G2 G3 -> partial_order G1 G3.
Proof.
  unfold partial_order.
  intros. 
  destruct H as [isoG1G2 | spoG1G2].
  + destruct H0 as [isoG2G3 | spoG2G3 ].
  (* g1 = g2 /\ g2 = g3 *)
  ++ left. eapply isomorphism_trans; eauto.
  (* g1 = g2 /\ g2 < g3 *)
  ++ right.
     unfold isomorphism in isoG1G2.
     destruct isoG1G2 as [H H0]. unfold homomorphism in H. destruct H as [f].
     destruct H as [ste lab].
     destruct H0 as [g]. unfold homomorphism in H. destruct H as [gste glab].
     unfold strict_partial_order' in *.
     intuition.
  +++ induction (steps measurement corruption G1).
  ++++ econstructor.
  ++++ econstructor.
  +++++ eapply find_cor_helper with (G2 := G2); eauto.
        clear IHl. admit.
  +++++ eapply IHl; auto with *. intros.  


  Abort.   

End PO.

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

  Definition asymmetric {A : Type} (R : A -> A -> Prop) : Prop := 
    forall a b, R a b -> ~ R b a. 

  Definition transitive {A : Type} (R : A -> A -> Prop) : Prop :=
    forall a1 a2 a3, R a1 a2 -> R a2 a3 -> R a1 a3.
    
  Lemma asym_implies_irr : forall {A : Type} (R : A -> A -> Prop), asymmetric R -> irreflexive R.
  Proof.
    unfold irreflexive, asymmetric.
    intros. intuition.
    specialize H with a a. intuition.
  Qed. 
    
  
  (* Supports says: 
    
      * Given two sets of graphs SS and TT, we say
      * that SS supports TT iff for every H in TT
      * there exists some G in SS such that 
      * G < H *)

  Definition Supports {A : Type} (R : A -> A -> Prop) (SS : list A) (TT : list A) : Prop :=(forall H, In H TT ->
  (exists G, In G SS /\ R G H)).

  Inductive Supports_ind {A : Type} (R : A -> A -> Prop) :  list A ->  list A -> Prop :=
  | sup_nil : forall SS, SS <> nil -> Supports_ind R SS nil
  | sup_cons : forall SS TT, (forall H, In H TT ->
  (exists G, In G SS /\ R G H)) -> Supports_ind R SS TT.
 

  Lemma Supports_nil_nil : forall {A: Type} (R : A -> A -> Prop) SS,  irreflexive R -> SS = nil -> Supports R SS SS.
  Proof.
    intros. subst. unfold Supports. intros. simpl in *. inversion H1.
  Qed.  

  Hypothesis eqDec_A : forall (A : Type) (x y : A), {x = y} + {x <> y}.

  Lemma SupportsIrr : forall {A : Type} (R : A -> A -> Prop),
    transitive R -> irreflexive R -> forall a, a <> nil -> ~ (Supports R) a a.
  Proof.
    unfold irreflexive. intros A R HTrans HIrr a HNil contra.
    destruct a.
    - apply HNil. reflexivity.
    - clear HNil. generalize dependent a. induction a0; unfold Supports in *.
    -- intros a contra. specialize contra with a. simpl in *. intuition.
       destruct H1. destruct H. destruct H; subst.
    --- specialize HIrr with x. contradiction.
    --- assumption.
    -- intros a1 contra. apply IHa0 with a. intros HH HIn.
       assert (In HH (a1 ::a :: a0) -> exists G : A, In G (a1 :: a :: a0) /\ R G HH) 
       by apply contra. simpl in *. destruct HIn; subst.
    --- pose proof (eqDec_A A). specialize X with a1 HH. destruct X; subst.
    ---- intuition. destruct H1 as [GG H1]. destruct H1. destruct H0; subst.
    ----- exists GG. auto.
    ----- exists GG. auto.
    ---- intuition. destruct H1 as [GG H1]. destruct H1. destruct H; subst.
    ----- assert (GG = GG \/ HH = GG \/ In GG a0 -> exists G : A, (GG = G \/ HH = G \/ In G a0) /\ R G GG)
          by apply contra. destruct H; subst.
    ------ left. reflexivity.
    ------ destruct H. destruct H; subst.
    ------- specialize HIrr with x. contradiction.
    ------- exists x. split; auto.
            eapply HTrans; eauto.
    ----- exists GG. auto.
    --- intuition. destruct H2 as [GG H2]. destruct H2. destruct H2; subst.
    ---- assert (GG = GG \/ a = GG \/ In GG a0 -> exists G : A, (GG = G \/ a = G \/ In G a0) /\ R G GG)
         by apply contra.
         destruct H2.
    ----- left. reflexivity.
    ----- destruct H2. destruct H2; subst.
    ------ specialize HIrr with x. contradiction.
    ------ exists x. split; auto.
           eapply HTrans; eauto.
    ---- exists GG. auto.
  Qed.

  (* if we prove asymmetry then we will get irreflexivity for free? 
    * http://web.stanford.edu/class/archive/cs/cs103/cs103.1164/lectures/09/Small09.pdf *)
  Lemma SupportsAsym : forall {A : Type} (R : A -> A -> Prop),
  asymmetric R -> asymmetric (Supports R).
  Proof.
    unfold asymmetric, Supports.
    intros. unfold not. intros. intuition.
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


 Theorem eq_impl_not_order : forall (g1 g2: attackgraph measurement corruption), (strict_partial_order (g1.(steps _ _)) (g2.(steps _ _))) -> ~ isomorphism g1 g2.
 Proof.
  intros. unfold isomorphism, strict_partial_order in *. intuition.
  + destruct H as [fg1g2]. destruct H3 as [fg2g1]. destruct H1.
    unfold homomorphism in *. intuition. 
  Abort.
  
  Theorem eq_impl_not_order : forall (g1 g2: attackgraph measurement corruption), (strict_partial_order (g1.(steps _ _)) (g2.(steps _ _))) -> ~ isomorphism g1 g2.
  Proof.
    intros. unfold strict_partial_order, isomorphism in *.
    unfold not. intros. intuition.
    + destruct H1. apply H2. induction H1.  econstructor.   
    
  Abort. 
 

 (* prove supports is a strict partial order when the strict partial order
  * relation is applied *)
  Definition supports_spo (SS : list (attackgraph measurement corruption)) (TT : list (attackgraph measurement corruption)) : Prop := 
    (forall (H : (attackgraph measurement corruption)), In H TT ->  
    (exists (G : (attackgraph measurement corruption)), In G SS /\ strict_partial_order (G.(steps _ _)) (H.(steps _ _)))).

  Inductive supports_spo_ind : list (attackgraph measurement corruption) -> list (attackgraph measurement corruption) ->Prop := 
  | sup_nil : forall SS, SS <> nil -> supports_spo_ind SS nil
  | sup_list : forall SS TT, (forall (H : (attackgraph measurement corruption)), In H TT ->  (exists (G : (attackgraph measurement corruption)), In G SS /\ strict_partial_order (G.(steps _ _)) (H.(steps _ _)))) -> supports_spo_ind SS TT.

  (* TODO : is this irr? *)
  Theorem supports_spo_irr :forall a, ~ supports_spo a a.
  Proof.
    unfold not. intros. induction H.
    + induction SS. destruct H. eauto. intuition. apply IHSS. intros. intuition. admit.
    +      
     inversion H.      unfold supports_spo.
    intros a spo_a_a. induction a.
    + admit.
    + 
    Lemma nil_supports_nil : supports_spo nil nil.
    Proof.
    
    Abort. 
    (* unfold supports_spo. simpl; intros.
      inversion H1.
    Qed.*)
    
    Lemma SS_supports_nil : forall SS, SS <> nil <-> supports_spo SS nil.
    Proof.
      unfold supports_spo. intros.  simpl in *. split.
      + intros. inversion H1. inversion H2. 
      + intros. induction SS. 
      ++ admit.
      ++ intuition. inversion H0.
      Abort.    
         
    Theorem supports_spo_refl :forall a, supports_spo a a.
    Proof.
      intros. induction a.
      + unfold supports_spo. intros. inversion H0. destruct H2. eauto. 
      + unfold supports_spo in *. intuition.
    Abort.  


    Theorem supports_spo_asym :forall x y, supports_spo x y -> ~ supports_spo y x.
    Proof.
      intros. unfold not. intros. unfold supports_spo in *.
      intuition. induction x.
      + admit.
      + intuition. specialize H0 with a.          

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
    intros x InxX.
    (* this issue is here bc there is no attack graph in Y *)
    induction Y.
    + simpl in *.
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
Definition supports' (SS : list (attackgraph measurement corruption)) (TT : list (attackgraph measurement corruption)) : Prop := 
  forall (H : (attackgraph measurement corruption)), In H TT ->
  ( exists (G : (attackgraph measurement corruption)), In G SS /\ strict_partial_order (G.(steps _ _)) (H.(steps _ _))) \/ 
  forall (H : (attackgraph measurement corruption)), In H TT ->
  ( exists (G : (attackgraph measurement corruption)), In G SS /\ isomorphism G H).


  Definition supports (SS : list (attackgraph measurement corruption)) (TT : list (attackgraph measurement corruption)) : Prop := supports_iso SS TT \/ supports_spo SS TT. 

 Theorem supports_refl : forall SS,  supports SS SS.
 Proof.
  intros. unfold supports. intros. left.
  unfold supports_iso. 
  intros s H. exists s.  split; eauto.
  pose proof (isomorphism_refl s).
  eauto.  
 Qed.

 (* TODO: what should equality be here? This isn't quite right  *)
 Theorem  supports_antisym : forall x y, supports x y -> supports y x -> set_eq x y. 
 Proof.
    intros X. intros Y.
    intros supXY supYX.
    unfold set_eq. split; unfold supports in *.
    + (* supports X Y *)  
      destruct supYX; eauto.
    ++ destruct supXY; eauto.
       unfold supports_iso in *. intros y1 Hy1Y.
       unfold supports_spo in H0. 
       specialize H with y1. intuition.
       (* y2 = x < y1 *)
       (* There's no where to go from here... *)       
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
    intuition.
    + admit.
    + right. unfold supports_iso, supports_spo in *.
      intros z HzZ.
      specialize H0 with z.
      intuition. destruct H1 as [y].
      destruct H0 as [HyZ spo]. specialize H with y.
      intuition. destruct H0 as [x].
      destruct H as [InxX].
      exists x. split; eauto.
      apply myeq in H.
      rewrite H.
      unfold isomorphism in H.
      destruct H as [fxy].
      destruct fxy as [fxy].
      destruct H as [gyx].
      unfold homomorphism in *.
      intuition.
      unfold strict_partial_order in *.
      intuition.
    ++ destruct H. clear H. induction (steps measurement corruption x).
    +++ econstructor.
    +++ econstructor.
    (* stuck here... *)
        inversion H5; subst.       
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
