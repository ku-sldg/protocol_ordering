(**** Labeled Graph Homomorphism 
By: Anna Fritz and Sarah Johnson
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
Require Import Order.partial_order.

(********** 
    SUPPORTS 
   
    CHASE analysis of a Copland Protocol generates 
    a set of graphs. We want to be able to compare 
    these sets of graphs so we introduce the idea 
    of supports as motivated by Rowe's paper.
    *********)

Section Supports_Facts. 


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
End Supports_Facts.


(********************************
 * OUR IMPLEMENTATION OF SUPPORTS 
 * FOR LISTS OF ATTACK GRAPHS 
 *********************************)

Section Supports_List. 

Context {measurement : Type}.
Context {corruption : Type}.

 (* Labels and States must have decidable equality *)
 Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
 Hypothesis eqDec_corruption : forall (x y : corruption), {x = y} + {x <> y}.
 Hypothesis eqDec_state : forall (G : attackgraph measurement corruption) (x y : G.(state _ _)), {x = y} + {x <> y}.
 (* could prove decidable from the hypothesis *)
 Hypothesis eqDec_graph : forall (G1 G2 : attackgraph measurement corruption), {G1 = G2} + {G1 <> G2}.

  (* TODO : maybe this? *)
 Theorem eq_impl_not_order : forall (g1 g2: attackgraph measurement corruption), (strict_partial_order (g1.(steps _ _)) (g2.(steps _ _))) -> ~ isomorphism g1 g2.
 Proof.
  intros. unfold isomorphism, strict_partial_order in *. intuition.
  + destruct H as [fg1g2]. destruct H3 as [fg2g1]. destruct H1.
    unfold homomorphism in *. intuition. 
  Abort.
  
  (* TODO : maybe this? *)
  Theorem eq_impl_not_order : forall (g1 g2: attackgraph measurement corruption), (strict_partial_order (g1.(steps _ _)) (g2.(steps _ _))) -> ~ isomorphism g1 g2.
  Proof.
    intros. unfold strict_partial_order, isomorphism in *.
    unfold not. intros. intuition.
    + destruct H1. apply H2. induction H1. 
  Abort. 
 

 (* prove supports is a strict partial order when the strict partial order
  * relation is applied *)
  Definition supports_spo (SS : list (attackgraph measurement corruption)) (TT : list (attackgraph measurement corruption)) : Prop := 
    (forall (H : (attackgraph measurement corruption)), In H TT ->  
    (exists (G : (attackgraph measurement corruption)), In G SS /\ strict_partial_order' G H)).

  (* TODO : is this irr? *)
  Theorem supports_spo_irrefl :forall a, a <> nil -> ~ supports_spo a a.
  Proof.
    unfold supports_spo.
    intros a HNil contra.
    destruct a.
    - apply HNil. reflexivity.
    - clear HNil. generalize dependent a. induction a0.
    -- intros a contra. specialize contra with a. simpl in *. intuition.
      destruct H1. destruct H. destruct H; subst.
    --- admit. (* pose proof (spo_irr x) as HIrr. specialize HIrr with x. contradiction. *)
    --- assumption.
    -- intros a1 contra. apply IHa0 with a. intros HH HIn.
      assert (In HH (a1 ::a :: a0) -> exists G, In G (a1 :: a :: a0) /\ strict_partial_order' G HH) 
      by apply contra. simpl in *. destruct HIn; subst.
    --- pose proof (eqDec_graph a1 HH). destruct H0; subst.
    ---- intuition. destruct H1 as [GG H1]. destruct H1. destruct H0; subst.
    ----- exists GG. auto.
    ----- exists GG. auto.
    ---- intuition. destruct H1 as [GG H1]. destruct H1. destruct H; subst.
    ----- assert (GG = GG \/ HH = GG \/ In GG a0 -> exists G, (GG = G \/ HH = G \/ In G a0) /\ strict_partial_order' G GG)
          by apply contra. destruct H; subst.
    ------ left. reflexivity.
    ------ destruct H. destruct H; subst.
    ------- admit. (* specialize HIrr with x. contradiction.*)
    ------- exists x. split; auto.
            (* eapply HTrans; eauto.*) admit. 
    ----- exists GG. auto.
    --- intuition. destruct H2 as [GG H2]. destruct H2. destruct H2; subst.
    ---- assert (GG = GG \/ a = GG \/ In GG a0 -> exists G, (GG = G \/ a = G \/ In G a0) /\ strict_partial_order' G GG)
        by apply contra.
        destruct H2.
    ----- left. reflexivity.
    ----- destruct H2. destruct H2; subst.
    ------ admit. (*  specialize HIrr with x. contradiction.*)
    ------ exists x. split; auto. admit. 
          (* eapply HTrans; eauto.*) 
    ---- exists GG. auto.
    Admitted. 
  
  Theorem supports_spo_asym :forall x y, x <> nil -> y <> nil -> supports_spo x y -> ~ supports_spo y x.
  Proof.
    unfold supports_spo. intros x y XNil YNil Hxy contra.
    destruct x.
    + apply XNil. reflexivity.
    + clear XNil. generalize dependent a. induction x.
    ++ intros a  Hxy contra. specialize contra with a.
       simpl in *. intuition. destruct H1. destruct H; subst.
       clear H0. specialize Hxy with x.
       intuition. destruct H0. destruct H0.
       destruct H0. subst.
    +++ admit.
    +++ eauto.
    ++ intros. apply IHx with (a := a) .
    +++ intros. destruct y.
    ++++ simpl in H0. exfalso; eauto.
    ++++ clear YNil. clear IHx.
         assert (Hind : In a1 (a1 :: y) -> exists G : attackgraph measurement corruption, In G (a0 :: a :: x) /\ strict_partial_order' G a1 ) by apply Hxy.
         simpl in Hind. intuition. destruct H3. destruct H1. specialize contra with x0. simpl in contra.
         apply contra in H1. destruct H1. destruct H1. clear H0. clear H2. clear contra.   induction y.
    +++++ simpl in *. admit.
    +++++ apply IHy. auto with *.   destruct H1.  
  Admitted.

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

  (* Prove properties of supports_iso 
   * reflexive, and transitive *)
  Theorem supports_iso_refl: forall x, supports_iso x x.
  Proof.
    intros. unfold supports_iso. intros.
    exists H. intuition.
    pose proof (isomorphism_refl H). eauto.
  Qed.

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

  (******************************
   SET EQUIVALENCE   
  
   * Equivalence over sets of graphs 
   * We define this as each graph supports each other *)

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
  
(******************************* 
  SUPPORTS AS PARTIAL ORDER 
********************************)

 (* defining partial order
  * this way is called the "reflexive kernel" 
  * <= *)
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
    unfold set_eq. split; unfold supports in *; intuition.
    + (* supports X Y *)  
      unfold supports_iso, supports_spo in *.
      intros y InyY.
      specialize
       admit.
    + eapply supports_spo_asym in H. contradiction.
    + admit.
    + eapply supports_spo_asym in H. contradiction.            
  Abort. 

 (* supports is transitive *)
 Theorem  supports_trans : forall x y z, supports x y -> supports y z -> supports x z.
 Proof with intuition.
    unfold supports. intros X Y Z. intros supXY supYZ...
    + left. eapply supports_iso_trans; eauto. 
    + right. unfold supports_iso, supports_spo in *.
      intros z HzZ.
      specialize H0 with z...
      destruct H1 as [y]. destruct H0 as [HyZ spo]. specialize H with y.
      intuition. destruct H0 as [x].
      destruct H as [InxX].
      exists x. split; eauto.
      eapply po_trans_helper; eauto.
    + right. unfold supports_iso, supports_spo in *.
    intros z HzZ.
    specialize H0 with z...
    destruct H1 as [y]. destruct H0 as [HyZ spo]. specialize H with y.
    intuition. destruct H0 as [x].
    destruct H as [InxX].
    exists x. split; eauto.
    eapply po_trans_helper'; eauto.
  + right. eapply supports_spo_trans; eauto.
Qed.

End Supports_List.