(**** Defining support to compare sets of attack graphs. 
By: Anna Fritz and Sarah Johnson
Date: July 18, 2023 

Idea of supports motivated by Paul Rowe's paper: 
"On Orderings in Security Models" *)

Require Import Coq.Lists.List.

Require Import Order.attack_graph.
Require Import Order.strict_partial_order.
Require Import Order.reduce.
Require Import Order.equiv.
Require Import Order.utilities.
Require Import Order.partial_order.

Require Import Coq.Program.Equality.

(********** 
    SUPPORTS 
   
    CHASE analysis of a Copland Protocol generates 
    a set of graphs. We want to be able to compare 
    these sets of graphs so we introduce the idea 
    of supports as motivated by Rowe's paper.
    *********)


(* This section generalizes supports and various 
 * relations to ensure supports behaves 
 * as expected  *)    
Section Supports_Facts. 

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

  (* given some reflexive and transitive relation we 
   * know that supports is reflexive and transitive *)
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

 (* if g1 < g2 then g1 cannot equal g2 *)
 Theorem order_impl_not_eq : forall (g1 g2: attackgraph measurement corruption), strict_partial_order g1 g2 -> ~ isomorphism g1 g2.
 Proof.
    intros. unfold isomorphism, strict_partial_order in *. intuition.
    + destruct H as [fg1g2]. destruct H3 as [fg2g1]. destruct H1.
      unfold homomorphism in *. destruct H as [fsteps flab]. destruct H2 as [gsteps glab]. intuition. apply H3.
      clear H4. clear H1. clear H3. clear fsteps. clear flab.
      clear H0.
      induction (steps measurement corruption g2).    
    ++ econstructor.
    ++ econstructor.
    +++ unfold find_cor. 
        destruct (label measurement corruption g2 (fst a)) eqn:lab_g2; eauto. destruct a.  specialize glab with s s0. specialize gsteps with s s0. simpl in *. intuition.
        clear H0. clear H2. clear IHl. clear H4.  
        induction (steps measurement corruption g1).
    ++++ simpl in *. intuition.
    ++++ simpl in H1. destruct H1.
    +++++ destruct a. inversion H0. econstructor.
          rewrite <- lab_g2. rewrite H. eauto.
    +++++ apply ex_tail. apply IHl0. intuition.
    +++ apply IHl; auto with *.
    + destruct H as [fg1g2]. destruct H3 as [fg2g1]. destruct H1.
    unfold homomorphism in *. destruct H as [fsteps flab]. destruct H2 as [gsteps glab]. intuition. apply H3.
    clear H4. clear H0. clear H3. clear fsteps. clear flab.
    clear H1.
    induction (steps measurement corruption g2).    
  ++ econstructor.
  ++ econstructor.
  +++ unfold find_time. 
      destruct (label measurement corruption g2 (fst a)) eqn:lab_g2; eauto.  
      destruct (label measurement corruption g2 (snd a)) eqn:lab_g22; eauto. destruct a.  specialize glab with s s0. specialize gsteps with s s0. simpl in *. intuition.
      clear H0. clear H2. clear IHl.  
      induction (steps measurement corruption g1).
  ++++ simpl in *. intuition.
  ++++ simpl in H1. destruct H1.
  +++++ destruct a. inversion H0. econstructor. intuition.
        rewrite <- lab_g22. rewrite H4. eauto.
        rewrite <- lab_g2. rewrite H. eauto.
  +++++ apply ex_tail. apply IHl0. intuition.
  +++ apply IHl; auto with *.
 Qed.   
 
 (* prove supports is a strict partial order when the strict partial order
  * relation is applied 
  
  * strict partial order = irreflexive, asymmetric, transitive *)
  Definition supports_spo (SS : list (attackgraph measurement corruption)) (TT : list (attackgraph measurement corruption)) : Prop := 
    (forall (H : (attackgraph measurement corruption)), In H TT ->  
    (exists (G : (attackgraph measurement corruption)), In G SS /\ strict_partial_order G H)).

  (* supports is irreflexive for everything except nil.
   * need to disallow the first parameter to be nil  *)  
  Theorem supports_spo_irrefl :forall a, a <> nil -> ~ supports_spo a a.
  Proof.
    unfold supports_spo.
    intros a HNil contra.
    destruct a.
    (* a is nil *)
    - apply HNil. reflexivity.
    - clear HNil. generalize dependent a. induction a0.
    (* base case (a::nil)*)
    -- intros a contra. specialize contra with a. simpl in *. intuition.
      destruct H1. destruct H. destruct H; subst.
    --- pose proof (spo_irr x) as HIrr. contradiction.
    --- assumption.
    (* inductive case (a1 :: a :: a0) *)
    -- intros a1 contra. apply IHa0 with a1. intros HH HIn.
       pose proof (contra' := contra). specialize contra' with HH.
        simpl in contra'. intuition.
        simpl in HIn. intuition. 
    --- subst. destruct H3. destruct H. intuition. 
    ---- subst. exists x. auto with *.
    ---- subst. assert (contra' := contra). specialize contra with x.
         simpl in contra. intuition. destruct H3. destruct H3.
         intuition.
    ----- subst. exfalso. apply spo_asym  in H4. contradiction.
    ----- subst. exfalso. apply spo_irr in H4. destruct H4.
    ----- exists x0. intuition. eapply spo_trans; eauto.
    ---- exists x. intuition.
    --- destruct H3. destruct H2. intuition.
    ---- subst. exists x. intuition.
    ---- subst. assert (contra' := contra). specialize contra with x.
    simpl in contra. intuition. destruct H4. destruct H4.
    intuition.
  ----- subst.  exists x0. intuition. eapply spo_trans; eauto.
  ----- subst. exfalso. apply spo_irr in H5. destruct H5.
  ----- exists x0. intuition. eapply spo_trans; eauto.
  ---- exists x. intuition.
  Qed. 
  
  Theorem supports_spo_asym :forall x y, x <> nil -> supports_spo x y -> ~ supports_spo y x.
  Proof.
    unfold supports_spo. intros x y XNil Hxy Hyxcontra.
    destruct x.
    + apply XNil. reflexivity.
    + clear XNil. generalize dependent a. generalize dependent y. induction x.
    ++ intros ys y Hxy Hyxcontra. specialize Hyxcontra with y.
       simpl in *. intuition. destruct H1. destruct H; subst.
       clear H0. specialize Hxy with x.
       intuition. destruct H0. destruct H0.
       destruct H0. subst.
    +++ apply spo_asym in H2. contradiction. 
    +++ eauto.
    ++ intros ys y. intros Hxy Hyxcontra.
       apply IHx with ys y; clear IHx.
    +++ intros. eapply Hxy in H0. destruct H0.
        destruct H0. simpl in *.
        destruct H0.
    ++++ subst. exists x0. intuition.
    ++++ destruct H0. 
    +++++ subst. specialize Hyxcontra with x0. intuition.
          destruct H2. destruct H2. apply Hxy in H2. destruct  H2. destruct H2.
          intuition.
    ++++++ subst. exists x2. intuition. eapply spo_trans; eauto. eapply spo_trans; eauto.                       
    ++++++ subst. eapply spo_asym in H3. contradiction.
    ++++++ exists x2. intuition. eapply spo_trans; eauto. eapply spo_trans; eauto.
    +++++ exists x0; intuition.
    +++ intros. simpl in *. destruct H0.
    ++++ subst. assert (Hyxcontra' := Hyxcontra). specialize Hyxcontra' with H.
         intuition.
    ++++  assert (Hyxcontra' := Hyxcontra). specialize Hyxcontra' with H.
    intuition.
  Qed.    
    
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

  (* supports wrapper with isomorphism *)
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

  Theorem supports_iso_sym : forall x y, x <> nil -> supports_iso x y -> supports_iso y x.
  Proof.
  Abort.
  (* If x supports y then its not necessarily true that y supports x *) 

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
    eapply isomorphism_trans; eauto.
  Qed.

  (* TODO *)
  Theorem  supports_iso_dec : forall x y, x <> nil -> {supports_iso x y} + {~ supports_iso x y} .
  Proof.
    intros. destruct x.
    + exfalso. apply H. intuition.
    + clear H. generalize dependent a. generalize dependent y. induction x.
    ++ intros. unfold supports_iso.
  Abort. 

(*****************************
 REDUCE SET TO EASIEST GRAPHS 
*****************************)

  Inductive reduce_set (orig : list (attackgraph measurement corruption)) : list (attackgraph measurement corruption) ->  list (attackgraph measurement corruption) -> Prop :=
  | set_nil : reduce_set orig nil nil
  (* there does not exist anything that is less than a1 *)
  | set_keep : forall a1 SS TT, (forall a2, In a2 orig -> ~ strict_partial_order a2 a1) -> reduce_set orig SS TT -> reduce_set orig (a1 :: SS) (a1 :: TT) 
  | set_remove : forall a1 SS TT, (exists a2, In a2 orig /\ strict_partial_order a2 a1) -> reduce_set orig SS TT -> reduce_set orig (a1 :: SS) TT. 


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
  
  (* TODO *)
  Theorem set_eq_dec : forall SS TT, TT <> nil -> {set_eq SS TT} + {~ set_eq SS TT}.
  Proof.
    intros. destruct TT.
    + exfalso. apply H. reflexivity.
    + clear H. generalize dependent a. induction TT.
    ++ intros. unfold set_eq. unfold supports_iso. admit.
  Abort. 

(******************************* 
  SUPPORTS AS PARTIAL ORDER 
********************************)

Definition supports (SS : list (attackgraph measurement corruption)) (TT : list (attackgraph measurement corruption)) : Prop := 
  forall (H : (attackgraph measurement corruption)), In H TT ->
(exists (G : (attackgraph measurement corruption)), In G SS /\ (isomorphism G H \/ strict_partial_order G H)).

Theorem supports_refl : forall SS,  supports SS SS.
Proof.
 intros. unfold supports. intros. exists H. split; intuition.  left.
 pose proof (isomorphism_refl H).
 eauto.  
Qed.

Check reduce_set. 

Theorem reduce_set_in : forall x x', 
reduce_set x x x' ->
forall a, In a x' ->
In a x.
Proof.
intros. induction H;
simpl in *; intuition.
Qed.


Theorem reduce_set_supports : forall x x',
reduce_set x x x' ->
supports x x'.
Proof.
intros x x' XRed. unfold supports.
intros H HIn.
induction XRed; subst.
- inversion HIn.
- destruct HIn; subst.
-- exists H. split; auto with *. left. apply isomorphism_refl.
-- apply IHXRed in H1. destruct H1 as [G H1]. destruct H1.
 exists G. split; auto with *.
- apply IHXRed in HIn. destruct HIn as [G H1]. destruct H1.
exists G. split; auto with *.
Qed.

Theorem reduce_set_supports_y : forall x y y',
reduce_set y y y' ->
supports x y ->
supports x y'.
Proof.
intros x y y' YRed Sup. unfold supports in *.
intros H HIn. eapply reduce_set_in in HIn; eauto.
Qed.

Theorem reduce_set_keep : forall orig x x',
reduce_set orig x x' ->
forall g', In g' x' ->
forall g, In g orig ->
~ strict_partial_order g g'.
Proof.
intros orig x x' XRed g' Inx' g Inorig contra.
induction XRed.
- inversion Inx'.
- destruct Inx'.
-- subst. specialize H with g. intuition.
-- apply IHXRed. auto.
- apply IHXRed. auto.
Qed.

(* if x reduces to x'  then 
 * forall g in x and not in x', 
 * there exists some g2 in the original 
 * that is strictly less than g *)
Theorem reduce_set_remove : forall orig x x',
reduce_set orig x x' ->
forall g, In g x -> ~(In g x') ->
exists g2, (In g2 orig /\ (strict_partial_order g2 g)).
Proof.
intros orig x x' XRed g Inx NInx'.
induction XRed.
- inversion Inx.
- destruct Inx.
-- subst. exfalso. apply NInx'. auto with *.
-- apply IHXRed; auto. intros contra. apply NInx'. auto with *.
- destruct Inx.
-- subst. assumption.
-- intuition.
Qed.

(* if the reduced set returns nil then the original set 
 * must've been nil *)
Theorem reduce_set_nil : forall x,
reduce_set x x nil ->
x = nil.
Proof.
intros x XRed.
destruct x.
- reflexivity.
- exfalso. apply supports_spo_irrefl with (a::x).
-- intros contra. inversion contra.
-- unfold supports_spo. intros.
   eapply reduce_set_remove. eauto. eauto. eauto.
Qed.

Theorem reduce_set_lt : forall orig x x',
  reduce_set orig x x' ->
  forall g', In g' x' ->
  forall g, In g orig ->
  ~ strict_partial_order g g'.
Proof.
  intros orig x x' XRed g' Inx' g Inorig contra.
  induction XRed.
  - inversion Inx'.
  - destruct Inx'.
  -- subst. specialize H with g. intuition.
  -- apply IHXRed. auto.
  - apply IHXRed. auto.
Qed.

Theorem in_reduced_orig' : forall orig x xs xs', In x xs' -> reduce_set orig xs xs' -> In x xs.
Proof.
  intros. simpl in *. induction H0.
  + invc H. 
  + simpl in *. destruct H. eauto. eauto.
  + simpl in *. right. eauto. 
Qed.

Lemma reduced_supports : forall orig x x' y, 
  reduce_set orig x x' -> supports x' y -> supports x y.
Proof.
  intros. unfold supports in *. intros.
  apply H0 in H2. destruct H2. destruct H2.
  pose proof in_reduced_orig' orig x0 x x'.
  exists x0;
  intuition.
Qed.

Lemma reduced_supports_y_x_x' : forall x x' y, 
  reduce_set x x x' -> supports y x -> supports y x'.
Proof.
  intros x x' y red. induction red.
  + unfold supports. intros. invc H1.
  + intros. unfold supports in *.
    intros. destruct H2.
  ++ subst. specialize H0 with H1. simpl in H0. intuition.
  ++ eapply IHred; auto with *.
  + intros. unfold supports in *.
    intros. apply IHred; auto with *.
Qed.          

Ltac unfold_all := unfold supports in *; unfold supports_iso in *.

Print supports.

Theorem reduce_set_remove' : forall orig x x',
  reduce_set orig x x' ->
  forall g, In g x -> ~(In g x') ->
  exists g', (In g' x' /\ (strict_partial_order g' g)).
Proof.
Abort. 

Lemma reduced_supports_x_x' : forall orig x x' y, 
  reduce_set orig x x' -> supports x y -> supports x' y.
Proof.
  intros.
  (* pose proof (reduce_set_keep orig x x') as keep.
  pose proof (reduce_set_remove orig x x') as remove.*)
  intuition.
  unfold_all. intros.
  induction H.
  + apply H0 in H2. destruct H2. destruct H. invc H.
  + intuition. pose proof (reduce_set_keep orig SS TT) as keep. intuition.
Abort.    


Theorem  supports_antisym' : forall x y x' y',
supports x y -> supports y x -> 
reduce_set x x x' -> reduce_set y y y' -> set_eq x' y'. 
Proof.
intros X Y. intros X' Y'.
intros (* YNil XNil *) supXY supYX.
intros redX' redY'.
unfold set_eq. split.
(* X' is isomorphic to Y' *)   
+ pose proof (reduced_supports_y_x_x' X X' Y). intuition. clear supYX.
  pose proof (reduced_supports_y_x_x' Y Y' X). intuition. clear supXY.
  pose proof (reduce_set_nil X).
  destruct X.
++ unfold_all. intros. admit.
++ unfold_all. intros.  eapply H0 in H3. destruct H3. destruct H3.
   induction redX'.   
   Abort.
 
(* supports is transitive *)
Theorem  supports_trans' : forall x y z, supports x y -> supports y z -> supports x z.
Proof with intuition.
Proof.
  intros. unfold supports in *.
  intros. apply H0 in H2.
  destruct H2. destruct H2.
  apply H in H2.
  destruct H2. destruct H2.
  exists x1. intuition.
  + left. eapply isomorphism_trans;eauto.
  + right. eapply po_trans_helper; eauto.
  + right. eapply po_trans_helper'; eauto.
  + right. eapply spo_trans; eauto.
Qed.   

End Supports_List.
