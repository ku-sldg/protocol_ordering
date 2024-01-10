
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