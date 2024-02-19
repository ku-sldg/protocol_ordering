(**** Labeled Graph Homomorphism 
      By: Anna Fritz 
      Date: July 18, 2023 
      
      Defining supports and covers and other interesting 
      properties taken from Paul Rowe's paper: 
      "On Orderings in Security Models" *)

Require Import Coq.Relations.Relations.       
Require Import Coq.Sets.Ensembles.

(* Defining supports and covers over a general homomorphism *)
Module homomorphism. 

  Context {L : Set}.  

  (* could make L implicit since it exists in the context... maybe should optimize once finished *)
  Class graph := {
    N : Set ; 
    E : N -> N -> Prop ;
    l : N -> L
  }.

  (* preorder over graphs  *)
  Definition homomorphism (G : graph) (H : graph) (f : G.(N) -> H.(N)) : Prop := 
      forall v v', E v v' -> E (f v) (f v') /\
      forall n, l n = l (f n).
 
  Print homomorphism. 

  Notation "x < y" := (homomorphism x y) (at level 70). 

  (* Properties over homomorphisms *)
  Lemma  homomorphism_refl : forall x, exists (f : N -> N), (x < x) f .
  Proof.
      intros. unfold homomorphism. exists (fun x => x). split; intros; eauto.
  Qed.   

  Lemma  homomorphism_trans : forall x y z, 
      ( exists (fxy: N-> N), (x < y) fxy ) -> 
      ( exists (gyz: N-> N), (y < z) gyz ) -> 
      exists (hxz: N-> N), (x < z) hxz.
  Proof.
      intros x y z Hxy Hyz. 
      intros.
      destruct Hxy as [fxy xy]. destruct Hyz as [gyz yz].
      unfold homomorphism in *. 
      exists (fun x => gyz (fxy (x))).
      intros v v'' H; split.
      + specialize xy with v v''.
        destruct xy. eauto.
        specialize yz with (fxy v) (fxy v'').
        destruct yz. eauto.
        eauto.  
      + intros. 
        specialize xy with v v''.
        destruct xy. eauto.
        specialize H1 with n. rewrite H1. 
        specialize yz with (fxy v) (fxy v'').
        destruct yz. eauto.
        specialize H3 with (fxy n).
        rewrite H3.
        eauto.  
    Qed. 

  (********** 
      COVERS 
     *********)

  Definition covers (TT : Ensemble graph) (SS : Ensemble graph) : Prop := 
      forall (G : graph), In _ SS G ->
      ( exists (H : graph), In _ TT H /\ exists f, homomorphism G H f ) .

  Inductive downward_closure (SS P : Ensemble graph) : graph -> Prop := 
  | dc : Included _ SS P -> 
        forall G, In _ P G -> 
        (exists H, In _ SS H /\ exists f, homomorphism G H f) -> 
        downward_closure SS P G. 
  
  (* Could define downward closure as a subset... 
     but I'm not sure what they gets us*)
  Definition dc_subset (SS P : Ensemble graph) := 
    Included _ SS P -> 
    forall G, In _ P G -> 
    { G : graph | (exists H, In _ SS H /\ exists f, homomorphism G H f)}.


  (********** 
      SUPPORTS 
     *********)

  Definition supports (SS : Ensemble graph) (TT : Ensemble graph) : Prop := 
      forall (H : graph), In _ TT H ->
      ( exists (G : graph), In _ SS G /\ exists f, homomorphism G H f ) .

  Lemma supports_refl : forall SS, supports SS SS.
    unfold supports. intros. exists H; split; eauto. apply homomorphism_refl.
  Qed.
  
  Lemma supports_trans : forall SS TT PP, supports SS TT -> supports TT PP -> supports SS PP.
     unfold supports. intros SS TT PP Hst Htp h' Hh'.
     specialize Htp with h'.
     destruct Htp; eauto.
     specialize Hst with x.
     destruct Hst. destruct H; eauto.
     destruct H. destruct H0.
     exists x0; split; eauto.
     apply homomorphism_trans with (y := x); eauto.
  Qed. 

  Inductive upward_closure (SS PP : Ensemble graph) : graph -> Prop := 
  | uc : Included _ SS PP -> 
      forall H, In _ PP H -> 
      (exists G, In _ SS G /\ exists f, homomorphism G H f) -> 
      upward_closure SS PP H. 


  Lemma subset_dc : forall P SS: Ensemble graph, 
     Included _ SS P -> Included _ SS (downward_closure SS P).
  Proof.
      intros. unfold Included.
      intros. unfold In. simpl in *. apply dc.
      + eauto.
      + unfold Included in H. apply H. eauto.
      + exists x. split. 
      ++ eauto.
      ++ apply homomorphism_refl. 
  Qed.

  Lemma subset_uc : forall P SS: Ensemble graph, 
  Included _ SS P -> Included _ SS (upward_closure SS P).
  Proof.
    intros. unfold Included.
    intros. unfold In. simpl in *. apply uc.
    + eauto.
    + unfold Included in H. apply H. eauto.
    + exists x. split. 
    ++ eauto.
    ++ apply homomorphism_refl. 
    Qed.

  Ltac inv H := inversion H; subst.
  Ltac invc H := inversion H; subst; clear H. 
  Ltac incl H1 x := unfold Included in H1; specialize H1 with x.
  Ltac cov H1 x := unfold covers in H1; specialize H1 with x.

  (* Proving the downward closure of S is a subset of the downward closure of T iff T covers S *)
  Theorem three : forall SS TT PP, 
  Included _ SS PP -> Included _ TT PP -> 
  Included _ (downward_closure SS PP) (downward_closure TT PP) <-> covers TT SS.
  Proof.
      split; intros.
      (* dc implies covers... this is proved by the definition of covers *)
      + unfold covers. intros. 
        unfold Included in H1.
        apply subset_dc in H.
        unfold Included in H. 
        apply subset_dc in H0.
        unfold Included in H0.
        eapply H1 in H; eauto.
        destruct H. apply H4.  
      (* covers implies dc *)
      + unfold Included. intros K H2. apply dc. 
      ++ eauto.
      ++ inversion H2. eauto.
      ++ unfold covers in H1.
         destruct H2.
         destruct H4.
         destruct H4. apply H1 in H4.
         destruct H4. destruct H4.
         exists x0. split; eauto.
         apply homomorphism_trans with (y := x); eauto.
Qed. 

  (* Proving the upward closure of S is a subset of the upward closure of T iff T supports S *)
  Theorem three' : forall SS TT PP, 
          Included _ SS PP -> Included _ TT PP -> 
          Included _ (upward_closure SS PP) (upward_closure TT PP) <-> supports TT SS.
  Proof.
    split; intros.
    (* uc implies supports... this is proved by the definition of supports *)
    + unfold supports. intros. 
      apply subset_uc in H.
      apply subset_uc in H0.
      unfold Included in *.
      eapply H1 in H; eauto.
      destruct H. apply H5.  
    (* supports implies uc *)
    + unfold Included. intros K H2. apply uc. 
    ++ eauto.
    ++ inversion H2. eauto.
    ++ unfold supports in H1.
       destruct H2.
       destruct H5.
       destruct H5. apply H1 in H5.
       destruct H5. destruct H5.
       exists x0. split; eauto.
       apply homomorphism_trans with (y := x); eauto.
Qed.

End homomorphism.

(* Incorrect supports definitions *)

 (* defining partial order
  * this way is called the "reflexive kernel" 
  * <= *)
  Definition supports (SS : list (attackgraph measurement adversary)) (TT : list (attackgraph measurement adversary)) : Prop := supports_iso SS TT \/ supports_spo SS TT. 

  Theorem supports_refl : forall SS,  supports SS SS.
  Proof.
   intros. unfold supports. intros. left.
   unfold supports_iso. 
   intros s H. exists s.  split; eauto.
   pose proof (bidir_homo_refl s).
   eauto.  
  Qed.
  
  Theorem  supports_antisym : forall x y, y <> nil -> x <> nil -> supports x y -> supports y x -> set_eq x y. 
  Proof.
  intros X. intros Y.
  intros YNil XNil supXY supYX. unfold supports in *. intuition.
  + (* supports_iso X Y *)  
    unfold set_eq. split; eauto.
  + apply set_eq_sym. unfold set_eq. split; eauto.  
   (* X = Y & Y < X *)
   unfold supports_iso, supports_spo in *. 
   exfalso.
     destruct Y.
   ++ apply YNil. reflexivity.
   ++ clear XNil. clear YNil. generalize dependent a. generalize dependent X. induction Y.
   +++ intros. simpl in *. specialize H with a. intuition.
       destruct H. destruct H. specialize H0 with x. intuition. destruct H3. destruct H0. destruct H0. subst.
       apply myeq in H1; eauto. apply order_impl_not_eq in H3. intuition. intuition.
   +++ intros. apply IHY with X a0.
   ++++ intros. specialize H with H1. simpl in H. simpl in H2. intuition.
   ++++ intros. eapply H0 in H2. destruct H2.
   destruct H2. simpl in *.
   destruct H2.
   +++++ subst. exists x. intuition.
   +++++ destruct H2. 
   ++++++ subst. specialize H with x. intuition.
     destruct H4. destruct H. apply H0 in H. destruct H. destruct H.
     intuition.
   +++++++ subst. exists x1. intuition. assert (H' : strict_partial_order x1 x). { eapply po_trans_helper'; eauto. }
           eapply spo_trans; eauto.
   +++++++  subst. apply myeq in H4; eauto. apply order_impl_not_eq in H6. contradiction.
   +++++++ exists x1. intuition. assert (H' : strict_partial_order x1 x). { eapply po_trans_helper'; eauto. }
   eapply spo_trans; eauto.
   ++++++ exists x; intuition.
   + unfold set_eq; intuition. 
   (* X < Y & Y = X *)
   unfold supports_iso, supports_spo in *. 
     exfalso.
     destruct X.
   ++ apply XNil. reflexivity.
   ++ clear XNil. clear YNil. generalize dependent a. generalize dependent Y. induction X.
   +++ intros. simpl in *. specialize H0 with a. intuition.
       destruct H0. destruct H0. specialize H with x. intuition. destruct H3. destruct H. destruct H. subst.
       apply myeq in H1; eauto. apply order_impl_not_eq in H3. intuition. intuition.
   +++ intros. apply IHX with Y a0.
   ++++ intros. eapply H in H2. destruct H2.
   destruct H2. simpl in *.
   destruct H2.
   +++++ subst. exists x. intuition.
   +++++ destruct H2. 
   ++++++ subst. specialize H0 with x. intuition.
     destruct H4. destruct H0. apply H in H0. destruct H0. destruct H0.
     intuition.
   +++++++ subst. exists x1. intuition. assert (H' : strict_partial_order x1 x). { eapply po_trans_helper'; eauto. }
           eapply spo_trans; eauto.
   +++++++  subst. apply myeq in H4; eauto. apply order_impl_not_eq in H6. contradiction.
   +++++++ exists x1. intuition. assert (H' : strict_partial_order x1 x). { eapply po_trans_helper'; eauto. }
   eapply spo_trans; eauto.
   ++++++ exists x; intuition.
   ++++ intros. specialize H0 with H1. simpl in H0. simpl in H2. intuition.
   + unfold set_eq. exfalso. eapply supports_spo_asym in H0. contradiction. intuition.
  Qed. 
  
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
