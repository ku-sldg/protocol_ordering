(**************************************
 ** PARTIAL ORDER 
 ** OVER ATTACK TREES
    parameterized over 
    an arbitrary adversary 
    event ordering
***************************************)

Require Import Coq.Lists.List.

Require Import Order.attack_graph.
Require Import Order.parameterized_graph_strict_partial_order.
Require Import Order.graph_normalization.
Require Import Order.graph_equiv.
Require Import Order.utilities.

Section Parameterized_PO_Facts. 

Context {measurement : Type}.
 Context {adversary : Type}.
 Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
 Hypothesis eqDec_adversary : forall (x y : adversary), {x = y} + {x <> y}.
 Hypothesis eqDec_event : forall (G : attackgraph measurement adversary) (x y : G.(event _ _)), {x = y} + {x <> y}.

 (* Attack tree ordering is parameterized over an adversary event ordering *)
Context {adv_event_spo : adversary -> adversary -> Prop}.
 
(* The ordering is a strict partial order *)
Hypothesis adv_event_spo_irrefl : forall (x : adversary), ~ adv_event_spo x x.
Hypothesis adv_event_spo_asym : forall (x y :adversary), adv_event_spo x y -> ~ adv_event_spo y x.
Hypothesis adv_event_spo_trans : forall (x y z : adversary), adv_event_spo x y -> adv_event_spo y z -> adv_event_spo x z.

Let strict_partial_order := @strict_partial_order measurement adversary adv_event_spo.

 (******* DEFINING PARTIAL ORDER (PO) ********
  **         =  \/  <   ->     <= *)
Definition partial_order (G1 : attackgraph measurement adversary) (G2 : attackgraph measurement adversary) := 
    isomorphism G1 G2 \/ strict_partial_order G1 G2.
  
 (******* PROVE PO REFLEXIVE *********)
Theorem po_refl : forall G1 G2, isomorphism G1 G2 ->  partial_order G1 G2.
Proof.
  unfold partial_order. intros. left. eauto.
Qed.

(******* PROVE PO ANTISYMMETRIC  *********)
Theorem po_anitsym : forall G1 G2, partial_order G1 G2 -> partial_order G2 G1 -> isomorphism G1 G2.
Proof.
  unfold partial_order. intros.
  destruct H; eauto.
  destruct H0; eauto.
  eapply iso_sym. eauto.
  pose proof (@spo_asym _ _ adv_event_spo G1 G2); intuition.
Qed. 

(******* HELPER LEMMAS ********
 ** The following is a series of
 ** helper lemmas which prove 
 ** useful for transitivity *)
Lemma adv_meas_label_ : forall  (G3 : attackgraph measurement adversary) (G2 : attackgraph measurement adversary) 
(l : (list (event measurement adversary G3 * event measurement adversary G3))) m (l' : list (event measurement adversary G2 * event measurement adversary G2)) a,  label measurement adversary G3 (fst a) = inl m -> (@adv_subset_ind _ _ adv_event_spo _ _ l' (a :: l)) -> (@adv_subset_ind _ _ adv_event_spo _ _ l' l).
Proof.
  intros. remember (a::l) as list1.   induction H0.
  + econstructor.   
  + econstructor.
  ++ destruct (label measurement adversary G2 (fst x)) eqn:lab_x.
  +++ destruct x. unfold find_adv. rewrite lab_x. apply I.
  +++ unfold find_adv. rewrite lab_x.
      unfold find_adv in *.
      rewrite lab_x in H0.  
      inversion H0; subst.
  ++++ inversion H3. subst. destruct a. simpl in *. rewrite H in H2. destruct H2.
  +++++ inversion H2.
  +++++ simpl in H2. inversion H2.
  ++++ inversion H3. subst.  eauto.
  ++ intuition.
Qed. 

Lemma time_meas_label_ : forall  (G3 : attackgraph measurement adversary) (G2 : attackgraph measurement adversary) 
(l : (list (event measurement adversary G3 * event measurement adversary G3))) m1 m2 c (l' : list (event measurement adversary G2 * event measurement adversary G2)) a,  ((label measurement adversary G3 (fst a) = inl m1 /\ label measurement adversary G3 (snd a) = inl m2) \/  (label measurement adversary G3 (fst a)) = inr c) -> (@time_subset_ind _ _ adv_event_spo _ _ l' (a :: l)) -> (@time_subset_ind _ _ adv_event_spo _ _ l' l).
Proof.
  intros. remember (a::l) as list1. destruct H as [ms | cs].
  + induction H0.
  ++ econstructor.   
  ++ econstructor.
  +++ unfold find_time. destruct (label measurement adversary G2 (fst x)) eqn:lab_x1;   
     eauto.
     destruct (label measurement adversary G2 (snd (x))) eqn:lab_x2; eauto.
     unfold find_time in H. destruct ms as [m1' m2'].
     rewrite lab_x1 in H. rewrite lab_x2 in H. inversion H; subst.
  ++++ inversion H2; subst. destruct a. simpl in *. destruct H1. destruct H1.
  +++++ rewrite H1 in m2'. inversion m2'.
  +++++ rewrite m2' in H1. simpl in H1. inversion H1.
  ++++ inversion H2. subst. eauto.
  +++ intuition.
  + induction H0.
  ++ econstructor.
  ++ econstructor; intuition.
     unfold find_time. destruct (label measurement adversary G2 (fst x)) eqn:lab_x1; eauto. unfold find_time in H. rewrite lab_x1 in H.
     destruct (label measurement adversary G2 (snd (x))) eqn:lab_x2; eauto.
     inversion H; subst.
  +++ inversion H3; subst. destruct a.  inversion H2; subst. simpl in *. rewrite H5 in cs. inversion cs.
  +++ inversion H3; subst. eauto.
Qed. 

Lemma adv_subset_not_nil_if_c : forall  (G3 : attackgraph measurement adversary) (G2 : attackgraph measurement adversary)  a (l : (list (event measurement adversary G3 * event measurement adversary G3))) (l' : (list (event measurement adversary G2 * event measurement adversary G2))) c, 
l' = nil -> label measurement adversary G3 (fst a) = inr c -> (@adv_subset_ind _ _ adv_event_spo _ _ (a :: l) l') -> False.
Proof.
  intros. subst. simpl in *. inversion H1; subst.
  unfold find_adv in H3. rewrite H0 in H3. inversion H3.
Qed. 

Lemma po_trans_helper : forall (G1 G2 G3 : attackgraph measurement adversary), isomorphism G1 G2 /\ strict_partial_order G2 G3 -> strict_partial_order G1 G3.
  Proof with intuition.
  intros... 
  unfold isomorphism in H0.
  destruct H0 as [f iso].
  destruct iso as [ste' iso]. destruct iso as [lab iso]. destruct iso as [inj sur].
  assert (forall st1 st2 : event measurement adversary G1,
          In (st1, st2) (edges measurement adversary G1) ->
          In (f st1, f st2) (edges measurement adversary G2)) as ste.
  { intros. apply ste'. auto. }
  clear ste'.
  unfold strict_partial_order in *. unfold parameterized_graph_strict_partial_order.strict_partial_order in *...
  (* goal: adv subset *)
  + clear H. clear H2. 
    induction (edges measurement adversary G1); econstructor.
  ++ destruct a.
     eapply find_adv_helper;  eauto.
     unfold find_adv.
     destruct (label measurement adversary G1 (fst (e, e0))) eqn:lab'; eauto.
     simpl in *. intuition. clear IHl.
     clear H1.
     specialize ste with e e0.
     intuition.
     induction (edges measurement adversary G2)...
     simpl in *. inversion H1.
     simpl in *. destruct a0... 
  +++ inversion H. econstructor. 
      pose proof (lab e) as labs.
      rewrite <- lab'. rewrite labs. auto.
  +++ apply ex_tail. apply H2. 
  ++ apply IHl; auto with *.
  (* goal: time subset  *)
  + clear H. clear H1.
    induction (edges measurement adversary G1); econstructor.
  ++ destruct a.
     eapply find_time_helper; eauto.
     unfold find_time.
     destruct (label measurement adversary G1 (fst (e, e0))) eqn:fst; eauto.
     destruct (label measurement adversary G1 (snd (e, e0))) eqn:snd; eauto.
     simpl in *... clear IHl. clear H2.
     specialize ste with e e0.
     intuition. 
     induction (edges measurement adversary G2).
     simpl in *. inversion H1.
     simpl in *. destruct a0...
  +++ inversion H. econstructor.
      pose proof (lab e) as labs. pose proof (lab e0) as labs0. 
      split; intuition. rewrite <- snd. rewrite labs0. auto.
      rewrite <- fst. rewrite labs. auto.
  +++ apply ex_tail. apply H2.
  ++ apply IHl; auto with *.
  (* goal: proper subset  *)
  + left.
    unfold adv_proper_subset. intuition.
  ++ unfold adv_proper_subset in H...
     clear H2. clear H1. clear H3.
     induction (edges measurement adversary G1); econstructor.
  +++ destruct a.
      eapply find_adv_helper;  eauto.
      unfold find_adv.
      destruct (label measurement adversary G1 (fst (e, e0))) eqn:lab'; eauto.
      simpl in *. intuition. clear IHl. clear H0.
      specialize ste with e e0.
      intuition. 
      induction (edges measurement adversary G2).
      simpl in *. inversion H1.
      simpl in *. destruct a0...
  ++++ inversion H. econstructor. pose proof (lab e) as labs.
       intuition. rewrite <- lab'. rewrite labs. auto.
  ++++ apply ex_tail. apply H2.
  +++ apply IHl; auto with *.
  ++ unfold adv_proper_subset in H... apply H4.
      clear H4. clear H1. clear H2. clear H3.
      induction (edges measurement adversary G3); econstructor. 
  +++ destruct a.
      inversion H0; subst.
      eapply find_adv_helper; eauto. clear IHl. clear H4. clear H2. clear H0.
      induction (edges measurement adversary G1); econstructor.
  ++++ unfold find_adv in *. 
      destruct (label measurement adversary G1 (fst a)) eqn:lab'; eauto.
      destruct a. pose proof (lab e1) as labs1. pose proof (lab e2) as labs2. simpl in *...
      specialize ste with e1 e2. simpl in *... clear IHl0.
      induction (edges measurement adversary G2).
      inversion H1.
      simpl in *.
      destruct H1.
      destruct a. inversion H. apply ex_head. rewrite <- lab'. rewrite labs1. left. reflexivity.
      apply ex_tail. eapply IHl1...
  ++++ apply IHl0; auto with *.  
  +++ eapply IHl. inversion H0...
  (* goal adversary subset *)
  + clear H. clear H2.
    induction (edges measurement adversary G1); econstructor.
  ++ destruct a.
     eapply find_adv_helper;  eauto.
     unfold find_adv.
     destruct (label measurement adversary G1 (fst (e, e0))) eqn:lab'; eauto.
     simpl in *. intuition. clear IHl.
     clear H1. specialize ste with e e0. intuition. 
     induction (edges measurement adversary G2)...
     simpl in *. inversion H1.
     simpl in *. destruct a0... 
  +++ inversion H. econstructor. pose proof (lab e) as labs.
      rewrite <- lab'. rewrite labs. auto.
  +++ apply ex_tail. apply H2.
  ++ apply IHl; auto with *.
  (* goal : time subset *) 
  + clear H. clear H1. 
    induction (edges measurement adversary G1); econstructor.
  ++ destruct a.
     eapply find_time_helper; eauto.
     unfold find_time.
     destruct (label measurement adversary G1 (fst (e, e0))) eqn:fst; eauto.
     destruct (label measurement adversary G1 (snd (e, e0))) eqn:snd; eauto.
     simpl in *... clear IHl. clear H2.
     specialize ste with e e0.
     intuition. 
     induction (edges measurement adversary G2).
     simpl in *. inversion H1.
     simpl in *. destruct a0...
  +++ inversion H. econstructor. 
      pose proof (lab e) as labs. pose proof (lab e0) as labs0. 
      split; intuition. rewrite <- snd. rewrite labs0. auto.
      rewrite <- fst. rewrite labs. auto.
  +++ apply ex_tail. apply H2.
  ++ apply IHl; auto with *.
  (* goal: proper subset time *)
  + right.
    unfold time_proper_subset. intuition.
  ++ unfold time_proper_subset in H... clear H2. clear H1. clear H3.
     induction (edges measurement adversary G1); econstructor.
  +++ destruct a.
      eapply find_time_helper;  eauto; unfold find_time.
      destruct (label measurement adversary G1 (fst (e, e0))) eqn:lab'; eauto.
      destruct (label measurement adversary G1 (snd (e, e0))) eqn:lab''; eauto.
      simpl in *... clear IHl. clear H0.
      specialize ste with e e0...
      induction (edges measurement adversary G2).
      simpl in *. inversion H1.
      simpl in *. destruct a0...
  ++++ inversion H. econstructor. 
       pose proof (lab e) as labs. pose proof (lab e0) as labs0. 
       split; intuition. rewrite <- lab''. rewrite labs0. eauto.
       rewrite <- lab'. rewrite labs...
  ++++ apply ex_tail. apply H2.
  +++ apply IHl; auto with *.
  ++ unfold time_proper_subset in H... apply H4.
     clear H4. clear H1. clear H2. clear H3.
     induction (edges measurement adversary G3); econstructor. 
  +++ destruct a.
      inversion H0; subst.
      eapply find_time_helper; eauto. clear IHl. clear H4. clear H2. clear H0.
      induction (edges measurement adversary G1); econstructor.
  ++++ unfold find_time in *. 
       destruct (label measurement adversary G1 (fst a)) eqn:lab'; eauto.
       destruct (label measurement adversary G1 (snd a)) eqn:lab''; eauto.
       destruct a. simpl in *...
       specialize ste with e1 e2. simpl in *... clear IHl0.
       induction (edges measurement adversary G2).
       inversion H1. simpl in *. destruct H1.
  +++++ destruct a. inversion H.
        pose proof (lab e1) as labs1. pose proof (lab e2) as labs2.
        apply ex_head... rewrite <- lab''. rewrite labs2. left. reflexivity.
        rewrite <- lab'. rewrite labs1...
  +++++ apply ex_tail. eapply IHl1...
  ++++ apply IHl0; auto with *.  
  +++ eapply IHl. inversion H0...
Qed.


Lemma po_trans_helper' : forall (G1 G2 G3 : attackgraph measurement adversary), strict_partial_order G1 G2 /\ isomorphism G2 G3 -> strict_partial_order G1 G3.
Proof with intuition. 
  intros G1 G2 G3 H1. destruct H1 as [H1 H0]. 
  unfold isomorphism in H0.
  destruct H0 as [f iso].
  destruct iso as [ste' iso]. destruct iso as [lab iso]. destruct iso as [inj sur].
  assert (forall st1 st2 : event measurement adversary G2,
          In (st1, st2) (edges measurement adversary G2) ->
          In (f st1, f st2) (edges measurement adversary G3)) as ste.
  { intros. apply ste'. auto. }
  clear ste'.
  unfold strict_partial_order in *. unfold parameterized_graph_strict_partial_order.strict_partial_order in *...
  (* goal: adv subset *)
  + clear H. clear H2. 
    induction (edges measurement adversary G1); econstructor.
  ++ destruct a.
     inversion H1; subst.  
     eapply find_adv_helper;  eauto.
     unfold find_adv. clear IHl. clear H1. clear H2. clear H4.
     induction (edges measurement adversary G2); econstructor.
  +++ destruct a.  unfold find_adv. 
      destruct (label measurement adversary G2 (fst (e1, e2))) eqn:lab'; 
      eauto. simpl in *.
      specialize ste with e1 e2. simpl in *... clear IHl0.
      induction (edges measurement adversary G3)... inversion H1. simpl in *...
      econstructor. destruct a0. inversion H. pose proof (lab e1) as labs1.
      rewrite <- lab'. rewrite labs1... apply ex_tail...
  +++ apply IHl0; auto with *.
  ++ inversion H1... 
  (* goal: time subset *) 
  + clear H. clear H1.
    induction (edges measurement adversary G1); econstructor.
  ++ destruct a.
     inversion H2; subst.  
     eapply find_time_helper;  eauto. 
     clear IHl. clear H1. clear H2. clear H4.
     induction (edges measurement adversary G2); econstructor.
  +++ destruct a.  unfold find_time. 
      destruct (label measurement adversary G2 (fst (e1, e2))) eqn:lab'; eauto. 
      destruct (label measurement adversary G2 (snd (e1, e2))) eqn:lab''; eauto. 
      simpl in *.
      specialize ste with e1 e2. simpl in *... clear IHl0.
      induction (edges measurement adversary G3)... inversion H1.
      simpl in *...
      econstructor. destruct a0. inversion H...
      pose proof (lab e2) as labs2.
      rewrite <- lab''; rewrite labs2...
      pose proof (lab e1) as labs1.
      rewrite <- lab'; rewrite labs1...
      apply ex_tail...
  +++ apply IHl0; auto with *.
  ++ inversion H2...
  (* goal: adv proper *)
  + left. unfold adv_proper_subset in *...
  ++ clear H3. clear H2. clear H1.
     induction (edges measurement adversary G1); econstructor.
  +++ destruct a.
      inversion H0; subst.  
      eapply find_adv_helper;  eauto.
      clear IHl. clear H0. clear H2. clear H4.
      induction (edges measurement adversary G2); econstructor.
  ++++ destruct a.  unfold find_adv. 
       destruct (label measurement adversary G2 (fst (e1, e2))) eqn:lab'; eauto. 
       specialize ste with e1 e2.
       simpl in *... clear IHl0.
       induction (edges measurement adversary G3)... inversion H1.
       simpl in *...
       econstructor. destruct a0. inversion H.
       pose proof (lab e1) as labs1. rewrite <- lab'. rewrite labs1. auto.
       apply ex_tail...
  ++++ apply IHl0; auto with *.
  +++ inversion H0...
  ++ apply H3. clear H1. clear H2. clear H0. clear H3.
     induction (edges measurement adversary G2); econstructor.
  +++ eapply find_adv_helper; eauto. destruct a.
      unfold find_adv. destruct (label measurement adversary G2 (fst (e,e0))) eqn:lab'; eauto.
      specialize ste with e e0. simpl in *... clear IHl.
      induction (edges measurement adversary G3).
      inversion H2. simpl in *. destruct H2.
      destruct a0. inversion H0. apply ex_head.
      pose proof (lab e) as labs. rewrite <- lab'. rewrite labs...
      apply ex_tail. eapply IHl0... auto with *.
      inversion H; eauto.
  +++ apply IHl; auto with *.  
  (* goal: adv subset *)
  + clear H. clear H2.
    induction (edges measurement adversary G1); econstructor.
  ++ destruct a.
     inversion H1; subst.  
     eapply find_adv_helper;  eauto.
     unfold find_adv. clear IHl. clear H1. clear H2. clear H4.
     induction (edges measurement adversary G2); econstructor.
  +++ destruct a.  unfold find_adv. 
      destruct (label measurement adversary G2 (fst (e1, e2))) eqn:lab'; eauto. 
      simpl in *.
      specialize ste with e1 e2. simpl in *... clear IHl0.
      induction (edges measurement adversary G3)... inversion H1. simpl in *...
      econstructor. destruct a0. inversion H.
      pose proof (lab e1) as labs1. rewrite <- lab'. rewrite labs1...
      apply ex_tail...
  +++ apply IHl0; auto with *.
  ++ inversion H1...
  (* goal: time subset *) 
  + clear H. clear H1.
    induction (edges measurement adversary G1); econstructor.
  ++ destruct a. inversion H2; subst.  
     eapply find_time_helper;  eauto. clear IHl. clear H1. clear H2. clear H4.
     induction (edges measurement adversary G2); econstructor.
  +++ destruct a.  unfold find_time. 
      destruct (label measurement adversary G2 (fst (e1, e2))) eqn:lab'; eauto. 
      destruct (label measurement adversary G2 (snd (e1, e2))) eqn:lab''; eauto.
      simpl in *.
      specialize ste with e1 e2. simpl in *... clear IHl0.
      induction (edges measurement adversary G3)... inversion H1.
      simpl in *...
      econstructor. destruct a0. inversion H...
      pose proof (lab e2) as labs2.
      rewrite <- lab''; rewrite labs2...
      pose proof (lab e1) as labs1.
      rewrite <- lab'; rewrite labs1...
      apply ex_tail...
  +++ apply IHl0; auto with *.
  ++ inversion H2...
  (* goal: time proper *)
  + right. unfold time_proper_subset in *...
  ++ clear H1. clear H2. clear H3.
     induction (edges measurement adversary G1); econstructor.
  +++ destruct a. inversion H0; subst.  
      eapply find_time_helper;  eauto.
      clear IHl. clear H0. clear H2. clear H4.
      induction (edges measurement adversary G2); econstructor.
  ++++ destruct a.  unfold find_time. 
       destruct (label measurement adversary G2 (fst (e1, e2))) eqn:lab'; eauto.
       destruct (label measurement adversary G2 (snd (e1, e2))) eqn:lab''; eauto.
       simpl in *.
       specialize ste with e1 e2. simpl in *... clear IHl0.
       induction (edges measurement adversary G3)... inversion H1.
       simpl in *...
       econstructor. destruct a0; inversion H...
       pose proof (lab e2) as labs2.
       rewrite <- lab''. rewrite labs2...
       pose proof (lab e1) as labs1.
       rewrite <- lab'. rewrite labs1... 
       apply ex_tail...
  ++++ apply IHl0; auto with *.
  +++ inversion H0...
  ++ apply H3. clear H1. clear H2. clear H0. clear H3.
     induction (edges measurement adversary G2); econstructor.
  +++ eapply find_time_helper; eauto. destruct a.
      unfold find_time. 
      destruct (label measurement adversary G2 (fst (e,e0))) eqn:lab'; eauto.
      destruct (label measurement adversary G2 (snd (e, e0))) eqn:lab''; eauto.
      specialize ste with e e0. simpl in *... clear IHl.
      induction (edges measurement adversary G3).
      inversion H2. simpl in *. destruct H2.
      destruct a0. inversion H0. apply ex_head. split.
      pose proof (lab e0) as labs0. rewrite <- labs0. rewrite lab''...
      pose proof (lab e) as labs. rewrite <- lab'. rewrite labs...
      apply ex_tail. eapply IHl0... auto with *.
      inversion H; eauto.
  +++ apply IHl; auto with *.
Qed.



(**************************************
  PARTIAL ORDER OVER ATTACK TREES 
  IS TRANSITIVE 
**************************************)
Theorem po_trans : forall G1 G2 G3, partial_order G1 G2 -> partial_order G2 G3 -> partial_order G1 G3.
Proof with intuition.
  unfold partial_order.
  intros. 
  destruct H as [isoG1G2 | spoG1G2].
  + destruct H0 as [isoG2G3 | spoG2G3 ].
  (* g1 = g2 /\ g2 = g3 *)
  ++ left. eapply iso_trans; eauto.
  (* g1 = g2 /\ g2 < g3 *)
  ++ right. eapply po_trans_helper; eauto.
  + destruct H0 as [isoG2G3 | spoG2G3 ].
  (* g1 < g2 /\ g2 = g3 *)
  ++ right. eapply po_trans_helper'; eauto.
  (* g1 < g2 /\ g2 < g3 *)
  ++  right. eapply spo_trans; eauto.
Qed. 


End Parameterized_PO_Facts.