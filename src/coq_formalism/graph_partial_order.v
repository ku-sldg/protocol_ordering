(**************************************
 ** PARTIAL ORDER OVER 
 ** INDIVIDUAL GRAPHS
 ** PO defined as equality or strict partial order
 ** =  \/  <   ->     <=
 ** Proved partial order was reflexive, 
 ** transitive, and antisymmetric 
***************************************)

Require Import Coq.Lists.List.

Require Import Order.attack_graph.
Require Import Order.graph_strict_partial_order.
Require Import Order.graph_normalization.
Require Import Order.graph_equiv.
Require Import Order.utilities.

Section PO_Facts. 

Context {measurement : Type}.
Context {adversary : Type}.

 (* Labels and States must have decidable equality *)
 Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
 Hypothesis eqDec_adversary : forall (x y : adversary), {x = y} + {x <> y}.
 Hypothesis eqDec_state : forall (G : attackgraph measurement adversary) (x y : G.(state _ _)), {x = y} + {x <> y}.

 (******* DEFINING PARTIAL ORDER (PO) ********
  **         =  \/  <   ->     <= *)
Definition partial_order (G1 : attackgraph measurement adversary) (G2 : attackgraph measurement adversary) := 
  bidir_homo G1 G2 \/ strict_partial_order G1 G2.
  
 (******* PROVE PO REFLEXIVE *********)
Theorem po_refl : forall G1 G2, bidir_homo G1 G2 ->  partial_order G1 G2.
Proof.
  unfold partial_order. intros. left. eauto.
Qed.

(******* PROVE PO ANTISYMMETRIC  *********)
Theorem po_anitsym : forall G1 G2, partial_order G1 G2 -> partial_order G2 G1 -> bidir_homo G1 G2.
Proof.
  unfold partial_order. intros.
  destruct H; eauto.
  destruct H0; eauto.
  eapply bidir_homo_sym. eauto.
  pose proof (spo_asym G1 G2); intuition.
Qed. 

(******* HELPER LEMMAS ********
 ** The following is a series of
 ** helper lemmas which prove 
 ** useful for transitivity *)
Lemma cor_meas_label_ : forall  (G3 : attackgraph measurement adversary) (G2 : attackgraph measurement adversary) 
(l : (list (state measurement adversary G3 * state measurement adversary G3))) m (l' : list (state measurement adversary G2 * state measurement adversary G2)) a,  label measurement adversary G3 (fst a) = inl m -> cor_subset_ind l' (a :: l) -> cor_subset_ind l' l.
Proof.
  intros. remember (a::l) as list1.   induction H0.
  + econstructor.   
  + econstructor.
  ++ destruct (label measurement adversary G2 (fst x)) eqn:lab_x.
  +++ destruct x. unfold find_cor. rewrite lab_x. apply I.
  +++ unfold find_cor. rewrite lab_x.
      unfold find_cor in *.
      rewrite lab_x in H0.  
      inversion H0; subst.
  ++++ inversion H3. subst. destruct a. simpl in *. rewrite H in H2. inversion H2.
  ++++ inversion H3. subst.  eauto.
  ++ intuition.
Qed. 

Lemma time_meas_label_ : forall  (G3 : attackgraph measurement adversary) (G2 : attackgraph measurement adversary) 
(l : (list (state measurement adversary G3 * state measurement adversary G3))) m1 m2 c (l' : list (state measurement adversary G2 * state measurement adversary G2)) a,  ((label measurement adversary G3 (fst a) = inl m1 /\ label measurement adversary G3 (snd a) = inl m2) \/  (label measurement adversary G3 (fst a)) = inr c) -> time_subset_ind l' (a :: l) -> time_subset_ind l' l.
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
  ++++ inversion H2; subst. destruct a. simpl in *. destruct H1. rewrite H1 in m2'. inversion m2'.
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

Lemma cor_subset_not_nil_if_c : forall  (G3 : attackgraph measurement adversary) (G2 : attackgraph measurement adversary)  a (l : (list (state measurement adversary G3 * state measurement adversary G3))) (l' : (list (state measurement adversary G2 * state measurement adversary G2))) c, 
l' = nil -> label measurement adversary G3 (fst a) = inr c -> cor_subset_ind (a :: l) l' -> False.
Proof.
  intros. subst. simpl in *. inversion H1; subst.
  unfold find_cor in H3. rewrite H0 in H3. inversion H3.
Qed. 

Lemma po_trans_helper : forall (G1 G2 G3 : attackgraph measurement adversary), bidir_homo G1 G2 /\ strict_partial_order G2 G3 -> strict_partial_order G1 G3.
Proof with intuition.
intros... 
unfold bidir_homo in H0.
destruct H0 as [isoG1G2  spoG1G2]. 
destruct isoG1G2 as [f H]. unfold homomorphism in H. destruct H as [ste lab].
destruct spoG1G2. unfold homomorphism in H. destruct H as [gste glab].
unfold strict_partial_order in *...
(* goal: cor subset *)
+ clear H. clear H2. clear gste.
  induction (steps measurement adversary G1); econstructor.
++ destruct a.
  eapply find_cor_helper;  eauto.
  unfold find_cor.
  destruct (label measurement adversary G1 (fst (s, s0))) eqn:lab'; eauto.
  simpl in *. intuition. clear IHl.
  clear H1.
  specialize ste with s s0.
  intuition. 
  induction (steps measurement adversary G2)...
  simpl in *. inversion H1.
  simpl in *. destruct a0... 
+++ inversion H. econstructor. specialize lab with s s0...
    rewrite <- lab'. rewrite H1. eauto.
+++ apply ex_tail. eapply IHl0; intuition; specialize glab with st1 st2...
++ apply IHl; auto with *.
  (* goal: time subset  *)
+  clear H. clear H1. clear gste.
      induction (steps measurement adversary G1); econstructor.
++ destruct a.
      eapply find_time_helper; eauto.
      unfold find_time.
      destruct (label measurement adversary G1 (fst (s, s0))) eqn:fst; eauto.
      destruct (label measurement adversary G1 (snd (s, s0))) eqn:snd; eauto.
      simpl in *... clear IHl. clear H2.
      specialize ste with s s0.
      intuition. 
      induction (steps measurement adversary G2).
      simpl in *. inversion H1.
      simpl in *. destruct a0...
+++ inversion H. econstructor. split; specialize lab with s s0;
      intuition. rewrite <- snd. rewrite H6. eauto.
       rewrite <- fst. rewrite H1. eauto.
+++ apply ex_tail. eapply IHl0; intuition; specialize glab with st1 st2.
      intuition. intuition.
++ apply IHl; auto with *.
  (* goal: proper subset  *)
+ left.
  unfold cor_proper_subset. intuition.
++ unfold cor_proper_subset in H... clear H2. clear H1. clear H3. clear gste.
  induction (steps measurement adversary G1); econstructor.
+++ destruct a.
      eapply find_cor_helper;  eauto.
      unfold find_cor.
      destruct (label measurement adversary G1 (fst (s, s0))) eqn:lab'; eauto.
      simpl in *. intuition. clear IHl. clear H0.
      specialize ste with s s0.
      intuition. 
      induction (steps measurement adversary G2).
      simpl in *. inversion H1.
      simpl in *. destruct a0...
++++ inversion H. econstructor. specialize lab with s s0.
      intuition. rewrite <- lab'. rewrite H1. eauto.
++++ apply ex_tail. eapply IHl0; intuition; specialize glab with st1 st2...
+++ apply IHl; auto with *.
++ unfold cor_proper_subset in H... apply H4.
  clear H4. clear H1. clear H2. clear H3. clear gste. 
  induction (steps measurement adversary G3); econstructor. 
+++ destruct a.
  inversion H0; subst.
  eapply find_cor_helper; eauto. clear IHl. clear H4. clear H2. clear H0.
  induction (steps measurement adversary G1); econstructor.
++++ unfold find_cor in *. 
    destruct (label measurement adversary G1 (fst a)) eqn:lab'; eauto.
    destruct a. specialize lab with s1 s2... simpl in *...
    specialize ste with s1 s2. simpl in *... clear IHl0.  (* clear IHl0. clear H4. clear H.*)
    induction (steps measurement adversary G2).
    inversion H4.
    simpl in *.
    destruct H4.
    destruct a. inversion H1. apply ex_head. rewrite <- lab'. rewrite H. reflexivity.
    apply ex_tail. eapply IHl1... auto with *.
    specialize glab with st1 st2. simpl in *...  
    specialize glab with st1 st2. simpl in *...
++++ apply IHl0; auto with *.  
+++ eapply IHl. inversion H0...
(* goal adversary subset *)
+ clear H. clear H2. clear gste.
induction (steps measurement adversary G1); econstructor.
++ destruct a.
  eapply find_cor_helper;  eauto.
  unfold find_cor.
  destruct (label measurement adversary G1 (fst (s, s0))) eqn:lab'; eauto.
  simpl in *. intuition. clear IHl.
  clear H1. specialize ste with s s0. intuition. 
  induction (steps measurement adversary G2)...
  simpl in *. inversion H1.
  simpl in *. destruct a0... 
+++ inversion H. econstructor. specialize lab with s s0...
  rewrite <- lab'. rewrite H1. eauto.
+++ apply ex_tail. eapply IHl0; intuition; specialize glab with st1 st2...
++ apply IHl; auto with *.
+ (* goal : time subset *) 
  clear H. clear H1. clear gste.
      induction (steps measurement adversary G1); econstructor.
++ destruct a.
      eapply find_time_helper; eauto.
      unfold find_time.
      destruct (label measurement adversary G1 (fst (s, s0))) eqn:fst; eauto.
      destruct (label measurement adversary G1 (snd (s, s0))) eqn:snd; eauto.
      simpl in *... clear IHl. clear H2.
      specialize ste with s s0.
      intuition. 
      induction (steps measurement adversary G2).
      simpl in *. inversion H1.
      simpl in *. destruct a0...
+++ inversion H. econstructor. split; specialize lab with s s0;
      intuition. rewrite <- snd. rewrite H6. eauto.
       rewrite <- fst. rewrite H1. eauto.
+++ apply ex_tail. eapply IHl0; intuition; specialize glab with st1 st2.
      intuition. intuition.
++ apply IHl; auto with *.
  (* goal: proper subset time *)
+ right.
  unfold time_proper_subset. intuition.
++ unfold time_proper_subset in H... clear H2. clear H1. clear H3. clear gste.
  induction (steps measurement adversary G1); econstructor.
+++ destruct a.
  eapply find_time_helper;  eauto; unfold find_time.
  destruct (label measurement adversary G1 (fst (s, s0))) eqn:lab'; eauto.
  destruct (label measurement adversary G1 (snd (s, s0))) eqn:lab''; eauto.
  simpl in *... clear IHl. clear H0.
  specialize ste with s s0...
  induction (steps measurement adversary G2).
  simpl in *. inversion H1.
  simpl in *. destruct a0...
++++ inversion H. econstructor. specialize lab with s s0.
intuition. rewrite <- lab''. rewrite H6. eauto.
rewrite <- lab'. rewrite H1...
++++ apply ex_tail. eapply IHl0; intuition; specialize glab with st1 st2...
+++ apply IHl; auto with *.
++ unfold time_proper_subset in H... apply H4.
clear H4. clear H1. clear H2. clear H3. clear gste. 
induction (steps measurement adversary G3); econstructor. 
+++ destruct a.
inversion H0; subst.
eapply find_time_helper; eauto. clear IHl. clear H4. clear H2. clear H0.
induction (steps measurement adversary G1); econstructor.
++++ unfold find_time in *. 
destruct (label measurement adversary G1 (fst a)) eqn:lab'; eauto.
destruct (label measurement adversary G1 (snd a)) eqn:lab''; eauto.
destruct a. specialize lab with s1 s2... simpl in *...
specialize ste with s1 s2. simpl in *... clear IHl0.  (* clear IHl0. clear H4. clear H.*)
induction (steps measurement adversary G2).
inversion H4. simpl in *. destruct H4.
+++++ destruct a. inversion H1. apply ex_head... rewrite <- lab''. rewrite H2. reflexivity.
      rewrite <- lab'. rewrite H...
+++++ apply ex_tail. eapply IHl1... auto with *.
specialize glab with st1 st2. simpl in *...  
specialize glab with st1 st2. simpl in *...
++++ apply IHl0; auto with *.  
+++ eapply IHl. inversion H0...
Qed.

Lemma po_trans_helper' : forall (G1 G2 G3 : attackgraph measurement adversary), strict_partial_order G1 G2 /\ bidir_homo G2 G3 -> strict_partial_order G1 G3.
Proof with intuition.
intros G1 G2 G3 H1. destruct H1 as [H1 H0]. 
unfold bidir_homo in H0.
destruct H0 as [isoG1G2  spoG1G2]. 
destruct isoG1G2 as [f H]. unfold homomorphism in H. destruct H as [ste lab].
destruct spoG1G2. unfold homomorphism in H. destruct H as [gste glab].
unfold strict_partial_order in *...
(* goal: cor subset *)
+ clear H. clear H2. clear gste.
  induction (steps measurement adversary G1); econstructor.
++ destruct a.
   inversion H1; subst.  
   eapply find_cor_helper;  eauto.
    unfold find_cor. clear IHl. clear H1. clear H2. clear H4. clear glab. 
    induction (steps measurement adversary G2); econstructor.
+++ destruct a.  unfold find_cor. destruct (label measurement adversary G2 (fst (s1, s2))) eqn:lab'; eauto. simpl in *.
    specialize lab with s1 s2.
    specialize ste with s1 s2. simpl in *... clear IHl0.
    induction (steps measurement adversary G3)... inversion H1. simpl in *...
    econstructor. destruct a0. inversion H3. rewrite <- lab'. rewrite H... apply ex_tail...
+++ apply IHl0; auto with *.
++ inversion H1...
+ (* goal: time subset *) 
  clear H. clear H1. clear gste.
  induction (steps measurement adversary G1); econstructor.
++ destruct a.
   inversion H2; subst.  
   eapply find_time_helper;  eauto. clear IHl. clear H1. clear H2. clear H4. clear glab. 
    induction (steps measurement adversary G2); econstructor.
+++ destruct a.  unfold find_time. 
   destruct (label measurement adversary G2 (fst (s1, s2))) eqn:lab'; eauto. 
   destruct (label measurement adversary G2 (snd (s1, s2))) eqn:lab''; eauto. simpl in *.
    specialize lab with s1 s2.
    specialize ste with s1 s2. simpl in *... clear IHl0.
    induction (steps measurement adversary G3)... inversion H1.
    simpl in *...
    econstructor. destruct a0. inversion H3...
     rewrite <- lab''; rewrite H4...
     rewrite <- lab'; rewrite H...
    apply ex_tail...
+++ apply IHl0; auto with *.
++ inversion H2...
(* goal: cor proper *)
+ left. unfold cor_proper_subset in *...
++ clear H3. clear H2. clear H1. clear gste.
  induction (steps measurement adversary G1); econstructor.
+++ destruct a.
   inversion H0; subst.  
   eapply find_cor_helper;  eauto.
   clear IHl. clear H0. clear H2. clear H4. clear glab. 
    induction (steps measurement adversary G2); econstructor.
++++ destruct a.  unfold find_cor. destruct (label measurement adversary G2 (fst (s1, s2))) eqn:lab'; eauto. simpl in *.
    specialize lab with s1 s2.
    specialize ste with s1 s2. simpl in *... clear IHl0.
    induction (steps measurement adversary G3)... inversion H1.
    simpl in *...
    econstructor. destruct a0. inversion H3. rewrite <- lab'.
    rewrite H...
    apply ex_tail...
++++ apply IHl0; auto with *.
+++ inversion H0...
++ apply H3. clear H1. clear H2. clear H0. clear H3.
   clear gste.
   induction (steps measurement adversary G2); econstructor.
+++ eapply find_cor_helper; eauto. destruct a.
    unfold find_cor. destruct (label measurement adversary G2 (fst (s,s0))) eqn:lab'; eauto.
    specialize lab with s s0... simpl in *...
    specialize ste with s s0. simpl in *... clear IHl.  (* clear IHl0. clear H4. clear H.*)
    induction (steps measurement adversary G3).
    inversion H5. simpl in *. destruct H5.
    destruct a0. inversion H2. apply ex_head. rewrite <- lab'. rewrite H0...
    apply ex_tail. eapply IHl0... auto with *.
    specialize glab with st1 st2. simpl in *...  
    specialize glab with st1 st2. simpl in *...
    inversion H; eauto.
+++ apply IHl; auto with *.  
(* goal: cor subset *)
+ clear H. clear H2. clear gste.
  induction (steps measurement adversary G1); econstructor.
++ destruct a.
   inversion H1; subst.  
   eapply find_cor_helper;  eauto.
    unfold find_cor. clear IHl. clear H1. clear H2. clear H4. clear glab. 
    induction (steps measurement adversary G2); econstructor.
+++ destruct a.  unfold find_cor. destruct (label measurement adversary G2 (fst (s1, s2))) eqn:lab'; eauto. simpl in *.
    specialize lab with s1 s2.
    specialize ste with s1 s2. simpl in *... clear IHl0.
    induction (steps measurement adversary G3)... inversion H1. simpl in *...
    econstructor. destruct a0. inversion H3. rewrite <- lab'. rewrite H... apply ex_tail...
+++ apply IHl0; auto with *.
++ inversion H1...
+ (* goal: time subset *) 
  clear H. clear H1. clear gste.
  induction (steps measurement adversary G1); econstructor.
++ destruct a.
   inversion H2; subst.  
   eapply find_time_helper;  eauto. clear IHl. clear H1. clear H2. clear H4. clear glab. 
    induction (steps measurement adversary G2); econstructor.
+++ destruct a.  unfold find_time. 
   destruct (label measurement adversary G2 (fst (s1, s2))) eqn:lab'; eauto. 
   destruct (label measurement adversary G2 (snd (s1, s2))) eqn:lab''; eauto. simpl in *.
    specialize lab with s1 s2.
    specialize ste with s1 s2. simpl in *... clear IHl0.
    induction (steps measurement adversary G3)... inversion H1.
    simpl in *...
    econstructor. destruct a0. inversion H3...
     rewrite <- lab''; rewrite H4...
     rewrite <- lab'; rewrite H...
    apply ex_tail...
+++ apply IHl0; auto with *.
++ inversion H2...
(* goal: time proper *)
+ right. unfold time_proper_subset in *...
++ clear H1. clear H2. clear H3. clear gste.
  induction (steps measurement adversary G1); econstructor.
+++ destruct a.
   inversion H0; subst.  
   eapply find_time_helper;  eauto.
   clear IHl. clear H0. clear H2. clear H4. clear glab. 
    induction (steps measurement adversary G2); econstructor.
++++ destruct a.  unfold find_time. 
     destruct (label measurement adversary G2 (fst (s1, s2))) eqn:lab'; eauto.
     destruct (label measurement adversary G2 (snd (s1, s2))) eqn:lab''; eauto.
     simpl in *.
    specialize lab with s1 s2.
    specialize ste with s1 s2. simpl in *... clear IHl0.
    induction (steps measurement adversary G3)... inversion H1.
    simpl in *...
    econstructor. destruct a0; inversion H3... rewrite <- lab''. rewrite H4...
    rewrite <- lab'. rewrite H... 
    apply ex_tail...
++++ apply IHl0; auto with *.
+++ inversion H0...
++ apply H3. clear H1. clear H2. clear H0. clear H3.
   clear gste.
   induction (steps measurement adversary G2); econstructor.
+++ eapply find_time_helper; eauto. destruct a.
    unfold find_time. 
    destruct (label measurement adversary G2 (fst (s,s0))) eqn:lab'; eauto.
    destruct (label measurement adversary G2 (snd (s, s0))) eqn:lab''; eauto.
    specialize lab with s s0... simpl in *...
    specialize ste with s s0. simpl in *... clear IHl.  (* clear IHl0. clear H4. clear H.*)
    induction (steps measurement adversary G3).
    inversion H5. simpl in *. destruct H5.
    destruct a0. inversion H2. apply ex_head. rewrite <- lab'. rewrite H0...
    rewrite <- lab''. rewrite H3...
    apply ex_tail. eapply IHl0... auto with *.
    specialize glab with st1 st2. simpl in *...  
    specialize glab with st1 st2. simpl in *...
    inversion H; eauto.
+++ apply IHl; auto with *.
Qed.   


(**************************************
  PARTIAL ORDER OVER INDIVIDUAL GRAPHS 
  IS TRANSITIVE 
**************************************)
Theorem po_trans : forall G1 G2 G3, partial_order G1 G2 -> partial_order G2 G3 -> partial_order G1 G3.
Proof with intuition.
  unfold partial_order.
  intros. 
  destruct H as [isoG1G2 | spoG1G2].
  + destruct H0 as [isoG2G3 | spoG2G3 ].
  (* g1 = g2 /\ g2 = g3 *)
  ++ left. eapply bidir_homo_trans; eauto.
  (* g1 = g2 /\ g2 < g3 *)
  ++ right. eapply po_trans_helper; eauto.
  + destruct H0 as [isoG2G3 | spoG2G3 ].
  (* g1 < g2 /\ g2 = g3 *)
  ++ right. eapply po_trans_helper'; eauto.
  (* g1 < g2 /\ g2 < g3 *)
  ++  right. eapply spo_trans; eauto.
Qed. 


End PO_Facts.