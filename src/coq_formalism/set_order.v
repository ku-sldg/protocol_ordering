(**** Defining support to compare sets of attack graphs. 
By: Anna Fritz and Sarah Johnson
Date: July 18, 2023 

Idea of supports motivated by Paul Rowe's paper: 
"On Orderings in Security Models" *)

Require Import Coq.Lists.List.

Require Import Order.attack_graph.
Require Import Order.graph_strict_partial_order.
Require Import Order.graph_normalization.
Require Import Order.graph_equiv.
Require Import Order.utilities.
Require Import Order.graph_partial_order.
Require Import Order.supports_facts.
Require Import Order.set_equiv.

Require Import Coq.Program.Equality.

(********** 
    SUPPORTS 
   
    CHASE analysis of a Copland Protocol generates 
    a set of graphs. We want to be able to compare 
    these sets of graphs so we introduce the idea 
    of supports as motivated by Rowe's paper.
    *********)

(********************************
 * OUR IMPLEMENTATION OF SUPPORTS 
 * FOR LISTS OF ATTACK GRAPHS 
 *********************************)

Section Supports_List. 

Context {measurement : Type}.
Context {adversary : Type}.

 (* Labels and States must have decidable equality *)
 Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
 Hypothesis eqDec_adversary : forall (x y : adversary), {x = y} + {x <> y}.
 Hypothesis eqDec_state : forall (G : attackgraph measurement adversary) (x y : G.(state _ _)), {x = y} + {x <> y}.

 (* if g1 < g2 then g1 cannot equal g2. Important sanity check that our definitions make sense. *)
 Theorem order_impl_not_eq : forall (g1 g2: attackgraph measurement adversary), strict_partial_order g1 g2 -> ~ bidir_homo g1 g2.
 Proof.
    intros. unfold bidir_homo, strict_partial_order in *. intuition.
    + destruct H as [fg1g2]. destruct H3 as [fg2g1]. destruct H1.
      unfold homomorphism in *. destruct H as [fsteps flab]. destruct H2 as [gsteps glab]. intuition. apply H3.
      clear H4. clear H1. clear H3. clear fsteps. clear flab.
      clear H0.
      induction (steps measurement adversary g2).    
    ++ econstructor.
    ++ econstructor.
    +++ unfold find_cor. 
        destruct (label measurement adversary g2 (fst a)) eqn:lab_g2; eauto. destruct a.  specialize glab with s s0. specialize gsteps with s s0. simpl in *. intuition.
        clear H0. clear H2. clear IHl. clear H4.  
        induction (steps measurement adversary g1).
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
    induction (steps measurement adversary g2).    
  ++ econstructor.
  ++ econstructor.
  +++ unfold find_time. 
      destruct (label measurement adversary g2 (fst a)) eqn:lab_g2; eauto.  
      destruct (label measurement adversary g2 (snd a)) eqn:lab_g22; eauto. destruct a.  specialize glab with s s0. specialize gsteps with s s0. simpl in *. intuition.
      clear H0. clear H2. clear IHl.  
      induction (steps measurement adversary g1).
  ++++ simpl in *. intuition.
  ++++ simpl in H1. destruct H1.
  +++++ destruct a. inversion H0. econstructor. intuition.
        rewrite <- lab_g22. rewrite H4. eauto.
        rewrite <- lab_g2. rewrite H. eauto.
  +++++ apply ex_tail. apply IHl0. intuition.
  +++ apply IHl; auto with *.
 Qed.   
 

(******************************* 
  SUPPORTS AS PREORDER 
********************************)

Definition supports (SS : list (attackgraph measurement adversary)) (TT : list (attackgraph measurement adversary)) : Prop := 
  forall (H : (attackgraph measurement adversary)), In H TT ->
(exists (G : (attackgraph measurement adversary)), In G SS /\ (bidir_homo G H \/ strict_partial_order G H)).

Theorem supports_refl : forall SS,  supports SS SS.
Proof.
 intros. unfold supports. intros. exists H. split; intuition.  left.
 pose proof (bidir_homo_refl H).
 eauto.  
Qed.

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
  + left. eapply bidir_homo_trans;eauto.
  + right. eapply po_trans_helper; eauto.
  + right. eapply po_trans_helper'; eauto.
  + right. eapply spo_trans; eauto.
Qed.   


Theorem  supports_antisym : forall x y,
supports x y -> supports y x -> set_eq x y.
Proof.
  intros; unfold supports in *. simpl in *. induction x.
  Abort.


(* FUTURE WORK 
   Not included in Fritz Dissertation work *)
(*****************************
 graph_normalization SET TO EASIEST GRAPHS 
*****************************)

Inductive reduce_set (orig : list (attackgraph measurement adversary)) : list (attackgraph measurement adversary) ->  list (attackgraph measurement adversary) -> Prop :=
| set_nil : reduce_set orig nil nil
(* there does not exist anything that is less than a1 *)
| set_keep : forall a1 SS TT, (forall a2, In a2 orig -> ~ strict_partial_order a2 a1) -> reduce_set orig SS TT -> reduce_set orig (a1 :: SS) (a1 :: TT) 
(* set_remove case causes problems *)
| set_remove : forall a1 SS TT, (exists a2, In a2 orig /\ strict_partial_order a2 a1) -> reduce_set orig SS TT -> reduce_set orig (a1 :: SS) TT. 

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
-- exists H. split; auto with *. left. apply bidir_homo_refl.
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
 

End Supports_List.
