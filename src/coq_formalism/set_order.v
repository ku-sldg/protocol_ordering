(**** Defining support to compare sets of attack graphs. 
By: Anna Fritz and Sarah Johnson
Date: July 18, 2023 

Idea of supports motivated by Paul Rowe'e paper: 
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
Require Import Order.set_reduce.

Require Import Coq.Program.Equality.

(********** 
    SUPPORTS 
   
    CHASE analysis of a Copland Protocol generates 
    a set of graphs. We want to be able to compare 
    these sets of graphs so we introduce the idea 
    of supports as motivated by Rowe'e paper.
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
 Hypothesis eqDec_event : forall (G : attackgraph measurement adversary) (x y : G.(event _ _)), {x = y} + {x <> y}.

 (* if g1 < g2 then g1 cannot equal g2. Important sanity check that our definitions make sense. *)
 Theorem order_impl_not_eq : forall (g1 g2: attackgraph measurement adversary), strict_partial_order g1 g2 -> ~ isomorphism g1 g2.
 Proof.
    intros. unfold strict_partial_order in *. intros H0.
    assert (isomorphism g2 g1).
    { apply iso_sym. auto. }
    unfold isomorphism in *.
    destruct H0 as [f iso]. 
    destruct iso as [ste iso]. destruct iso as [lab iso]. destruct iso as [inj sur].
    destruct H1 as [g giso].
    destruct giso as [gste' giso]. destruct giso as [glab giso]. destruct giso as [ginj gsur].
    assert (forall st1 st2 : event measurement adversary g2,
            In (st1, st2) (edges measurement adversary g2) ->
            In (g st1, g st2) (edges measurement adversary g1)) as gste.
    { intros. apply gste'. auto. } clear gste'. clear ste. clear lab.
     intuition.
    + destruct H0. intuition. apply H1.
      clear H1. clear H2. clear H. clear H0. 
      induction (edges measurement adversary g2).    
    ++ econstructor.
    ++ econstructor.
    +++ unfold find_cor. 
        destruct (label measurement adversary g2 (fst a)) eqn:lab_g2; eauto. destruct a.
        specialize gste with e e0. simpl in *. intuition.
        clear H0. clear IHl.
        induction (edges measurement adversary g1).
    ++++ simpl in *. intuition.
    ++++ simpl in H1. destruct H1.
    +++++ destruct a. inversion H. econstructor.
          pose proof (glab e) as glabs.
          rewrite <- lab_g2. rewrite glabs. auto.
    +++++ apply ex_tail. apply IHl0. intuition.
    +++ apply IHl; auto with *.
    + destruct H0. intuition. apply H1.
      clear H1. clear H2. clear H0. clear H.
      induction (edges measurement adversary g2).    
    ++ econstructor.
    ++ econstructor.
    +++ unfold find_time. 
        destruct (label measurement adversary g2 (fst a)) eqn:lab_g2; eauto.
        destruct (label measurement adversary g2 (snd a)) eqn:lab_g22; eauto. 
        destruct a. specialize gste with e e0. simpl in *. intuition.
        clear H0. clear IHl.  
        induction (edges measurement adversary g1).
  ++++ simpl in *. intuition.
  ++++ simpl in H1. destruct H1.
  +++++ destruct a. inversion H. econstructor. intuition.
        pose proof (glab e0) as glabs0.
        rewrite <- lab_g22. rewrite glabs0. auto.
        pose proof (glab e) as glabs.
        rewrite <- lab_g2. rewrite glabs. auto.
  +++++ apply ex_tail. apply IHl0. intuition.
  +++ apply IHl; auto with *.
Qed.
 

(******************************* 
  SUPPORTS AS PREORDER 
********************************)

Definition supports (SS : list (attackgraph measurement adversary)) (TT : list (attackgraph measurement adversary)) : Prop := 
  forall (H : (attackgraph measurement adversary)), In H TT ->
(exists (G : (attackgraph measurement adversary)), In G SS /\ (isomorphism G H \/ strict_partial_order G H)).

Theorem supports_refl : forall SS,  supports SS SS.
Proof.
 intros. unfold supports. intros. exists H. split; intuition.  left.
 pose proof (iso_refl H).
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
  + left. eapply iso_trans;eauto.
  + right. eapply po_trans_helper; eauto.
  + right. eapply po_trans_helper'; eauto.
  + right. eapply spo_trans; eauto.
Qed.   


(******************************* 
  SUPPORTS WITH REDUCE SET
********************************)

Theorem getallchains_supports_y : forall x y y',
  getAllChains y y y' -> 
  supports x y ->
  supports x y'.
Proof.
  intros x y y' YChains Sup. unfold supports in *.
  intros H HIn'. eapply getallchains_in in HIn'; eauto.
Qed.

Theorem getallchains_supports_x : forall x y x',
  getAllChains x x x' ->
  x <> nil ->
  supports x y ->
  supports x' y.
Proof.
  intros x y x' HChains XCons Sup. 
  unfold supports in *. intros H HInY.
  pose proof HInY as HSup.
  apply Sup in HSup. clear Sup.
  destruct HSup as [G HSup]. destruct HSup as [GInX HLeq].
  pose proof (getallchains_result x x' HChains G GInX) as HRes.
  destruct HRes as [G' HRes]. destruct HRes as [G'InX' G'LeqG].
  exists G'. split; auto. eapply po_trans; eauto.
Qed.


(******************************* 
  SUPPORTS AS PARTIAL ORDER 
********************************)

(* supports is antisymmetric modulo set reduction *)
Theorem  supports_antisym : forall x y x' y', 
y <> nil -> x <> nil -> 
supports x y -> supports y x -> 
getAllChains x x x' -> getAllChains y y y' -> set_eq x' y'.
Proof.
  intros X Y. intros X' Y'.
  intros YNil XNil supXY supYX.
  intros chainsX' chainsY'.
  unfold set_eq.
  pose proof (getallchains_supports_x X Y X' chainsX' XNil supXY) as supX'Y.
  pose proof (getallchains_supports_y X' Y Y' chainsY' supX'Y) as supX'Y'.
  clear supXY supX'Y.
  pose proof (getallchains_supports_x Y X Y' chainsY' YNil supYX) as supY'X.
  pose proof (getallchains_supports_y Y' X X' chainsX' supY'X) as supY'X'.
  clear supYX supY'X.
  unfold supports in *. unfold supports_iso. split.
  - intros H HInY'. pose proof (supX'Y' H HInY'). 
    destruct H0 as [G H0]. destruct H0 as [GInX' GLeqH].
    destruct GLeqH as [GEqH | GLeH].
  -- exists G. auto.
  -- pose proof (supY'X' G GInX'). destruct H0 as [F H0].
    destruct H0 as [FInY' FLeqG].
    destruct FLeqG as [FEqG | FLeG].
  --- pose proof (po_trans_helper F G H).
      assert (isomorphism F G /\ strict_partial_order G H) by auto.
      apply H0 in H1. clear H0.
      pose proof (getallchains_not_spo Y Y' chainsY' F FInY' H HInY'). contradiction.
  --- assert (strict_partial_order F H).
      { eapply spo_trans; eauto. }
      pose proof (getallchains_not_spo Y Y' chainsY' F FInY' H HInY'). contradiction.
  - intros H HInX'. pose proof (supY'X' H HInX').
    destruct H0 as [G H0]. destruct H0 as [GInY' GLeqH].
    destruct GLeqH as [GEqH | GLeH].
  -- exists G. auto.
  -- pose proof (supX'Y' G GInY'). destruct H0 as [F H0].
     destruct H0 as [FInX' FLeqG].
     destruct FLeqG as [FEqG | FLeG].
  --- pose proof (po_trans_helper F G H).
      assert (isomorphism F G /\ strict_partial_order G H) by auto.
      apply H0 in H1. clear H0.
      pose proof (getallchains_not_spo X X' chainsX' F FInX' H HInX'). contradiction.
  --- assert (strict_partial_order F H).
      { eapply spo_trans; eauto. }
      pose proof (getallchains_not_spo X X' chainsX' F FInX' H HInX'). contradiction.
Qed.
 

End Supports_List.
