Require Import Coq.Lists.List.

Require Import Order.attack_graph.
Require Import Order.parameterized_graph_strict_partial_order.
Require Import Order.parameterized_graph_partial_order.
Require Import Order.graph_normalization.
Require Import Order.graph_equiv.
Require Import Order.utilities.

(********************************
 * Reduce a set of attack trees
 * to its easiest attacks

    parameterized over 
    an arbitrary adversary 
    event ordering
 *********************************)

Section Parameterized_Set_Reduce. 

Context {measurement : Type}.
Context {adversary : Type}.
 Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
 Hypothesis eqDec_adversary : forall (x y : adversary), {x = y} + {x <> y}.
 Hypothesis eqDec_event : forall (G : attackgraph measurement adversary) (x y : G.(event _ _)), {x = y} + {x <> y}.

 (* Attack tree ordering is parameterized over an adversary event ordering *)
 Context {adv_event_spo : adversary -> adversary -> Prop}.

 (* The ordering is a strict partial order *)
 Hypothesis adv_event_spo_irrefl : forall (x : adversary), ~ adv_event_spo x x.
 Hypothesis adv_event_spo_asym : forall (x y : adversary), adv_event_spo x y -> ~ adv_event_spo y x.
 Hypothesis adv_event_spo_trans : forall (x y z : adversary), adv_event_spo x y -> adv_event_spo y z -> adv_event_spo x z.
 
 Let strict_partial_order := @strict_partial_order measurement adversary adv_event_spo.


 (** Given the original set orig and an attack tree a,
    find an attack tree in orig that is 
        minimal with respect to orig and
        less than a
    Follows a chain of attack trees in orig
        a > a' > a'' > ... > minimal element
*)
(* Called "minimal" in the paper *)
Inductive getChain (orig : list (attackgraph measurement adversary)) (a : (attackgraph measurement adversary)) : (attackgraph measurement adversary) -> Prop :=
| set_keep_chain : (forall a2, In a2 orig -> ~ strict_partial_order a2 a) -> getChain orig a a
| set_remove_chain : forall a2 a', In a2 orig -> strict_partial_order a2 a -> getChain orig a2 a' -> getChain orig a a'.

(** The nth attack tree of the resulting list is
        less than the nth element of the input list and
        minimal with respect to the original list
*)
(* Called "min" in the paper *)
Inductive getAllChains (orig : list (attackgraph measurement adversary)): list (attackgraph measurement adversary) -> list (attackgraph measurement adversary) -> Prop :=
| nil_case : getAllChains orig nil nil
| cons_case : forall a a' l l', getChain orig a a' -> getAllChains orig l l' -> getAllChains orig (a :: l) (a'::l').


(* Various helpful lemmas *)

Lemma getchain_in : forall x a a',
  getChain x a a' ->
  In a x ->
  In a' x.
Proof.
  intros x a a' HChain HIn. induction HChain.
  - assumption.
  - apply IHHChain. assumption.
Qed.

Theorem getallchains_getchain : forall orig x x', 
    getAllChains orig x x' ->
    forall a', In a' x' ->
    exists a, In a x /\ getChain orig a a'.
Proof.
  intros orig x x' HChains a' HIn'.
  induction HChains.
  - inversion HIn'.
  - destruct HIn' as [HIn'|HIn'].
  -- subst. exists a. auto with *.
  -- apply IHHChains in HIn'. destruct HIn' as [a2 HIn]. destruct HIn as [HIn HChain].
     exists a2. auto with *.
Qed.

Theorem getallchains_in : forall x x', 
  getAllChains x x x' ->
  forall a', In a' x' ->
  In a' x.
Proof.
  intros x x' HChains a' HIn'.
  assert (exists a, In a x /\ getChain x a a').
  { eapply getallchains_getchain; eauto. }
  destruct H as [a H]. destruct H as [HIn HChain].
  eapply getchain_in; eauto.
Qed.

Lemma getchain_leq : forall x a a', 
  getChain x a a' ->
  (isomorphism a' a) \/ (strict_partial_order a' a).
Proof.
  intros x a a' HChain. induction HChain.
  - left. apply iso_refl.
  - right. destruct IHHChain as [HIso | HSpo].
  -- eapply po_trans_helper; eauto.
  -- eapply spo_trans; eauto.
Qed. 

Theorem getallchains_remove : forall orig x x',
  getAllChains orig x x' ->
  forall g, In g x -> ~(In g x') ->
  exists g2, (In g2 orig /\ (strict_partial_order g2 g)).
Proof.
  intros orig x x' HChains g Inx NInx'.
  induction HChains.
  - inversion Inx.
  - destruct Inx.
  -- subst. clear IHHChains. inversion H; subst.
  --- exfalso. apply NInx'. auto with *.
  ---  exists a2. auto with *.
  -- apply IHHChains; auto with *.
Qed.


Lemma getallchains_getchain' : forall orig x x',
  getAllChains orig x x' ->
  forall g, In g x ->
  exists g', In g' x' /\ getChain orig g g'.
Proof.
  intros orig x x' HChains g Inx.
  induction HChains.
  - inversion Inx.
  - destruct Inx.
  -- subst. exists a'. auto with *.
  -- apply IHHChains in H0. destruct H0 as [g' H0]. destruct H0 as [HIn' HChain].
     exists g'. auto with *.
Qed.

Theorem getallchains_result : forall x x',
  getAllChains x x x' ->
  forall g, In g x ->
  exists g', (In g' x' /\ (isomorphism g' g \/ strict_partial_order g' g)).
Proof.
  intros x x' HChains g Inx.
  assert (exists g', In g' x' /\ getChain x g g') as HChain.
  { eapply getallchains_getchain'; eauto. }
  destruct HChain as [g' HChain]. destruct HChain as [Inx' HChain].
  apply getchain_leq in HChain.
  exists g'. auto with *.
Qed.

Lemma getchain_keep : forall orig a a',
  getChain orig a a' ->
  forall g, In g orig ->
  ~ strict_partial_order g a'.
Proof.
  intros orig a a' HChain g Inorig contra.
  induction HChain.
  - specialize H with g. apply H in Inorig. contradiction.
  - apply IHHChain. assumption.
Qed.

Theorem getallchains_keep : forall orig x x',
  getAllChains orig x x' ->
  forall g', In g' x' ->
  forall g, In g orig ->
  ~ strict_partial_order g g'.
Proof.
  intros orig x x' HChains g' Inx' g Inorig contra.
  induction HChains.
  - inversion Inx'.
  - destruct Inx'.
  -- subst. clear IHHChains. eapply getchain_keep; eauto.
  -- apply IHHChains. auto.
Qed.

Theorem getallchains_not_spo : forall x x',
  getAllChains x x x' ->
  forall g1, In g1 x' ->
  forall g2, In g2 x' ->
  ~ (strict_partial_order g1 g2).
Proof.
  intros x x' HChains g1 In1 g2 In2 contra.
  pose proof (getallchains_in x x' HChains g1 In1) as Inorig.
  pose proof (getallchains_keep x x x' HChains g2 In2 g1 Inorig).
  contradiction.
Qed.

End Parameterized_Set_Reduce.