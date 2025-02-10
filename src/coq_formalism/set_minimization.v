Require Import Coq.Lists.List.

Require Import Order.utilities.ltacs.
Require Import Order.utilities.lists.
Require Import Order.utilities.existsb.
Require Import Order.utilities.labelSubsets.

Require Import Order.attacktree.
Require Import Order.attacktree_ordering.


(** Given a set of attack trees P and an attack tree A,
 ** find an attack tree in P that is less than A and
 ** minimal with respect to P.
 **
 ** Follow a chain of attack trees in P such that
 ** A > A' > A'' > ... > some minimal element. *)

Section Minimization. 
  Context {components : Type}.


(** minimal
 ** 
 ** An element A is minimal with respect to a set P
 ** if and only if B is not strictly less than A for
 ** every B in P. *)

    Definition minimal (A : attacktree components) P : Prop :=
        forall A', In A' P -> ~ prec A' A.

    Fixpoint minimal_fix (A : attacktree components) P : Prop :=
    match P with
    | A' :: P' => ~ prec_fix A' A /\ minimal_fix A P'
    | nil => True 
    end.

    Inductive minimal_ind A :
        list (attacktree components) -> Prop :=
    | minimalCons : forall A' P',
        ~ prec A' A ->
        minimal_ind A P' ->
        minimal_ind A (A'::P')
    | minimalNil :
        minimal_ind A nil.

    Hint Unfold minimal : core.

    Lemma minimal_same : forall A P,
        minimal_fix A P <->  minimal_ind A P.
    Proof.
        intros A P; split; intros H.
        - induction P; constructor; simpl in H; destruct H; auto;
          rewrite <- prec_same; auto.
        - induction H; simpl; try (split; [rewrite prec_same|]); auto.
    Qed.

    Lemma minimal_same' : forall A P,
        minimal_fix A P <-> minimal A P.
    Proof.
        intros A P; split; intros H.
        - intros A' HIn; induction P;
          try (inversion HIn; fail);
          destruct H; destruct HIn; subst;
          [ rewrite <- prec_same | apply IHP ]; auto.
        - induction P; simpl; auto;
          split; [ rewrite prec_same | apply IHP; intros A' HIn ];
          apply H; simpl; auto.
    Qed.
        



(** getMinimal
 ** 
 ** Gets an element A' such that A' is less than A 
 ** and A' is minimal with respect to P. *)

    Fixpoint getMinimal_fix A P : attacktree components :=
    match P with
    | A' :: P' => if (precDec A' A)
                  then getMinimal_fix A' P'
                  else getMinimal_fix A P'
    | nil => A 
    end.

    Inductive getMinimal_ind : 
        attacktree components -> list (attacktree components) -> attacktree components -> Prop :=
    | getMinimalPrec : forall A P' A' A'',
        prec A' A ->
        getMinimal_ind A' P' A'' ->
        getMinimal_ind A (A' :: P') A''
    | getMinimalNotPrec : forall A P' A' A'',
        ~ prec A' A ->
        getMinimal_ind A P' A'' ->
        getMinimal_ind A (A' :: P') A''
    | getMinimalNil : forall A,
        getMinimal_ind A nil A.


    Lemma getMinimal_same : forall A P A',
        getMinimal_fix A P = A' <->
        getMinimal_ind A P A'.
    Proof.
        intros A P A'; split; intros H.
        - generalize dependent A'; generalize dependent A; 
          induction P; intros; simpl in *;
          try (subst; apply getMinimalNil);
          destruct (precDec a A); apply IHP in H;
          [ apply getMinimalPrec | apply getMinimalNotPrec ]; auto;
          rewrite <- prec_same; auto.
        - induction H; simpl; subst; auto;
          destruct (precDec A' A) as [Hp|Hp]; auto;
          [ apply prec_same in H | apply prec_same in Hp ]; contradiction.
    Qed.


    Lemma getMinimal_preceq : forall A P A',
        getMinimal_ind A P A' ->
        preceq A' A.
    Proof.
        intros A P A' H; apply preceq_preceq; 
        induction H; auto.
        - left; destruct IHgetMinimal_ind;
          [ eapply prec_transitive | eapply prec_simeq1 ]; eauto.
        - right; apply simeq_reflexive.
    Qed.


    Lemma getMinimal_minimal : forall A P A',
        getMinimal_ind A P A' ->
        minimal_ind A' P.
    Proof.
        intros A P A' H; induction H; constructor; auto;
        apply getMinimal_preceq in H0; apply preceq_preceq in H0.
        - destruct H0; 
          [ apply prec_asymmetric 
          | apply prec_irreflexive; apply simeq_symmetric ]; 
          auto.
        - intros contra; apply H; destruct H0;
          [ eapply prec_transitive
          | eapply prec_simeq2 ]; 
          eauto.
    Qed.


    Lemma getMinimal_in : forall A P A',
        getMinimal_ind A P A' ->
        In A' P \/ A' = A.
    Proof.
        intros A P A' HMin; induction HMin; auto;
        destruct IHHMin; subst; simpl; auto.
    Qed.


(** min
 **
 ** Produces a set containing minimal attack trees.
 **
 ** Furthermore, the nth element of min(P) is less
 ** than the nth element of P and is minimal with
 ** respect to P. *)

    Fixpoint min_fix Q P : list (attacktree components) :=
    match P with
    | A'::P' => (getMinimal_fix A' Q) :: (min_fix Q P')
    | nil => nil
    end.

    Inductive min_ind Q :
        list (attacktree components) -> list (attacktree components) -> Prop :=
    | minCons : forall A' A'' P' P'',
        getMinimal_ind A' Q A'' ->
        min_ind Q P' P'' ->
        min_ind Q (A'::P') (A''::P'')
    | minNil : 
        min_ind Q nil nil.


    Lemma min_same : forall Q P P',
        min_fix Q P = P' <->
        min_ind Q P P'.
    Proof.
        intros Q P P'; split; intros H.
        - generalize dependent P'; induction P; intros;
          simpl in H; subst; constructor;
          [ apply getMinimal_same | apply IHP ]; auto.
        - induction H; simpl; auto;
          apply getMinimal_same in H; subst; auto.
    Qed.


    Lemma min_getMinimal' : forall Q P P',
        min_ind Q P P' ->
        forall A, In A P ->
        exists A', In A' P' /\ getMinimal_ind A Q A'.
    Proof.
        intros Q P P' HMin A HIn;
        induction HMin; inversion HIn; subst.
        -- exists A''; split; simpl; auto.
        -- apply IHHMin in H0; destruct H0 as [A''' H0]; destruct H0;
           exists A'''; split; simpl; auto.
    Qed.

    Lemma min_preceq : forall P P',
        min_ind P P P'->
        forall A, In A P ->
        exists A', In A' P' /\ preceq A' A.
    Proof.
        intros P P' HMin A HIn;
        pose proof (min_getMinimal' P P P' HMin A HIn) as H;
        destruct H as [A' H]; destruct H as [H H'];
        apply getMinimal_preceq in H';
        exists A'; split; auto.
    Qed.


    Lemma min_getMinimal : forall Q P P',
        min_ind Q P P' ->
        forall A', In A' P' ->
        exists A, In A P /\ getMinimal_ind A Q A'.
    Proof.
        intros Q P P' HMin A' HIn; induction HMin;
        try (inversion HIn; fail);
        destruct HIn as [|HIn]; subst;
        [ eexists; split; simpl; eauto 
        | apply IHHMin in HIn; destruct HIn as [A HIn]; destruct HIn;
          exists A; split; simpl; auto ].
    Qed.


    Lemma min_in : forall P P',
        min_ind P P P' ->
        forall A', In A' P' ->
        In A' P.
    Proof.
        intros P P' HMin A' HIn; eapply min_getMinimal in HMin; eauto;
        destruct HMin as [A HMin]; destruct HMin as [HMin HGet];
        apply getMinimal_in in HGet; destruct HGet; subst; auto.
    Qed.


    Lemma min_minimal : forall P P',
        min_ind P P P' ->
        forall A', In A' P' ->
        minimal_ind A' P.
    Proof.
        intros P P' HMin A' HIn';
        pose proof (min_getMinimal P P P' HMin A' HIn') as HGet;
        destruct HGet as [A HGet]; destruct HGet;
        eapply getMinimal_minimal; eauto.
    Qed.

End Minimization. 


(*

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

*)