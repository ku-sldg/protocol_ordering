Require Import Coq.Lists.List.

Require Import Order.utilities.ltacs.
Require Import Order.utilities.lists.
Require Import Order.utilities.existsb.
Require Import Order.utilities.labelSubsets.
Require Import Order.utilities.supports.

Require Import Order.attacktree.
Require Import Order.attacktree_ordering.
Require Import Order.set_minimization.



Section SetOrdering. 
    Context {components : Type}.

(** equiv (Equivalence)
 **
 ** Sets of attack trees P and Q are equivalent (i.e., P \equiv Q)
 ** if and only if they are the same set. *)

    Definition equiv (P Q : list (attacktree components)) : Prop :=
        supports simeq P Q /\ supports simeq Q P.

    Hint Unfold equiv : core.

    Definition equiv_fix (P Q : list (attacktree components)) : Prop :=
        supports_fix simeq_fix simeqDec P Q /\ supports_fix simeq_fix simeqDec Q P.


    Lemma equiv_same : forall P Q,
        equiv_fix P Q <->
        equiv P Q.
    Proof.
        intros P Q; split; intros HEq;
        destruct HEq as [HST HTS].
        - split; intros B HIn;
          apply supports_same in HST, HTS;  
          [ apply HST in HIn | apply HTS in HIn ];
          destruct HIn as [A]; exists A; rewrite <- simeq_same; auto.
        - split; apply supports_same; intros B HIn;
          [ apply HST in HIn | apply HTS in HIn ];
          destruct HIn as [A]; exists A; rewrite simeq_same; auto.
    Qed.


    Theorem equiv_reflexive : forall P,
        equiv P P.
    Proof.
        intros; split; apply supports_reflexive; apply simeq_reflexive.
    Qed. 

    Theorem equiv_symmetric : forall P Q,
        equiv P Q ->
        equiv Q P.
    Proof.
        intros P Q HEq; destruct HEq; split; auto.
    Qed.

    Theorem equiv_transitive : forall P Q R,
        equiv P Q ->
        equiv Q R ->
        equiv P R.
    Proof.
        intros P Q R HST HTU; destruct HST, HTU; split; 
        eapply supports_transitive; eauto; apply simeq_transitive.
    Qed.



(** leq (Partial order)
 **
 ** Set of attack trees P is less than or equal to Q (i.e., P \leq Q)
 ** if and only if P supports Q under the preceq relation. *)

    Definition leq (P Q : list (attacktree components)) : Prop :=
        supports preceq P Q.

    Hint Unfold leq : core.

    Definition leq_fix (P Q : list (attacktree components)) : Prop :=
        supports_fix preceq_fix preceqDec P Q.


    Lemma leq_same : forall P Q,
        leq_fix P Q <->
        leq P Q.
    Proof.
        intros P Q; split; intros HLeq; 
        [ apply supports_same in HLeq | apply supports_same ]; 
        intros B HIn; apply HLeq in HIn; destruct HIn as [A];
        exists A; [ rewrite <- preceq_same | rewrite preceq_same ]; auto.
    Qed.


    Theorem leq_reflexive : forall P Q,
        equiv P Q ->
        leq P Q.
    Proof.
        intros P Q HEq B HIn; destruct HEq as [HST];
        apply HST in HIn; destruct HIn as [A HIn]; destruct HIn;
        exists A; split; auto; apply preceq_reflexive; auto.
    Qed.

    Theorem leq_transitive : forall P Q R,
        leq P Q ->
        leq Q R ->
        leq P R.
    Proof.
        intros P Q R HST HTU; eapply supports_transitive; eauto; apply preceq_transitive.
    Qed.


    Lemma min_leq1 : forall P P',
        min_ind P P P' ->
        leq P' P.
    Proof.
        intros P P' HMin B HIn; eapply min_preceq; eauto.
    Qed.

    Lemma min_leq2 : forall P P',
        min_ind P P P' ->
        leq P P'.
    Proof.
        intros P P' HMin B HIn; exists B; split;
        [ eapply min_in; eauto | apply preceq_reflexive; apply simeq_reflexive ].
    Qed.

    Lemma leq_min1 : forall P Q P',
        leq P Q ->
        min_ind P P P' ->
        leq P' Q.
    Proof.
        intros P Q P' HLeq HMin;
        apply min_leq1 in HMin;
        eapply leq_transitive; eauto.
    Qed.

    Lemma leq_min2 : forall P Q Q',
        leq P Q ->
        min_ind Q Q Q' ->
        leq P Q'.
    Proof.
        intros P Q Q' HLeq HMin B HIn; apply HLeq; eapply min_in; eauto.
    Qed.


    Theorem leq_antisymmetric : forall P Q P' Q',
        leq P Q ->
        leq Q P ->
        min_ind P P P' ->
        min_ind Q Q Q' ->
        equiv P' Q'.
    Proof.
        intros P Q P' Q' HLeqPQ HLeqQP HMinP HMinQ;
        assert (leq P' Q') as HPQ by
        ( pose proof (min_leq1 P P' HMinP); pose proof (min_leq2 Q Q' HMinQ);
          eapply leq_transitive; eauto; eapply leq_transitive; eauto );
        assert (leq Q' P') as HQP by 
        ( pose proof (min_leq1 Q Q' HMinQ); pose proof (min_leq2 P P' HMinP);
          eapply leq_transitive; eauto; eapply leq_transitive; eauto );
        clear HLeqPQ HLeqQP; split;
        intros A' HIn; pose proof HIn as HIn';
        [ apply HPQ in HIn' | apply HQP in HIn' ];
        destruct HIn' as [B' HIn']; destruct HIn' as [HIn' HOrd];
        apply preceq_preceq in HOrd; destruct HOrd.
        - exfalso; 
          apply HQP in HIn'; destruct HIn' as [A HIn']; destruct HIn' as [HIn' HOrd];
          apply preceq_preceq in HOrd; destruct HOrd;
          [ assert (prec A A') as contra by (eapply prec_transitive; eauto)
          | assert (prec A A') as contra by (eapply prec_simeq1; eauto) ];
          pose proof (min_minimal Q Q' HMinQ A' HIn) as HMin;
          apply minimal_same in HMin; apply minimal_same' in HMin;
          unfold minimal, not in HMin;  
          eapply HMin; eauto; eapply min_in; eauto.
        - exists B'; auto.
        - exfalso; 
          apply HPQ in HIn'; destruct HIn' as [A HIn']; destruct HIn' as [HIn' HOrd];
          apply preceq_preceq in HOrd; destruct HOrd;
          [ assert (prec A A') as contra by (eapply prec_transitive; eauto)
          | assert (prec A A') as contra by (eapply prec_simeq1; eauto) ];
          pose proof (min_minimal P P' HMinP A' HIn) as HMin;
          apply minimal_same in HMin; apply minimal_same' in HMin;
          unfold minimal, not in HMin;  
          eapply HMin; eauto; eapply min_in; eauto.
        - exists B'; auto.
    Qed.
    

End SetOrdering. 