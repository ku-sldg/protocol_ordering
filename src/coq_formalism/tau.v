Require Import Coq.Lists.List.

Require Import Order.utilities.logics.
Require Import Order.utilities.ltacs.
Require Import Order.utilities.lists.
Require Import Order.utilities.existsb.
Require Import Order.utilities.labelSubsets.

Require Import Order.attacktree.
Require Import Order.pi.


Section Tau. 
    Context {components : Type}.
    
(** tau
 ** 
 ** The set of time-constrained adversary events in an attack tree. *)

    Fixpoint tau_helper {A : attacktree components} (edges : edgesT A) :
        list (eventT A) :=
    match edges with
    | (ev1, ev2) :: edges' => match (myLabel A ev1), (myLabel A ev2) with
                        | inl _, inr _ => ev2 :: (tau_helper edges')
                        | _, _ => tau_helper edges'
                        end
    | nil => nil
    end.

    Definition tau (A : attacktree components) : list (eventT A) :=
        tau_helper (myEdges A).

    Hint Unfold tau : core.

    Lemma tau_fact : forall A ev,
        In ev (tau A)
        <->
        (exists ev' meas, In (ev', ev) (myEdges A) /\ myLabel A ev' = inl meas) 
         /\ 
        (exists adv, myLabel A ev = inr adv).
    Proof.
        intros A ev; autounfold; split; intros H.
        - split; induction (myEdges A); try (inversion H; fail);
          destruct a as [ev1 ev2]; simpl in H;
          remember (myLabel A ev1) as Hl1; remember (myLabel A ev2) as Hl2;
          destruct Hl1, Hl2;
          try (destruct H; subst);
          try (apply IHl in H; destruct H as [ans H]; exists ans; auto);
          try (destruct H as [ans' H]; destruct H; exists ans'; simpl; auto).
        -- exists ev1, m; simpl; auto.
        -- exists a; auto.
        - destruct H as [HIn HAdv]; destruct HIn as [ev' HIn]; destruct HIn as [meas HIn];
          destruct HIn as [HIn HMeas]; destruct HAdv as [adv HAdv];
          induction (myEdges A); try (inversion HIn; fail).
          destruct a as [ev1 ev2]; destruct HIn; simpl.
        -- inv H; destruct (myLabel A ev'); destruct (myLabel A ev); inversion HAdv; inversion HMeas; simpl; auto.
        -- destruct (myLabel A ev1); destruct (myLabel A ev2); repeat right; apply IHl; auto.
    Qed.



(** Tau is a subset of Pi. *)

    Lemma tau_pi : forall A ev,
        In ev (tau A) ->
        In ev (pi A).
    Proof.
        unfold pi, tau; intros A ev H; 
        induction (myEdges A);
        try (inversion H; fail);
        destruct a as [ev1 ev2]; simpl in *;
        destruct (myLabel A ev1), (myLabel A ev2);
        try (repeat right; auto; fail); 
        destruct H; subst; simpl; auto.
    Qed.


(** Convenient notations for set comparisons. *)

    Definition tauSubset (A B : attacktree components) : Prop :=
        labelSubset (tau A) (tau B) (myLabel A) (myLabel B).
    Definition tauSubset_fix (A B : attacktree components) : Prop :=
        labelSubset_fix (myEqDec_labels A) (tau A) (tau B) (myLabel A) (myLabel B).
    Definition tauProperSubset (A B : attacktree components) : Prop :=
        labelProperSubset (tau A) (tau B) (myLabel A) (myLabel B).
    Definition tauProperSubset_fix (A B : attacktree components) : Prop :=
        labelProperSubset_fix (myEqDec_labels A) (tau A) (tau B) (myLabel A) (myLabel B).
    Definition tauSameset (A B : attacktree components) : Prop :=
        labelSameset (tau A) (tau B) (myLabel A) (myLabel B).
    Definition tauSameset_fix (A B : attacktree components) : Prop :=
        labelSameset_fix (myEqDec_labels A) (tau A) (tau B) (myLabel A) (myLabel B).

    Hint Unfold tauSubset : core.
    Hint Unfold tauProperSubset : core.
    Hint Unfold tauSameset : core.


(** The fixpoint and standard definitions are equivalent. *)
    Lemma tauSubset_same : forall A B,
        tauSubset_fix A B <-> tauSubset A B.
    Proof.
        split; intros; eapply labelSubset_same; eauto.
    Qed.
    Lemma tauProperSubset_same : forall A B,
        tauProperSubset_fix A B <-> tauProperSubset A B.
    Proof.
        split; intros; eapply labelProperSubset_same; eauto.
    Qed.
    Lemma tauSameset_same : forall A B,
        tauSameset_fix A B <-> tauSameset A B.
    Proof.
        split; intros; eapply labelSameset_same; eauto.
    Qed.


(** Set comparisons are decidable. *)
    Lemma tauSubsetDec : forall A B,
        {tauSubset_fix A B} + {~ tauSubset_fix A B}.
    Proof. intros; apply labelSubsetDec. Defined.
    Lemma tauProperSubsetDec : forall A B,
        {tauProperSubset_fix A B} + {~ tauProperSubset_fix A B}.
    Proof. intros; apply labelProperSubsetDec. Defined.
    Lemma tauSamesetDec : forall A B,
        {tauSameset_fix A B} + {~ tauSameset_fix A B}.
    Proof. intros; apply labelSamesetDec. Defined.

End Tau.