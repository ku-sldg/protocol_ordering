Require Import Coq.Lists.List.

Require Import Order.utilities.logics.
Require Import Order.utilities.ltacs.
Require Import Order.utilities.lists.
Require Import Order.utilities.existsb.
Require Import Order.utilities.labelSubsets.

Require Import Order.attacktree.


Section Pi. 
    Context {components : Type}.
    
(** pi 
 ** 
 ** The set of adversary events in an attack tree. *)

    Fixpoint piHelper {A : attacktree components} (edges : edgesT A) : 
        list (eventT A) :=
    match edges with
    | (ev1, ev2) :: edges' => match (myLabel A ev1), (myLabel A ev2) with
                              | inr _, inr _ => ev1 :: ev2 :: (piHelper edges')
                              | inr _, inl _ => ev1 :: (piHelper edges')
                              | inl _, inr _ => ev2 :: (piHelper edges')
                              | inl _, inl _ => piHelper edges'
                              end
    | nil => nil
    end.

    Definition pi (A : attacktree components) : list (eventT A) :=
        piHelper (myEdges A).

    Hint Unfold pi : core.

    Lemma pi_fact : forall A ev,
        In ev (pi A)
        <->
        (exists ev', In (ev, ev') (myEdges A) \/ In (ev', ev) (myEdges A)) 
         /\ 
        (exists adv, myLabel A ev = inr adv).
    Proof.
        intros A ev; autounfold; split; intros H.
        - split; induction (myEdges A); try (inversion H; fail);
          destruct a as [ev1 ev2]; simpl in H;
          remember (myLabel A ev1) as Hl1; remember (myLabel A ev2) as Hl2;
          destruct Hl1, Hl2;
          try (repeat destruct H; subst);
          try (apply IHl in H; destruct H as [ans H]; exists ans; simpl; destruct H; auto);
          try (exists ev1; simpl; auto; fail);
          try (exists ev2; simpl; auto; fail);
          try (exists a; auto; fail);
          try (exists a0; auto; fail).
        - destruct H as [HIn HAdv]; destruct HIn as [ev' HIn]; destruct HAdv as [adv HAdv];
          induction (myEdges A); try (destruct HIn as [HIn|HIn]; inversion HIn; fail);
          destruct a as [ev1 ev2]; destruct HIn; simpl; destruct H;
          try (inv H; destruct (myLabel A ev); destruct (myLabel A ev'); try (inversion HAdv; fail); simpl; auto);
          try (destruct (myLabel A ev1); destruct (myLabel A ev2); repeat right; apply IHl; auto).
    Qed.
        

(** Convenient notations for set comparisons. *)
    Definition piSubset (A B : attacktree components) : Prop :=
        labelSubset (pi A) (pi B) (myLabel A) (myLabel B).
    Definition piSubset_fix (A B : attacktree components) : Prop :=
        labelSubset_fix (myEqDec_labels A) (pi A) (pi B) (myLabel A) (myLabel B).
    Definition piProperSubset (A B : attacktree components) : Prop :=
        labelProperSubset (pi A) (pi B) (myLabel A) (myLabel B).
    Definition piProperSubset_fix (A B : attacktree components) : Prop :=
        labelProperSubset_fix (myEqDec_labels A) (pi A) (pi B) (myLabel A) (myLabel B).
    Definition piSameset (A B : attacktree components) : Prop :=
        labelSameset (pi A) (pi B) (myLabel A) (myLabel B).
    Definition piSameset_fix (A B : attacktree components) : Prop :=
        labelSameset_fix (myEqDec_labels A) (pi A) (pi B) (myLabel A) (myLabel B).

    Hint Unfold piSubset : core.
    Hint Unfold piProperSubset : core.
    Hint Unfold piSameset : core.


(** The fixpoint and standard definitions are equivalent. *)
    Lemma piSubset_same : forall A B,
        piSubset_fix A B <-> piSubset A B.
    Proof.
        split; intros; eapply labelSubset_same; eauto.
    Qed.
    Lemma piProperSubset_same : forall A B,
        piProperSubset_fix A B <-> piProperSubset A B.
    Proof.
        split; intros; eapply labelProperSubset_same; eauto.
    Qed.
    Lemma piSameset_same : forall A B,
        piSameset_fix A B <-> piSameset A B.
    Proof.
        split; intros; eapply labelSameset_same; eauto.
    Qed.

(** Set comparisons are decidable. *)
    Lemma piSubsetDec : forall A B,
        {piSubset_fix A B} + {~ piSubset_fix A B}.
    Proof. intros; apply labelSubsetDec. Defined.
    Lemma piProperSubsetDec : forall A B,
        {piProperSubset_fix A B} + {~ piProperSubset_fix A B}.
    Proof. intros; apply labelProperSubsetDec. Defined.
    Lemma piSamesetDec : forall A B,
        {piSameset_fix A B} + {~ piSameset_fix A B}.
    Proof. intros; apply labelSamesetDec. Defined.

End Pi.