
Require Import Coq.Lists.List.

Require Import Order.utilities.logics.
Require Import Order.utilities.ltacs.
Require Import Order.utilities.lists.
Require Import Order.utilities.existsb.
Require Import Order.utilities.labelSubsets.

Require Import Order.attacktree.

Section AttackTreeOrdering. 
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
        autounfold; intros A ev H; 
        induction (myEdges A);
        try (inversion H; fail);
        destruct a as [ev1 ev2]; simpl in *;
        destruct (myLabel A ev1), (myLabel A ev2);
        try (repeat right; auto; fail); 
        destruct H; subst; simpl; auto.
    Qed.


(** Convenient notations for set comparisons. *)

    Definition piSubset (A B : attacktree components) : Prop :=
        labelSubset (pi A) (pi B) (myLabel A) (myLabel B).
    Definition piSubset_fix (A B : attacktree components) : Prop :=
        labelSubset_fix (pi A) (pi B) (myLabel A) (myLabel B).
    Definition piProperSubset (A B : attacktree components) : Prop :=
        labelProperSubset (pi A) (pi B) (myLabel A) (myLabel B).
    Definition piProperSubset_fix (A B : attacktree components) : Prop :=
        labelProperSubset_fix (pi A) (pi B) (myLabel A) (myLabel B).
    Definition piSameset (A B : attacktree components) : Prop :=
        labelSameset (pi A) (pi B) (myLabel A) (myLabel B).
    Definition piSameset_fix (A B : attacktree components) : Prop :=
        labelSameset_fix (pi A) (pi B) (myLabel A) (myLabel B).
    Definition tauSubset (A B : attacktree components) : Prop :=
        labelSubset (tau A) (tau B) (myLabel A) (myLabel B).
    Definition tauSubset_fix (A B : attacktree components) : Prop :=
        labelSubset_fix (tau A) (tau B) (myLabel A) (myLabel B).
    Definition tauProperSubset (A B : attacktree components) : Prop :=
        labelProperSubset (tau A) (tau B) (myLabel A) (myLabel B).
    Definition tauProperSubset_fix (A B : attacktree components) : Prop :=
        labelProperSubset_fix (tau A) (tau B) (myLabel A) (myLabel B).
    Definition tauSameset (A B : attacktree components) : Prop :=
        labelSameset (tau A) (tau B) (myLabel A) (myLabel B).
    Definition tauSameset_fix (A B : attacktree components) : Prop :=
        labelSameset_fix (tau A) (tau B) (myLabel A) (myLabel B).

    Hint Unfold piSubset : core.
    Hint Unfold piProperSubset : core.
    Hint Unfold piSameset : core.
    Hint Unfold tauSubset : core.
    Hint Unfold tauProperSubset : core.
    Hint Unfold tauSameset : core.


(** The fixpoint and standard definitions are equivalent. *)
    Lemma piSubset_same : forall A B,
        piSubset_fix A B <-> piSubset A B.
    Proof.
        split; intros; apply labelSubset_same; auto.
    Qed.
    Lemma piProperSubset_same : forall A B,
        piProperSubset_fix A B <-> piProperSubset A B.
    Proof.
        split; intros; apply labelProperSubset_same; auto.
    Qed.
    Lemma piSameset_same : forall A B,
        piSameset_fix A B <-> piSameset A B.
    Proof.
        split; intros; apply labelSameset_same; auto.
    Qed.
    Lemma tauSubset_same : forall A B,
        tauSubset_fix A B <-> tauSubset A B.
    Proof.
        split; intros; apply labelSubset_same; auto.
    Qed.
    Lemma tauProperSubset_same : forall A B,
        tauProperSubset_fix A B <-> tauProperSubset A B.
    Proof.
        split; intros; apply labelProperSubset_same; auto.
    Qed.
    Lemma tauSameset_same : forall A B,
        tauSameset_fix A B <-> tauSameset A B.
    Proof.
        split; intros; apply labelSameset_same; auto.
    Qed.


(** Set comparisons are decidable. *)
    Lemma piSubsetDec : forall (A B : attacktree components),
        {piSubset_fix A B} + {~ piSubset_fix A B}.
    Proof. 
        intros; apply labelSubsetDec; apply myEqDec_labels; auto. 
    Qed.
    Lemma tauSubsetDec : forall (A B : attacktree components),
        {tauSubset_fix A B} + {~ tauSubset_fix A B}.
    Proof. 
        intros; apply labelSubsetDec; apply myEqDec_labels; auto. 
    Qed.






(** simeq (Equivalence)
 **
 ** Attack trees A and B are equivalent (i.e., A \simeq B)
 ** if and only if \pi(A) = \pi(B) and \tau(A) = \tau(B). *)

    Definition simeq (A B : attacktree components) : Prop :=
        piSameset A B /\ tauSameset A B.
    Definition simeq_fix (A B : attacktree components) : Prop :=
        piSameset_fix A B /\ tauSameset_fix A B.
    
    Hint Unfold simeq : core.

    Lemma simeq_same : forall A B,
        simeq_fix A B <-> simeq A B.
    Proof.
        intros; split; intros H; destruct H; split; apply labelSameset_same; auto.
    Qed.

    Theorem simeq_reflexive : forall A,
        simeq A A.
    Proof.
        intros A; repeat split; intros a H;
        exists a; auto.
    Qed.

    Theorem simeq_symmetric : forall A B,
        simeq A B ->
        simeq B A.
    Proof.
        intros A B H; destruct H as [H H0]; destruct H, H0;
        repeat split; intros a HIn; auto.
    Qed.

    Theorem simeq_transitive : forall A B C,
        simeq A B ->
        simeq B C ->
        simeq A C.
    Proof.
        intros A B C H H';
        destruct H as [H H0]; destruct H, H0;
        destruct H' as [H' H0']; destruct H', H0';
        repeat split; eapply labelSubset_transitive; eauto.
    Qed.

    Lemma simeqDec : forall (A B : attacktree components),
        {simeq_fix A B} + {~ simeq_fix A B}.
    Proof.
        intros; repeat apply conjunctionDec;
        try apply piSubsetDec;
        try apply tauSubsetDec.
    Qed.



(** prec (Strict partial order)
 **
 ** Attack tree A is strictly less than B (i.e., A \prec B)
 ** if and only if \pi(A) \subseteq \pi(B) and \tau(A) \subseteq \tau(B)
 ** and either \pi(A) \subset \pi(B) or \tau(A) \subset \tau(B). *)

    Definition prec (A B : attacktree components) : Prop :=
        piSubset A B /\ tauSubset A B /\ (piProperSubset A B \/ tauProperSubset A B).
    Definition prec_fix (A B : attacktree components) : Prop :=
        piSubset_fix A B /\ tauSubset_fix A B /\ (piProperSubset_fix A B \/ tauProperSubset_fix A B).

    Hint Unfold prec : core.

    Lemma prec_same : forall A B,
        prec_fix A B <-> prec A B.
    Proof.
        intros; split; intros H; 
        destruct H as [H H0]; destruct H0 as [H0 HP]; repeat split;
        try (apply labelSubset_same; auto);
        destruct HP; [left|right|left|right];
        apply labelProperSubset_same; auto.
    Qed.

    Theorem prec_irreflexive : forall A B,
        simeq A B ->
        ~ prec A B.
    Proof.
        intros A B H H';
        destruct H as [H H0]; destruct H; destruct H0;
        destruct H' as [H' H0']; destruct H0' as [H0' HP];
        destruct HP as [HP|HP]; destruct HP; contradiction.
    Qed.

    Theorem prec_asymmetric : forall A B,
        prec A B ->
        ~ prec B A.
    Proof.
        intros A B H H';
        destruct H as [H H0]; destruct H0 as [H0 HP];
        destruct H' as [H' H0']; destruct H0' as [H0' HP'];
        destruct HP as [HP|HP]; destruct HP; contradiction.
    Qed.

    Theorem prec_transitive : forall A B C,
        prec A B ->
        prec B C ->
        prec A C.
    Proof.
        intros A B C H H';
        destruct H as [H H0]; destruct H0 as [H0 HP];
        destruct H' as [H' H0']; destruct H0' as [H0' HP'];
        repeat split;
        try (eapply labelSubset_transitive; eauto);
        destruct HP; [left|right];
        eapply labelProperSubset_transitive1'; eauto.
    Qed.
    
    Lemma precDec : forall (A B : attacktree components),
        {prec_fix A B} + {~ prec_fix A B}.
    Proof.
        intros; repeat apply conjunctionDec;
        try (apply disjunctionDec; apply conjunctionDec);
        try apply negationDec;
        try apply piSubsetDec;
        try apply tauSubsetDec.
    Qed.


(** preceq (Partial order)
 **
 ** Attack tree A is less than or equal to B (i.e., A \preceq B)
 ** if and only if \pi(A) \subseteq \pi(B) and \tau(A) \subseteq \tau(B) *)

    Definition preceq (A B : attacktree components) : Prop :=
        piSubset A B /\ tauSubset A B.
    Definition preceq_fix (A B : attacktree components) : Prop :=
        piSubset_fix A B /\ tauSubset_fix A B.
    
    Hint Unfold preceq : core.

    Lemma preceq_same : forall A B,
        preceq_fix A B <-> preceq A B.
    Proof.
        intros; split; intros H; destruct H;
        split; apply labelSubset_same; auto.
    Qed.

    Theorem preceq_reflexive : forall A B,
        simeq A B ->
        preceq A B.
    Proof.
        intros A B H;
        destruct H as [H H0]; destruct H, H0;
        split; auto.
    Qed.
    
    Theorem preceq_antisymmetric : forall A B,
        preceq A B ->
        preceq B A ->
        simeq A B.
    Proof.
        intros A B H H';
        destruct H, H';
        repeat split; auto.
    Qed.

    Theorem preceq_transitive : forall A B C,
        preceq A B ->
        preceq B C ->
        preceq A C.
    Proof.
        intros A B C H H'; destruct H, H';
        split; eapply labelSubset_transitive; eauto.
    Qed.

    Lemma prec_simeq1 : forall A B C,
        simeq A B ->
        prec B C ->
        prec A C.
    Proof.
        intros A B C HAB HBC; 
        destruct HAB as [HAB HAB']; destruct HAB, HAB';
        destruct HBC as [HBC HBC']; destruct HBC' as [HBC' HBC''];
        repeat split;
        try (eapply labelSubset_transitive; eauto);
        destruct HBC''; [left|right];
        eapply labelProperSubset_transitive2'; eauto.
    Qed.

     Lemma prec_simeq2 : forall A B C,
        prec A B ->
        simeq B C ->
        prec A C.
    Proof.
        intros A B C HAB HBC; 
        destruct HAB as [HAB HAB']; destruct HAB' as [HAB' HAB''];
        destruct HBC as [HBC HBC']; destruct HBC, HBC';
        repeat split;
        try (eapply labelSubset_transitive; eauto);
        destruct HAB''; [left|right];
        eapply labelProperSubset_transitive1'; eauto.
    Qed.


    Lemma preceq_preceq : forall A B,
        preceq A B <->
        prec A B \/ simeq A B.
    Proof.
        intros A B; split; intros H. 
        - destruct H as [H H']; 
          destruct (piSubsetDec B A) as [Hp|Hp], (tauSubsetDec B A) as [Ht|Ht];
          rewrite piSubset_same in Hp; rewrite tauSubset_same in Ht;
          try (left; repeat split; auto; fail);
          right; split; auto.
        - destruct H as [H|H]; destruct H as [H H'];
          destruct H'; try destruct H; auto.
    Qed.

    Lemma preceqDec : forall (A B : attacktree components),
        {preceq_fix A B} + {~ preceq_fix A B}.
    Proof.
        intros; apply conjunctionDec;
        try apply piSubsetDec;
        try apply tauSubsetDec.
    Qed.
    
End AttackTreeOrdering. 