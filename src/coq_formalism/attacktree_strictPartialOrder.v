
(*************************
 ** STRICT PARTIAL ORDER 
 ** OVER INDIVIDUAL ATTACK TREES 
 ** $\prec$
 **
 ** An attack tree is strictly worse than another
 ** if it requires strictly less work to perform
 ** by an adversary.
 **
 ** Defines and computes two sets: (1) the set of 
 ** adversary events $\pi$ and (2) the set of time-
 ** contrained adversary events $\tau$.
 ** 
 ** Only compare attack trees with common sets of both
 ** adversary events and time-contrained adversary events. *)



Require Import Coq.Lists.List.

Require Import Order.utilities.ltacs.
Require Import Order.utilities.lists.
Require Import Order.utilities.existsb.
Require Import Order.utilities.labelSubsets.

Require Import Order.attacktree.
Require Import Order.attacktree_normalization.
Require Import Order.attacktree_equivalence.


Section AttackTreeStrictPartialOrder. 
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

    Definition piSubset (A B : attacktree components) : Prop :=
        labelSubset (pi A) (pi B) (myLabel A) (myLabel B).
    Definition piSubset_fix (A B : attacktree components) : Prop :=
        labelSubset_fix (pi A) (pi B) (myLabel A) (myLabel B).

    Definition piProperSubset (A B : attacktree components) : Prop :=
        piSubset A B /\ ~ piSubset B A.
    Definition piProperSubset_fix (A B : attacktree components) : Prop :=
        piSubset_fix A B /\ ~ piSubset_fix B A.

    Hint Unfold pi : core.
    Hint Unfold piSubset : core.
    Hint Unfold piProperSubset : core.

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


    Lemma pi_isomorphism : forall A B,
        isomorphism A B ->
        piSubset A B.
    Proof.
        intros A B HIso; destruct_iso HIso;
        unfold injective, surjective, edgePreserving, labelPreserving in *;
        intros a H; exists (f a); split.
        - apply pi_fact; apply pi_fact in H;
          destruct H as [HIn HAdv]; destruct HIn as [ev' HIn];
          split.
        -- exists (f ev'); destruct HIn; [left|right]; apply HEdg; auto.
        -- destruct HAdv as [adv HAdv]; exists adv; rewrite <- HLab; auto.
        - apply HLab.
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

    Definition tauSubset (A B : attacktree components) : Prop :=
    labelSubset (tau A) (tau B) (myLabel A) (myLabel B).
    Definition tauSubset_fix (A B : attacktree components) : Prop :=
    labelSubset_fix (tau A) (tau B) (myLabel A) (myLabel B).

    Definition tauProperSubset (A B : attacktree components) : Prop :=
    tauSubset A B /\ ~ tauSubset B A.
    Definition tauProperSubset_fix (A B : attacktree components) : Prop :=
    tauSubset_fix A B /\ ~ tauSubset_fix B A.


    Hint Unfold tau : core.
    Hint Unfold tauSubset : core.
    Hint Unfold tauProperSubset : core.

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


    Lemma tau_isomorphism : forall A B,
        isomorphism A B ->
        tauSubset A B.
    Proof.
        intros A B HIso; destruct_iso HIso;
        unfold injective, surjective, edgePreserving, labelPreserving in *;
        intros a H; exists (f a); split.
        - apply tau_fact; apply tau_fact in H.
          destruct H as [HIn HAdv]; 
          destruct HIn as [ev' HIn]; destruct HIn as [meas HIn];
          split.
        -- exists (f ev'), meas; rewrite <- HEdg; rewrite <- HLab; auto.
        -- destruct HAdv as [adv HAdv]; exists adv; rewrite <- HLab; auto.
        - apply HLab.
    Qed.


(** Tau is a subset of Pi *)

    Lemma tau_pi : forall A ev,
        In ev (tau A) ->
        In ev (pi A).
    Proof.
        autounfold.
        intros A ev H. induction (myEdges A);
        try (inversion H; fail);
        destruct a as [ev1 ev2]; simpl in *;
        destruct (myLabel A ev1), (myLabel A ev2);
        try (repeat right; auto; fail); 
        destruct H; subst; simpl; auto.
    Qed.




(** strictlyLessWork *)

    Definition strictlyLessWork (A B : attacktree components) : Prop :=
        (piProperSubset A B /\ tauSubset A B) \/ (piSubset A B /\ tauProperSubset A B).
    Definition strictlyLessWork_fix (A B : attacktree components) : Prop :=
        (piProperSubset_fix A B /\ tauSubset_fix A B) \/ (piSubset_fix A B /\ tauProperSubset_fix A B).





(** Strictly Less Work is a strict partial order. *)

    Theorem strictlyLessWork_irreflexive : forall (A B : attacktree components),
        isomorphism A B ->
        ~ strictlyLessWork A B.
    Proof.
        intros A B H HSub;
        pose proof isomorphism_symmetric H as H0;
        pose proof H as H1; pose proof H0 as H2;
        apply pi_isomorphism in H, H0; apply tau_isomorphism in H1, H2;
        destruct HSub as [HSub|HSub]; destruct HSub as [HPi HTau];
        [ destruct HPi | destruct HTau ]; contradiction.
    Qed.


    Theorem strictlyLessWork_asymmetric : forall (A B : attacktree components),
        strictlyLessWork A B ->
        ~ strictlyLessWork B A.
    Proof.
        intros A B HAB HBA;
        destruct HAB as [HAB|HAB], HBA as [HBA|HBA];
        destruct HAB as [H1 H2], HBA as [H3 H4];
        try destruct H1; try destruct H2; try destruct H3; try destruct H4;
        contradiction.
    Qed.


    Theorem strictlyLessWork_transitive : forall A B C,
        strictlyLessWork A B ->
        strictlyLessWork B C ->
        strictlyLessWork A C.
    Proof.
        unfold strictlyLessWork; intros A B C HAB HBC;
        destruct HAB as [HAB|HAB], HBC as [HBC|HBC];
        destruct HAB as [H1 H2], HBC as [H3 H4];
        try destruct H1; try destruct H2; try destruct H3; try destruct H4.
        - left; repeat split;
          try (eapply labelSubset_transitive; eauto);
          eapply labelProperSubset_transitive1; eauto.
        - left; repeat split;
          try (eapply labelSubset_transitive; eauto);
          intros H5; assert (piSubset B A).
          { eapply labelSubset_transitive; eauto. }
          contradiction.
        - left; repeat split;
          try (eapply labelSubset_transitive; eauto);
          intros H5; assert (piSubset C B).
          { eapply labelSubset_transitive; eauto. }
          contradiction.
        - right; repeat split; 
          try (eapply labelSubset_transitive; eauto);
          eapply labelProperSubset_transitive1; eauto.
    Qed.

 
 End AttackTreeStrictPartialOrder.