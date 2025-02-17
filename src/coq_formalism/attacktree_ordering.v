
Require Import Coq.Lists.List.

Require Import Order.utilities.logics.
Require Import Order.utilities.ltacs.
Require Import Order.utilities.lists.
Require Import Order.utilities.existsb.
Require Import Order.utilities.labelSubsets.

Require Import Order.attacktree.
Require Import Order.pi.
Require Import Order.tau.

Section AttackTreeOrdering. 
    Context {components : Type}.


(** simeq (Equivalence)
 **
 ** Attack trees A and B are equivalent (i.e., A \simeq B)
 ** if and only if \pi(A) = \pi(B) and \tau(A) = \tau(B). *)

    Definition simeq (A B : attacktree components) : Prop :=
        piSameset A B /\ tauSameset A B.

    Definition simeq_fix (A B : attacktree components) : Prop :=
        if (piSamesetDec A B)
        then if (tauSamesetDec A B)
             then True
             else False
        else False.
    
    Hint Unfold simeq : core.

    Lemma simeq_same : forall A B,
        simeq_fix A B <-> simeq A B.
    Proof.
        unfold simeq_fix; intros; split; intros H;
        destruct (piSamesetDec A B) as [Hp|Hp], (tauSamesetDec A B) as [Ht|Ht]; 
        auto; inversion H;
        [ split | | |];
        try apply Hp; try apply Ht;
        eapply labelSameset_same; eauto.
    Qed.

    Lemma simeqDec : forall (A B : attacktree components),
        {simeq_fix A B} + {~ simeq_fix A B}.
    Proof.
        intros; unfold simeq_fix; destruct (piSamesetDec A B), (tauSamesetDec A B); auto.
    Defined.

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





(** prec (Strict partial order)
 **
 ** Attack tree A is strictly less than B (i.e., A \prec B)
 ** if and only if \pi(A) \subseteq \pi(B) and \tau(A) \subseteq \tau(B)
 ** and either \pi(A) \subset \pi(B) or \tau(A) \subset \tau(B). *)

    Definition prec (A B : attacktree components) : Prop :=
        piSubset A B /\ tauSubset A B /\ (piProperSubset A B \/ tauProperSubset A B).

    Definition prec_fix (A B : attacktree components) : Prop :=
        if (piSubsetDec A B)
        then if (tauSubsetDec A B)
             then if (piProperSubsetDec A B)
                  then True
                  else if (tauProperSubsetDec A B)
                       then True
                  else False
             else False
        else False.

    Hint Unfold prec : core.

    Lemma prec_same : forall A B,
        prec_fix A B <-> prec A B.
    Proof.
        unfold prec_fix; intros; split; intros H.
        - destruct (piSubsetDec A B) as [Hp|Hp], 
                   (tauSubsetDec A B) as [Ht|Ht],
                   (piProperSubsetDec A B) as [Hp'|Hp'], 
                   (tauProperSubsetDec A B) as [Ht'|Ht'];
          try inversion H; repeat split; 
          try (eapply labelSubset_same; eauto; fail);
          try (left; eapply labelProperSubset_same; eauto; fail);
          try (right; eapply labelProperSubset_same; eauto; fail). 
        - destruct (piSubsetDec A B) as [Hp|Hp], 
                   (tauSubsetDec A B) as [Ht|Ht],
                   (piProperSubsetDec A B) as [HP|HP], 
                   (tauProperSubsetDec A B) as [HT|HT];
          destruct H as [Hp' H]; destruct H as [Ht' H]; auto;
          try (apply Hp; eapply labelSubset_same; eauto);
          try (apply Ht; eapply labelSubset_same; eauto);
          destruct H; [apply HP | apply HT]; eapply labelProperSubset_same; eauto.
    Qed.

    Lemma precDec : forall (A B : attacktree components),
        {prec_fix A B} + {~ prec_fix A B}.
    Proof.
        intros; unfold prec_fix; 
        destruct (piSubsetDec A B), (tauSubsetDec A B), 
                 (piProperSubsetDec A B), (tauProperSubsetDec A B); 
        auto.
    Defined.

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
        eapply labelProperSubset_transitive1; eauto.
    Qed.
    


(** preceq (Partial order)
 **
 ** Attack tree A is less than or equal to B (i.e., A \preceq B)
 ** if and only if \pi(A) \subseteq \pi(B) and \tau(A) \subseteq \tau(B) *)

    Definition preceq (A B : attacktree components) : Prop :=
        piSubset A B /\ tauSubset A B.

    Definition preceq_fix (A B : attacktree components) : Prop :=
        if (piSubsetDec A B) 
        then if (tauSubsetDec A B)
             then True
             else False
        else False.

    Hint Unfold preceq : core.

    Lemma preceq_same : forall A B,
        preceq_fix A B <-> preceq A B.
    Proof.
        unfold preceq_fix; intros; split; intros H;
         destruct (piSubsetDec A B) as [Hp|Hp], (tauSubsetDec A B) as [Ht|Ht];
         auto; inversion H;
         [split| | |];
         try apply Ht; try apply Hp;
         eapply labelSubset_same; eauto.
    Qed.

    Lemma preceqDec : forall (A B : attacktree components),
        {preceq_fix A B} + {~ preceq_fix A B}.
    Proof.
        intros; unfold preceq_fix; destruct (piSubsetDec A B), (tauSubsetDec A B); auto.
    Defined.

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
        eapply labelProperSubset_transitive2; eauto.
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
        eapply labelProperSubset_transitive1; eauto.
    Qed.


    Lemma preceq_preceq : forall A B,
        preceq A B <->
        prec A B \/ simeq A B.
    Proof.
        intros A B; split; intros H. 
        - destruct H as [H H'];
          destruct (labelSubsetDec (myEqDec_labels B) (pi B) (pi A) (myLabel B) (myLabel A)) as [Hp|Hp];
          destruct (labelSubsetDec (myEqDec_labels B) (tau B) (tau A) (myLabel B) (myLabel A)) as [Ht|Ht];
          rewrite labelSubset_same in Hp, Ht;
          try (right; repeat split; auto; fail);
          left; repeat split; auto; 
          try (left; repeat split; auto; fail);
          try (right; repeat split; auto; fail).
        - destruct H as [H|H]; destruct H as [H H'];
          destruct H'; try destruct H; auto.
    Qed.

    



(*


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
    Defined.



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
    Defined.


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
    Defined.
*)    
End AttackTreeOrdering. 