(*************************
 ** PARTIAL ORDER 
 ** OVER INDIVIDUAL ATTACK TREES 
 ** $\preceq$
 **
 ** An attack tree is the same or worse than another
 ** if it is isomorphic or requires strictly less work 
 ** to perform by an adversary. *)

Require Import Coq.Lists.List.

Require Import Order.utilities.ltacs.
Require Import Order.utilities.lists.
Require Import Order.utilities.existsb.
Require Import Order.utilities.labelSubsets.

Require Import Order.attacktree.
Require Import Order.attacktree_normalization.
Require Import Order.attacktree_equivalence.
Require Import Order.attacktree_strictPartialOrder.


Section AttackTreePartialOrder.
    Context {components : Type}.

    Definition sameOrLessWork (A B : attacktree components) :=
        isomorphism A B \/ strictlyLessWork A B.
    
    Hint Unfold sameOrLessWork : core.

    Theorem sameOrLessWork_reflexive : forall A B,
        isomorphism A B ->
        sameOrLessWork A B.
    Proof.
        intros; auto.
    Qed.

    Theorem sameOrLessWork_antisymmetric : forall A B,
        sameOrLessWork A B ->
        sameOrLessWork B A ->
        isomorphism A B.
    Proof.
        intros A B HAB HBA; destruct HAB, HBA; auto;
        [ apply isomorphism_symmetric | exfalso; eapply strictlyLessWork_asymmetric ]; eauto.
    Qed.

    Theorem sameOrLessWork_transitive : forall A B C,
        sameOrLessWork A B ->
        sameOrLessWork B C ->
        sameOrLessWork A C.
    Proof.
        intros A B C HAB HBC; 
        destruct HAB as [HAB|HAB], HBC as [HBC|HBC].
        - left; eapply isomorphism_transitive; eauto.
        - right; pose proof HAB as HAB';
          apply pi_isomorphism in HAB; apply tau_isomorphism in HAB';
          destruct HBC as [HBC|HBC]; destruct HBC as [HBC HBC'];
          [ destruct HBC; left | destruct HBC'; right ];
          repeat split;
          try (eapply labelSubset_transitive; eauto);
          eapply labelProperSubset_transitive2; eauto.
        - right; pose proof HBC as HBC';
          apply pi_isomorphism in HBC; apply tau_isomorphism in HBC';
          destruct HAB as [HAB|HAB]; destruct HAB as [HAB HAB'];
          [ destruct HAB; left | destruct HAB'; right ];
          repeat split;
          try (eapply labelSubset_transitive; eauto);
          eapply labelProperSubset_transitive1; eauto.
        - right; eapply strictlyLessWork_transitive; eauto.
    Qed.

End AttackTreePartialOrder.