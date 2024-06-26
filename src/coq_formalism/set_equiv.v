(******************************
SET EQUIVALENCE   

* Equivalence over sets of graphs 
* We define this as each graph supports each other *)

Require Import Coq.Lists.List.

Require Import Order.attack_graph.
Require Import Order.graph_strict_partial_order.
Require Import Order.graph_normalization.
Require Import Order.graph_equiv.
Require Import Order.utilities.
Require Import Order.graph_partial_order.
Require Import Order.supports_facts.

Require Import Coq.Program.Equality.

Section Set_Equiv. 

Context {measurement : Type}.
Context {adversary : Type}.

Definition set_eq (SS : list (attackgraph measurement adversary)) (TT : list (attackgraph measurement adversary)) :=  supports_iso SS TT /\ supports_iso TT SS.

(* Prove properties of equivalence relation 
* reflexivity 
* symmetry
* transitivity *)

Theorem set_eq_refl : forall SS, set_eq SS SS .
Proof.
    intros. unfold set_eq; split;
    apply supports_iso_refl.     
Qed.

Theorem set_eq_sym : forall SS TT, set_eq SS TT -> set_eq TT SS.
Proof.
    intros. unfold set_eq in *; split; destruct H; intuition.
Qed.

Theorem set_eq_trans : forall SS TT, set_eq SS TT -> forall PP, set_eq TT PP -> set_eq SS PP.
Proof. 
    unfold set_eq in *. intros SS TT seteqSSTT. destruct seteqSSTT as [seteqSSTT seteqTTSS]. intros PP.
    intros seteqTTPP. destruct seteqTTPP as [seteqTTPP seteqPPTT].
    split.
    + eapply supports_iso_trans; eauto.
    + eapply supports_iso_trans; eauto.
Qed.

(* TODO: Prove that our equivalence relation is decidable *)
Theorem set_eq_dec : forall SS TT, TT <> nil -> {set_eq SS TT} + {~ set_eq SS TT}.
Proof.
    intros. destruct TT.
    + exfalso. apply H. reflexivity.
    + clear H. generalize dependent a. induction TT.
    ++ intros. unfold set_eq. unfold supports_iso.
Abort. 

End Set_Equiv. 