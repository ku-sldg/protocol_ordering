Require Import Coq.Lists.List.

Require Import Order.attack_graph.
Require Import Order.graph_strict_partial_order.
Require Import Order.graph_normalization.
Require Import Order.graph_equiv.
Require Import Order.utilities.

Require Import Coq.Program.Equality.

Section Supports_Facts. 

Context {measurement : Type}.
Context {adversary : Type}.

(* Supports is a preorder when the attack tree equivalence 
  * relation is applied *) 
Definition supports_iso (SS : list (attackgraph measurement adversary)) (TT : list (attackgraph measurement adversary)) : Prop := 
    forall (H : (attackgraph measurement adversary)), In H TT ->
    (exists (G : (attackgraph measurement adversary)), In G SS /\ isomorphism G H).
    
    Theorem supports_iso_refl: forall x, supports_iso x x.
    Proof.
    intros. unfold supports_iso. intros.
    exists H. intuition.
    pose proof (iso_refl H). eauto.
    Qed.
    
    Theorem  supports_iso_trans : forall x y z, supports_iso x y -> supports_iso y z -> supports_iso x z.
    Proof.
    unfold supports_iso.
    intros X Y Z. intros HXY HYZ.
    intros A InAZ.
    specialize HYZ with A; intuition.
    destruct H as [B H].
    destruct H as [InBY H].
    specialize HXY with B. intuition.
    destruct H0 as [C H0].
    destruct H0 as [InCX H0]. 
    exists C; intuition.
    eapply iso_trans; eauto.
    Qed.
    
 
 (* Supports is a strict partial order when the strict partial order
  * over attack trees is applied 
 *)
  Definition supports_spo (SS : list (attackgraph measurement adversary)) (TT : list (attackgraph measurement adversary)) : Prop := 
    (forall (H : (attackgraph measurement adversary)), In H TT ->  
    (exists (G : (attackgraph measurement adversary)), In G SS /\ strict_partial_order G H)).

  (* supports is irreflexive for everything except nil. *)  
  Theorem supports_spo_irrefl :forall a, a <> nil -> ~ supports_spo a a.
  Proof.
    unfold supports_spo.
    intros a HNil contra.
    destruct a.
    (* a is nil *)
    - apply HNil. reflexivity.
    - clear HNil. generalize dependent a. induction a0.
    (* base case (a::nil)*)
    -- intros a contra. specialize contra with a. simpl in *. intuition.
      destruct H1. destruct H. destruct H; subst.
    --- pose proof (spo_irr x) as HIrr. contradiction.
    --- assumption.
    (* inductive case (a1 :: a :: a0) *)
    -- intros a1 contra. apply IHa0 with a1. intros HH HIn.
       pose proof (contra' := contra). specialize contra' with HH.
        simpl in contra'. intuition.
        simpl in HIn. intuition. 
    --- subst. destruct H3. destruct H. intuition. 
    ---- subst. exists x. auto with *.
    ---- subst. assert (contra' := contra). specialize contra with x.
         simpl in contra. intuition. destruct H3. destruct H3.
         intuition.
    ----- subst. exfalso. apply spo_asym  in H4. contradiction.
    ----- subst. exfalso. apply spo_irr in H4. destruct H4.
    ----- exists x0. intuition. eapply spo_trans; eauto.
    ---- exists x. intuition.
    --- destruct H3. destruct H2. intuition.
    ---- subst. exists x. intuition.
    ---- subst. assert (contra' := contra). specialize contra with x.
    simpl in contra. intuition. destruct H4. destruct H4.
    intuition.
  ----- subst.  exists x0. intuition. eapply spo_trans; eauto.
  ----- subst. exfalso. apply spo_irr in H5. destruct H5.
  ----- exists x0. intuition. eapply spo_trans; eauto.
  ---- exists x. intuition.
  Qed. 
  
  Theorem supports_spo_asym :forall x y, x <> nil -> supports_spo x y -> ~ supports_spo y x.
  Proof.
    unfold supports_spo. intros x y XNil Hxy Hyxcontra.
    destruct x.
    + apply XNil. reflexivity.
    + clear XNil. generalize dependent a. generalize dependent y. induction x.
    ++ intros ys y Hxy Hyxcontra. specialize Hyxcontra with y.
       simpl in *. intuition. destruct H1. destruct H; subst.
       clear H0. specialize Hxy with x.
       intuition. destruct H0. destruct H0.
       destruct H0. subst.
    +++ apply spo_asym in H2. contradiction. 
    +++ eauto.
    ++ intros ys y. intros Hxy Hyxcontra.
       apply IHx with ys y; clear IHx.
    +++ intros. eapply Hxy in H0. destruct H0.
        destruct H0. simpl in *.
        destruct H0.
    ++++ subst. exists x0. intuition.
    ++++ destruct H0. 
    +++++ subst. specialize Hyxcontra with x0. intuition.
          destruct H2. destruct H2. apply Hxy in H2. destruct  H2. destruct H2.
          intuition.
    ++++++ subst. exists x2. intuition. eapply spo_trans; eauto. eapply spo_trans; eauto.                       
    ++++++ subst. eapply spo_asym in H3. contradiction.
    ++++++ exists x2. intuition. eapply spo_trans; eauto. eapply spo_trans; eauto.
    +++++ exists x0; intuition.
    +++ intros. simpl in *. destruct H0.
    ++++ subst. assert (Hyxcontra' := Hyxcontra). specialize Hyxcontra' with H.
         intuition.
    ++++  assert (Hyxcontra' := Hyxcontra). specialize Hyxcontra' with H.
    intuition.
  Qed.    
    
  Theorem supports_spo_trans : forall x y z, supports_spo x y -> supports_spo y z -> supports_spo x z.
  Proof. 
  unfold supports_spo.
  intros X Y Z. intros HXY HYZ.
  intros A InAZ.
  specialize HYZ with A; intuition.
  destruct H as [B H].
  destruct H as [InBY H].
  specialize HXY with B. intuition.
  destruct H0 as [C H0].
  destruct H0 as [InCX H0]. exists C; intuition.
  pose proof (spo_trans C B A).
  eapply H1; eauto.   
  Qed.

End Supports_Facts. 