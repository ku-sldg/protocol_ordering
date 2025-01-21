
Require Import Coq.Lists.List.




Ltac inv H := inversion H; subst; clear H.

(** If two lists are equal, then there lengths are equal. *)
Lemma listEq_length : forall {A : Type} (l m : list A),
    l = m ->
    length l = length m.
Proof.
    intros A l m H; 
    destruct l; subst; auto.
Qed.


(** removeFirst 
 ** 
 ** Removes the first occurence of x in l. *)
Fixpoint removeFirst {A : Type} 
        (eq_dec : forall x y : A, {x = y}+{x <> y}) 
        (x : A) 
        (l : list A) {struct l} : 
    list A :=
match l with
| y::l' => if (eq_dec x y) then l' else y::(removeFirst eq_dec x l')
| nil => nil
end.


Lemma removeFirst_lengthAdd : forall A eq_dec x (l : list A),
    In x l ->
    length (removeFirst eq_dec x l) + 1 = length l.
Proof.
    intros A eq_dec x l HIn; 
    induction l; [inversion HIn|]; simpl;
    destruct (eq_dec x a) as [Heqx|Heqx]; subst.
    - rewrite PeanoNat.Nat.add_1_r; auto.
    - destruct HIn as [HIn|HIn]; subst; simpl.
    -- exfalso; apply Heqx; auto.
    -- apply IHl in HIn; rewrite <- HIn; auto.
Qed.

Lemma removeFirst_lengthSub : forall A eq_dec x (l : list A),
    In x l ->
    length (removeFirst eq_dec x l) = length l - 1.
Proof.
    intros A eq_dec x l HIn; 
    induction l; [inversion HIn|]; simpl;
    destruct (eq_dec x a) as [Heqx|Heqx]; subst.
    - rewrite PeanoNat.Nat.sub_0_r; auto.
    - destruct HIn as [HIn|HIn]; subst; simpl.
    -- exfalso; apply Heqx; auto.
    -- assert (exists n, length l = S n) as Hl.
    { destruct l; [inversion HIn | simpl; exists (length l); auto]. }
    apply IHl in HIn; rewrite HIn;
    destruct Hl as [n Hl]; rewrite Hl;
    simpl; rewrite PeanoNat.Nat.sub_0_r; auto.
Qed.


(** existsb 
 ** 
 ** Determine whether a function can be satisfied
 ** by an element of the list. *)

Fixpoint existsb_fix {A : Type} (f : A -> Prop) (l : list A) : Prop := 
match l with 
| a::l' => f a \/ existsb_fix f l'
| nil => False
end.

Inductive existsb_ind {A : Type} (f : A -> Prop) : list A -> Prop :=
| exHead : forall a l, f a -> existsb_ind f (a::l)
| exTail : forall a l, existsb_ind f l -> existsb_ind f (a::l).


Lemma existsb_same : forall A f (l : list A), 
    existsb_fix f l <-> existsb_ind f l.
Proof.
    intros A f l; split; intros H.
    - induction l; simpl in *; inversion H;
      [apply exHead | apply exTail]; auto.
    - induction H; simpl; auto.
Qed.

Lemma existsb_exists : forall A f (l : list A), 
    existsb_fix f l <-> exists a, In a l /\ f a.
Proof.
    intros A f l; split; intros H; induction l; simpl;
    inversion H; firstorder; subst; auto.
Qed.


Lemma existsb_incl : forall A f (l m  : list A), 
    existsb_fix f l -> 
    incl l m -> 
    existsb_fix f m.
Proof.
    intros A f l m HEx HIncl;
    apply existsb_exists in HEx;
    destruct HEx as [a HEx];
    destruct HEx as [HIn Hf];
    apply existsb_exists; exists a; 
    split; [apply HIncl|]; auto.
Qed.



(** labelSubset
 ** 
 ** Given two lists and associated labeling functions,
 ** determine whether for every element in the first
 ** list there is an element in the second with the
 ** same label. *)

Definition labelSubset {A B L : Type} 
        (l : list A) (m : list B)
        (f : A -> L) (g : B -> L) :
    Prop :=
forall a, In a l -> exists b, In b m /\ f a = g b.

Fixpoint labelSubset_fix {A B L : Type} 
        (l : list A) (m : list B)
        (f : A -> L) (g : B -> L) :
    Prop := 
match l with
| a::l' => (existsb_fix (fun b => f a = g b) m) /\ labelSubset_fix l' m f g
| nil => True
end.

Global Hint Unfold labelSubset : core.

Lemma labelSubset_same : forall A B L l m (f : A -> L) (g : B -> L),
    labelSubset l m f g <-> labelSubset_fix l m f g.
Proof.
    intros A B L l m f g; 
    split; intros H; induction l; simpl; auto.
    - split; [apply existsb_exists | apply IHl; intros a0 HIn]; 
      apply H; simpl; auto.
    - intros a contra; inversion contra.
    - intros a0 HIn; destruct HIn; subst; destruct H;
      [apply existsb_exists | apply IHl]; auto.
Qed.

Lemma labelSubset_trans : forall A B C L l m n (f : A -> L) (g : B -> L) (h : C -> L),
    labelSubset l m f g ->
    labelSubset m n g h ->
    labelSubset l n f h.
Proof.
    intros A B C L l m n f g h H1 H2 a HIn;
    apply H1 in HIn; destruct HIn as [b HIn]; destruct HIn as [HIn HEq];
    apply H2 in HIn; rewrite <- HEq in HIn; auto.
Qed.

Lemma labelProperSubset_trans : forall A B C L l m n (f : A -> L) (g : B -> L) (h : C -> L),
    labelSubset l m f g ->
    ~ labelSubset m l g f ->
    labelSubset m n g h ->
    ~ labelSubset n m h g ->
    ~ labelSubset n l h f.
Proof.
    intros A B C L l m n f g h H1 N1 H2 N2 contra.
    assert (~ (labelSubset m l g f \/ labelSubset n m h g)) as H.
    { intros H; destruct H; auto. }
    apply H; left; eapply labelSubset_trans; eauto.
Qed.

(** labelProperSubset *)
(*
Definition labelProperSubset {A B L : Type} 
        (l : list A) (m : list B)
        (f : A -> L) (g : B -> L) :
    Prop :=
labelSubset l m f g /\ ~ labelSubset m l g f.

Global Hint Unfold labelProperSubset : core.

Lemma labelProperSubset_exists : forall A B L l m (f : A -> L) (g : B -> L),
    labelProperSubset l m f g ->
    exists b, In b m /\  (forall a, In a l -> f a <> g b).
Proof.
    unfold labelProperSubset, labelSubset. intros A B L l m f g H.
    destruct H as [HSub HNot].

*)