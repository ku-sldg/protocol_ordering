Require Import Coq.Lists.List.

Require Import Order.utilities.existsb.


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
    labelSubset_fix l m f g <-> labelSubset l m f g.
Proof.
    intros A B L l m f g; 
    split; intros H; induction l; simpl; auto.
    - intros a contra; inversion contra.
    - intros a0 HIn; destruct HIn; subst; destruct H;
      [apply existsb_exists | apply IHl]; auto.
    - split; [apply existsb_exists | apply IHl; intros a0 HIn]; 
      apply H; simpl; auto.
Qed.

Lemma labelSubsetDec : forall L,
    (forall (x y : L), {x = y} + {x <> y}) ->
    forall A B l m (f : A -> L) (g : B -> L),
    {labelSubset_fix l m f g} + {~ labelSubset_fix l m f g}.
Proof.
    intros L HDec A B l m f g; induction l; simpl; auto;
    pose proof existsbDec B (fun b => f a = g b) as exDec;
    assert (forall b, {f a = g b} + {f a <> g b}) as fgDec.
    { intros b; destruct (HDec (f a) (g b)); auto. }
    eapply exDec in fgDec; destruct fgDec, IHl;
    try (left; eauto; fail);
    try (right; intros contra; destruct contra; contradiction).
Qed.

Lemma labelSubset_transitive : forall A B C L l m n (f : A -> L) (g : B -> L) (h : C -> L),
    labelSubset l m f g ->
    labelSubset m n g h ->
    labelSubset l n f h.
Proof.
    intros A B C L l m n f g h H1 H2 a HIn;
    apply H1 in HIn; destruct HIn as [b HIn]; destruct HIn as [HIn HEq];
    apply H2 in HIn; rewrite <- HEq in HIn; auto.
Qed.



(* REMOVE THESE HERE *)
Lemma labelProperSubset_transitive1 : forall A B C L l m n (f : A -> L) (g : B -> L) (h : C -> L),
    labelSubset l m f g ->
    labelSubset m n g h ->
    ~ labelSubset m l g f ->
    ~ labelSubset n l h f.
Proof.
    intros A B C L l m n f g h H1 H2 HN contra;
    apply HN; clear HN; eapply labelSubset_transitive; eauto.
Qed.

Lemma labelProperSubset_transitive2 : forall A B C L l m n (f : A -> L) (g : B -> L) (h : C -> L),
    labelSubset l m f g ->
    labelSubset m n g h ->
    ~ labelSubset n m h g ->
    ~ labelSubset n l h f.
Proof.
    intros A B C L l m n f g h H1 H2 HN contra;
    apply HN; clear HN; eapply labelSubset_transitive; eauto.
Qed.





(** labelProperSubset *)

Definition labelProperSubset {A B L : Type} 
        (l : list A) (m : list B)
        (f : A -> L) (g : B -> L) :
    Prop :=
labelSubset l m f g /\ ~ labelSubset m l g f.

Definition labelProperSubset_fix {A B L : Type} 
        (l : list A) (m : list B)
        (f : A -> L) (g : B -> L) :
    Prop :=
labelSubset_fix l m f g /\ ~ labelSubset_fix m l g f.

Global Hint Unfold labelProperSubset : core.

Lemma labelProperSubset_same : forall A B L l m (f : A -> L) (g : B -> L),
    labelProperSubset_fix l m f g <-> labelProperSubset l m f g.
Proof.
    intros; split; intros H; destruct H as [H N];
    split; try (intros contra; apply N);
    apply labelSubset_same; auto.
Qed.

Lemma labelProperSubset_transitive1' : forall A B C L l m n (f : A -> L) (g : B -> L) (h : C -> L),
    labelProperSubset l m f g ->
    labelSubset m n g h ->
    labelProperSubset l n f h.
Proof.
    intros A B C L l m n f g h H1 H2; 
    destruct H1 as [H HN]; split;
    [ | intros contra; apply HN ];
    eapply labelSubset_transitive; eauto.
Qed.

Lemma labelProperSubset_transitive2' : forall A B C L l m n (f : A -> L) (g : B -> L) (h : C -> L),
    labelSubset l m f g ->
    labelProperSubset m n g h ->
    labelProperSubset l n f h.
Proof.
    intros A B C L l m n f g h H1 H2; 
    destruct H2 as [H HN]; split;
    [ | intros contra; apply HN ];
    eapply labelSubset_transitive; eauto.
Qed.



(** labelSameset *)

Definition labelSameset {A B L : Type} 
        (l : list A) (m : list B)
        (f : A -> L) (g : B -> L) :
    Prop :=
labelSubset l m f g /\ labelSubset m l g f.

Definition labelSameset_fix {A B L : Type} 
        (l : list A) (m : list B)
        (f : A -> L) (g : B -> L) :
    Prop :=
labelSubset_fix l m f g /\ labelSubset_fix m l g f.

Global Hint Unfold labelSameset : core.

Lemma labelSameset_same : forall A B L l m (f : A -> L) (g : B -> L),
    labelSameset_fix l m f g <-> labelSameset l m f g.
Proof.
    intros; split; intros H; destruct H;
    split; apply labelSubset_same; auto.
Qed.