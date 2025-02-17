Require Import Coq.Lists.List.


(** existsb 
 ** 
 ** Determine whether a function can be satisfied
 ** by an element of the list. *)


Fixpoint existsb_fix {A : Type} 
        (f : A -> Prop) (fDec : forall x, {f x} + {~f x}) (l : list A) : 
    Prop := 
match l with 
| a::l' => if (fDec a)
           then True
           else existsb_fix f fDec l'
| nil => False
end.

Inductive existsb_ind {A : Type} (f : A -> Prop) : list A -> Prop :=
| exHead : forall a l, f a -> existsb_ind f (a::l)
| exTail : forall a l, existsb_ind f l -> existsb_ind f (a::l).


Lemma existsbDec : forall {A} f fDec,
    forall (l : list A), {existsb_fix f fDec l} + {~existsb_fix f fDec l}.
Proof.
    intros A f fDec l; induction l; simpl; auto.
    destruct (fDec a).
    - left; auto.
    - destruct IHl.
    -- left; auto.
    -- right; auto.
Defined.


Lemma existsb_same : forall A f fDec (l : list A), 
    existsb_fix f fDec l <-> existsb_ind f l.
Proof.
    intros A f fDec l; split; intros H.
    - induction l.
    -- simpl in *. inversion H.
    -- simpl in *. destruct (fDec a).
    --- apply exHead. auto.
    --- apply exTail. auto.
    - induction H; simpl; destruct (fDec a); auto. contradiction.
Qed.

Lemma existsb_exists : forall A f fDec (l : list A), 
    existsb_fix f fDec l <-> exists a, In a l /\ f a.
Proof.
    intros A f fDec l; split; intros H; induction l; simpl in *.
    - contradiction.
    - destruct (fDec a); firstorder.
    - firstorder.
    - destruct (fDec a).
    -- auto.
    -- destruct H as [a' H]. destruct H as [H n']. destruct H; subst.
    --- contradiction.
    --- apply IHl. eauto.
Qed.


Lemma existsb_incl : forall A f fDec (l m  : list A), 
    existsb_fix f fDec l -> 
    incl l m -> 
    existsb_fix f fDec m.
Proof.
    intros A f fDec l m HEx HIncl;
    apply existsb_exists in HEx;
    destruct HEx as [a HEx];
    destruct HEx as [HIn Hf];
    apply existsb_exists; exists a; 
    split; [apply HIncl|]; auto.
Qed.


(*
Fixpoint existsb_fix {A : Type} (f : A -> Prop) (l : list A) : Prop := 
match l with 
| a::l' => f a \/ existsb_fix f l'
| nil => False
end.

Inductive existsb_ind {A : Type} (f : A -> Prop) : list A -> Prop :=
| exHead : forall a l, f a -> existsb_ind f (a::l)
| exTail : forall a l, existsb_ind f l -> existsb_ind f (a::l).


Lemma existsbDec : forall A f,
    (forall (x : A), {f x} + {~ f x}) ->
    forall (l : list A), {existsb_fix f l} + {~existsb_fix f l}.
Proof.
    intros A f HDec l; induction l; simpl; auto.
    destruct (HDec a).
    - left; left; auto.
    - destruct IHl.
    -- left; right; auto.
    -- right; intros contra; destruct contra; contradiction.
Defined.


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

*)
