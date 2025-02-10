Require Import Coq.Lists.List.


(** existsb 
 ** 
 ** Determine whether a function can be satisfied
 ** by an element of the list. *)

Fixpoint existsb_fix {A : Type} (f : A -> Prop) (l : list A) : Prop := 
match l with 
| a::l' => f a \/ existsb_fix f l'
| nil => False
end.

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
Qed.


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
