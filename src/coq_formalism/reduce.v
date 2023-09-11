(******************************
    Trying to reduce graph before comparison 

    Assumptions 
    1. Measurement events are not predicatable by an adversary
    2. Adversary does not know future measurement events 
    
    By: Anna Fritz and Sarah Johnson
    Date: Sept 11, 2023 *)

Require Import Coq.Lists.List.

(* TODO prove eq_list is an equivalence relation *)
(* currently unused *)
(*
Definition eq_list {A : Type} (l1 l2 : list A) : Prop :=
    forall a, In a l1 <-> In a l2.
*)
(* TODO define an equivalence relation over attackgraphs
        that considers labels and shapes *)
(* Isomorphism most likely *)


Record attackgraph (measurement corruption : Type) : Type := 
{
    state : Type ;
    steps : list (state * state) ;
    label : state -> measurement + corruption
}.



Section Reducer.

Context {measurement : Type}.
Context {corruption : Type}.
Context {G : attackgraph measurement corruption}.

(* Labels and States must have decidable equality *)
Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
Hypothesis eqDec_corruption : forall (x y : corruption), {x = y} + {x <> y}.
Hypothesis eqDec_state : forall (x y : G.(state _ _)), {x = y} + {x <> y}.

Lemma eqDec_step : forall (x y : G.(state _ _) * G.(state _ _)), {x = y} + {x <> y}.
Proof.
    intros x y;
    destruct x as [stx stx']; destruct y as [sty sty'].
    destruct eqDec_state with (x:=stx) (y:=sty);
    destruct eqDec_state with (x:=stx') (y:=sty');
    try (right; intros contra; rewrite pair_equal_spec in contra; destruct contra; contradiction).
    - subst; left; rewrite pair_equal_spec; split; reflexivity.
Qed.

(*
Lemma eqDec_steps : forall (x y : list (G.(state _ _) * G.(state _ _))), {x = y} + {x <> y}.
Proof.
    induction x as [|x lx]; induction y as [|y ly].
    - left. reflexivity.
    - right. intros contra; inversion contra.
    - right. intros contra; inversion contra.
    - pose proof eqDec_step. destruct X with (x:=x) (y:=y).
    -- subst. Admitted.
*)


(* Replace all occurences of st by st' in Steps *)
Fixpoint replace_measurement (Steps : list (G.(state _ _) * G.(state _ _))) (st st' : G.(state _ _)) : 
list (G.(state _ _) * G.(state _ _)) :=
match Steps with
| (st1, st2) :: Steps' => 
    if (eqDec_state st1 st)
    then if (eqDec_state st2 st)
            then (st', st') :: replace_measurement Steps' st st'
            else (st', st2) :: replace_measurement Steps' st st'
    else if (eqDec_state st2 st)
            then (st1, st') :: replace_measurement Steps' st st'
            else (st1, st2) :: replace_measurement Steps' st st'
| nil => Steps
end.

Inductive replace_measurement' (st st' : G.(state _ _)) : list (G.(state _ _) * G.(state _ _)) -> list (G.(state _ _) * G.(state _ _)) -> Prop :=
| TheEnd : replace_measurement' st st' nil nil
| TheMid : replace_measurement' st st' ((st,st)::nil) nil.

Print replace_measurement'.

(* Find a step from a measurement event to a measurement event in Steps
    Remove that step from AllSteps
    Call replace_measurement 
    
 * AllSteps -- passed around. this contains all of the steps 
 * Steps -- graph recursed on *)
Fixpoint find_measurement (AllSteps Steps : list (G.(state _ _) * G.(state _ _))) : list (G.(state _ _) * G.(state _ _)) := 
match Steps with
| (st1, st2) :: Steps' =>
    match (G.(label _ _) st1) with
    | inl m1 => 
        match (G.(label _ _) st2) with
        | inl m2 =>
            (* if m1 and m2 are measurement labels *)
            replace_measurement (remove eqDec_step (st1, st2) AllSteps) st1 st2
        (* recurse when m1 is a measurement event but not m2 *)
        | _ => find_measurement AllSteps Steps'
        end
    (* m1 is not a measurement event *)
    | _ => find_measurement AllSteps Steps'
    end
(* *)
| nil => AllSteps
end.

(* caller
 * takes in list of steps  *)
Definition reduce1 (Steps : list (G.(state _ _) * G.(state _ _))) : list (G.(state _ _) * G.(state _ _)) :=
    find_measurement Steps Steps.

(* main function would take in whole attack graph... this is a problem as a fixpoint *)

(* Should use different list equality maybe *)

Inductive reducer : list (G.(state _ _) * G.(state _ _)) -> list (G.(state _ _) * G.(state _ _)) -> Prop :=
| r : forall Steps,
    Steps = reduce1 Steps ->
    reducer Steps Steps
| t : forall Steps Steps',
    Steps <> reduce1 Steps ->
    reducer (reduce1 Steps) Steps' ->
    reducer Steps Steps'.

Lemma test : forall Steps,
    exists Steps', reducer Steps Steps'.
Abort.

End Reducer.



(* *********** *)
(* Example m3b *)
(* *********** *)
(* *********** *)


Section Reducer.

Inductive measurement : Type :=
| ms : measurement
| ms4 : measurement.

Inductive corruption : Type :=
| sys : corruption
| ker : corruption.

Inductive state_m3b : Type :=
| s : state_m3b 
| k : state_m3b
| m : state_m3b
| m4 : state_m3b.

Definition label_m3b (st : state_m3b) : measurement + corruption :=
match st with
| s => inr sys
| k => inr ker
| m => inl ms
| m4 => inl ms4
end.

Definition steps_m3b : list (state_m3b * state_m3b) := 
    (k, m) :: 
    (m, m4) ::
    (s, m4) ::
    nil.


Definition m3b : attackgraph measurement corruption := 
{|
    state := state_m3b ;
    steps := steps_m3b ;
    label := label_m3b
|}.




Lemma eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
Lemma eqDec_corruption : forall (x y : corruption), {x = y} + {x <> y}.
Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
Lemma eqDec_state : forall (x y : m3b.(state _ _)), {x = y} + {x <> y}.
Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.

Ltac eqDec_step_left step1 step2 :=
    destruct (eqDec_step eqDec_state step1 step2) as [H|H]; [clear H | contradiction].
Ltac eqDec_step_right step1 step2 :=
    destruct (eqDec_step eqDec_state step1 step2) as [H|H]; [inversion H | clear H].
Ltac eqDec_state_left st1 st2 :=
    destruct (eqDec_state st1 st2) as [H|H]; [clear H | contradiction].
Ltac eqDec_state_right st1 st2 :=
    destruct (eqDec_state st1 st2) as [H|H]; [inversion H | clear H].

Lemma example_m3b : 
    (reduce1 eqDec_state m3b.(steps _ _)) =
    ((k, m4) :: (s, m4) :: nil).
Proof.
    unfold reduce1.
    simpl. 
    eqDec_step_right (m, m4) (k, m).
    eqDec_step_left (m, m4) (m, m4).
    eqDec_step_right (m, m4) (s, m4).
    simpl.
    eqDec_state_left m m.
    eqDec_state_right k m.
    eqDec_state_right s m.
    eqDec_state_right m4 m.
    reflexivity.
Qed.



Check reduce1.
Check reduce1 eqDec_state. 
Check ((s,k)::nil).
Check reduce1 eqDec_state ((s,k)::nil).

Check replace_measurement'.
Check replace_measurement' s.
Lemma tester : 
    replace_measurement' s k ((m,m) :: nil) nil.

End Reducer.
*)



(* *********** *)
(* Example m2c *)
(* *********** *)
(* *********** *)

(*
Section Reducer.

Inductive measurement : Type :=
| ms : measurement
| ms4 : measurement.

Inductive corruption : Type :=
| sys : corruption
| ker : corruption.

Inductive state_m2c : Type :=
| s : state_m2c
| k : state_m2c
| m : state_m2c
| m' : state_m2c
| m4 : state_m2c.

Definition label_m2c (st : state_m2c) : measurement + corruption :=
match st with
| s => inr sys
| k => inr ker
| m => inl ms
| m' => inl ms
| m4 => inl ms4
end.

Definition steps_m2c : list (state_m2c * state_m2c) :=  
    (m, m') ::
    (m', k) ::
    (s, m4) :: 
    (k, m4) :: 
    nil.


Definition m2c : attackgraph measurement corruption := 
{|
    state := state_m2c ;
    steps := steps_m2c ;
    label := label_m2c
|}.


Lemma eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
Lemma eqDec_corruption : forall (x y : corruption), {x = y} + {x <> y}.
Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
Lemma eqDec_state : forall (x y : m2c.(state _ _)), {x = y} + {x <> y}.
Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.

Ltac eqDec_step_left step1 step2 :=
    destruct (eqDec_step eqDec_state step1 step2) as [H|H]; [clear H | contradiction].
Ltac eqDec_step_right step1 step2 :=
    destruct (eqDec_step eqDec_state step1 step2) as [H|H]; [inversion H | clear H].
Ltac eqDec_state_left st1 st2 :=
    destruct (eqDec_state st1 st2) as [H|H]; [clear H | contradiction].
Ltac eqDec_state_right st1 st2 :=
    destruct (eqDec_state st1 st2) as [H|H]; [inversion H | clear H].

Lemma example_m2c : 
    (reduce1 eqDec_state m2c.(steps _ _)) =
    ((m', k) :: (s, m4) :: (k, m4) :: nil).
Proof.
    unfold reduce1.
    simpl. 
    eqDec_step_left (m, m') (m, m').
    eqDec_step_right (m, m') (m', k).
    eqDec_step_right (m, m') (k, m4).
    eqDec_step_right (m, m') (s, m4).
    simpl.
    eqDec_state_right m' m.
    eqDec_state_right k m.
    eqDec_state_right m4 m.
    eqDec_state_right s m.
    reflexivity.
Qed.

End Reducer.
*)


(* *********** *)
(* Example m5c *)
(* *********** *)
(* *********** *)


Section Reducer.

Inductive measurement : Type :=
| ms : measurement
| ms4 : measurement.

Inductive corruption : Type :=
| sys : corruption
| vc : corruption
| cc : corruption.

Inductive state_m5c : Type :=
| s : state_m5c
| v : state_m5c
| c : state_m5c
| m : state_m5c
| m' : state_m5c
| m4 : state_m5c.

Definition label_m5c (st : state_m5c) : measurement + corruption :=
match st with
| s => inr sys
| v => inr vc
| c => inr cc
| m => inl ms
| m' => inl ms
| m4 => inl ms4
end.

Definition steps_m5c : list (state_m5c * state_m5c) := 
    (c, m') ::
    (m, m') ::
    (v, m') ::
    (m', m4) ::
    (s, m4) ::
    nil.


Definition m5c : attackgraph measurement corruption := 
{|
    state := state_m5c ;
    steps := steps_m5c ;
    label := label_m5c
|}.


Lemma eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
Lemma eqDec_corruption : forall (x y : corruption), {x = y} + {x <> y}.
Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
Lemma eqDec_state : forall (x y : m5c.(state _ _)), {x = y} + {x <> y}.
Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.


Ltac eqDec_step_left step1 step2 :=
    destruct (eqDec_step eqDec_state step1 step2) as [H|H]; [clear H | contradiction].
Ltac eqDec_step_right step1 step2 :=
    destruct (eqDec_step eqDec_state step1 step2) as [H|H]; [inversion H | clear H].
Ltac eqDec_state_left st1 st2 :=
    destruct (eqDec_state st1 st2) as [H|H]; [clear H | contradiction].
Ltac eqDec_state_right st1 st2 :=
    destruct (eqDec_state st1 st2) as [H|H]; [inversion H | clear H].

Lemma example_m5c' : 
    (reduce1 eqDec_state (reduce1 eqDec_state m5c.(steps _ _))) =
    ((c, m4) :: (v, m4) :: (s, m4) :: nil).
Proof.
    unfold reduce1.
    simpl.
    eqDec_step_right (m, m') (c, m').
    eqDec_step_left (m, m') (m, m').
    eqDec_step_right (m, m') (v, m').
    eqDec_step_right (m, m') (m', m4).
    eqDec_step_right (m, m') (s, m4).
    simpl.
    eqDec_state_right c m.
    eqDec_state_right m' m.
    eqDec_state_right v m.
    eqDec_state_right m4 m.
    eqDec_state_right s m.
    simpl.
    eqDec_step_right (m', m4) (c, m').
    eqDec_step_right (m', m4) (m, m').
    eqDec_step_right (m', m4) (v, m').
    eqDec_step_left (m', m4) (m', m4).
    eqDec_step_right (m', m4) (s, m4).
    simpl.
    eqDec_state_right c m'.
    eqDec_state_left m' m'.
    eqDec_state_right v m'.
    eqDec_state_right s m'.
    eqDec_state_right m4 m'.
    reflexivity.
Qed.

End Reducer.
*)