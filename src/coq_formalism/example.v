(********************
 EXAMPLE ATTACK GRAPHS
 
 Proving various examples about the 
 graphs to ensure our definitions 
 are correct *)

Require Import Coq.Lists.List.

Require Import Order.attack_graph.
Require Import Order.strict_partial_order.
Require Import Order.reduce.
Require Import Order.equiv.
Require Import Order.utilities.
Require Import Order.partial_order.
Require Import Order.supports.
Require Import Order.compare. 


(* ******************* 
     sys & 
   vc sys seq 
************************
   Proving vc sys seq 
   supports sys 
 * ****************** *)
Module vc_sys_seq_supports_sys. 

    Set Implicit Arguments.

    Inductive measurement : Type :=
    | ms : measurement
    | ms4 : measurement.

    Inductive corruption : Type :=
    | sys : corruption
    | ker : corruption
    | vc : corruption
    | a : corruption
    | c : corruption.

    Inductive states_sys : Type :=
    | sys_sys : states_sys 
    | sys_ker : states_sys
    | sys_vc : states_sys
    | sys_ms4 : states_sys.

    Definition label_sys (st : states_sys) : measurement + corruption :=
    match st with
    | sys_sys => inr sys
    | sys_ker => inr ker
    | sys_vc => inr vc
    | sys_ms4 => inl ms4
    end.

    (* 2 graphs for sys... m1a and m2a *)
    Definition steps_m1a : list (states_sys * states_sys) := 
        (sys_sys, sys_ms4) :: 
        (sys_vc, sys_ms4) ::
        nil.
    
    Definition m1a : attackgraph measurement corruption := 
    {|
        state := states_sys ;
        steps := steps_m1a ;
        label := label_sys
    |}.

    Definition steps_m2a : list (states_sys * states_sys) := 
        (sys_sys, sys_ms4) :: 
        (sys_ker, sys_ms4) ::
        nil.
    
    Definition m2a : attackgraph measurement corruption := 
    {|
        state := states_sys ;
        steps := steps_m2a ;
        label := label_sys
    |}.

    Inductive states_vc_sys_seq : Type :=
    | vc_sys_sys : states_vc_sys_seq 
    | vc_sys_ker : states_vc_sys_seq
    | vc_sys_vc : states_vc_sys_seq
    | vc_sys_a : states_vc_sys_seq
    | vc_sys_c : states_vc_sys_seq
    | vc_sys_ms3 : states_vc_sys_seq
    | vc_sys_ms4 : states_vc_sys_seq.

    Definition label_vc_sys_seq (st : states_vc_sys_seq) : measurement + corruption :=
    match st with
    | vc_sys_sys => inr sys
    | vc_sys_ker => inr ker
    | vc_sys_vc => inr vc
    | vc_sys_a => inr a
    | vc_sys_c => inr c 
    | vc_sys_ms3 => inl ms 
    | vc_sys_ms4 => inl ms4
    end.

    (* 4 possible graphs *)

    Definition steps_m1b : list (states_vc_sys_seq * states_vc_sys_seq) := 
        (vc_sys_ms3, vc_sys_vc) :: 
        (vc_sys_vc, vc_sys_ms4) ::
        (vc_sys_sys, vc_sys_ms4) ::
        nil.

    Definition m1b : attackgraph measurement corruption := 
    {|
        state := states_vc_sys_seq ;
        steps := steps_m1b ;
        label := label_vc_sys_seq
    |}.

    Definition steps_m2b : list (states_vc_sys_seq * states_vc_sys_seq) := 
        (vc_sys_ms3, vc_sys_ms4) :: 
        (vc_sys_vc, vc_sys_ms4) ::
        (vc_sys_sys, vc_sys_ms4) ::
        nil.

    Definition m2b : attackgraph measurement corruption := 
    {|
        state := states_vc_sys_seq ;
        steps := steps_m2b ;
        label := label_vc_sys_seq
    |}.

    Definition steps_m3b : list (states_vc_sys_seq * states_vc_sys_seq) := 
        (vc_sys_vc, vc_sys_ms3) ::
        (vc_sys_a, vc_sys_ms3) ::
        (vc_sys_ms3, vc_sys_ms4) :: 
        (vc_sys_sys, vc_sys_ms4) ::
        nil.

    Definition m3b : attackgraph measurement corruption := 
    {|
        state := states_vc_sys_seq ;
        steps := steps_m3b ;
        label := label_vc_sys_seq
    |}.

    Definition steps_m4b : list (states_vc_sys_seq * states_vc_sys_seq) := 
        (vc_sys_vc, vc_sys_ms3) ::
        (vc_sys_c, vc_sys_ms3) ::
        (vc_sys_ms3, vc_sys_ms4) :: 
        (vc_sys_sys, vc_sys_ms4) ::
        nil.

    Definition m4b : attackgraph measurement corruption := 
    {|
        state := states_vc_sys_seq ;
        steps := steps_m4b ;
        label := label_vc_sys_seq
    |}.

    (* Prove m2b, m3b and m4b reduce *)

    Definition steps_m2b' : list (states_vc_sys_seq * states_vc_sys_seq) := 
        (vc_sys_vc, vc_sys_ms4) ::
        (vc_sys_sys, vc_sys_ms4) ::
        nil.

    Definition m2b' : attackgraph measurement corruption := 
    {|
        state := states_vc_sys_seq ;
        steps := steps_m2b' ;
        label := label_vc_sys_seq
    |}.

    Definition steps_m3b' : list (states_vc_sys_seq * states_vc_sys_seq) := 
        (vc_sys_vc, vc_sys_ms4) ::
        (vc_sys_a, vc_sys_ms4) ::
        (vc_sys_sys, vc_sys_ms4) ::
        nil.

    Definition m3b' : attackgraph measurement corruption := 
    {|
        state := states_vc_sys_seq ;
        steps := steps_m3b' ;
        label := label_vc_sys_seq
    |}.

    Definition steps_m4b' : list (states_vc_sys_seq * states_vc_sys_seq) := 
        (vc_sys_vc, vc_sys_ms4) ::
        (vc_sys_c, vc_sys_ms4) ::
        (vc_sys_sys, vc_sys_ms4) ::
        nil.

    Definition m4b' : attackgraph measurement corruption := 
    {|
        state := states_vc_sys_seq ;
        steps := steps_m4b' ;
        label := label_vc_sys_seq
    |}.

    Lemma eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
    Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
    Lemma eqDec_corruption : forall (x y : corruption), {x = y} + {x <> y}.
    Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
    Lemma eqDec_state2: forall (x y : m2b.(state _ _)), {x = y} + {x <> y}.
    Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
    Lemma eqDec_state3: forall (x y : m3b.(state _ _)), {x = y} + {x <> y}.
    Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
    Lemma eqDec_state4: forall (x y : m4b.(state _ _)), {x = y} + {x <> y}.
    Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.

    Ltac eqDec_step_left step1 step2 eqDec_state :=
    destruct (eqDec_step eqDec_state step1 step2) as [H|H]; [clear H | contradiction].
    Ltac eqDec_step_right step1 step2 eqDec_state :=
    destruct (eqDec_step eqDec_state step1 step2) as [H|H]; [inversion H | clear H].
    Ltac eqDec_state_left st1 st2 eqDec_state :=
    destruct (eqDec_state st1 st2) as [H|H]; [clear H | contradiction].
    Ltac eqDec_state_right st1 st2 eqDec_state :=
    destruct (eqDec_state st1 st2) as [H|H]; [inversion H | clear H].

    Lemma example_m2b_reduce1 : 
    reduce1 eqDec_state2 steps_m2b =
    steps_m2b'.
    Proof.
     unfold reduce1. simpl. 
     eqDec_step_left (vc_sys_ms3, vc_sys_ms4) (vc_sys_ms3, vc_sys_ms4) eqDec_state2.
     eqDec_step_right (vc_sys_ms3, vc_sys_ms4) (vc_sys_vc, vc_sys_ms4) eqDec_state2.
     eqDec_step_right (vc_sys_ms3, vc_sys_ms4) (vc_sys_sys, vc_sys_ms4) eqDec_state2.
     simpl.
     eqDec_state_right vc_sys_vc vc_sys_ms3 eqDec_state2.
     eqDec_state_right vc_sys_ms4 vc_sys_ms3 eqDec_state2.
     eqDec_state_right vc_sys_sys vc_sys_ms3 eqDec_state2.
     unfold steps_m2b'. reflexivity.
    Qed. 

    Lemma m2b_reduced : reducer eqDec_state2 steps_m2b steps_m2b'.
    Proof. 
        apply reduce_more.
        + rewrite example_m2b_reduce1. unfold not. intros. inversion H. 
        + rewrite example_m2b_reduce1. apply reduce_done. eauto.
    Qed. 

    Lemma example_m3b_reduce1 : 
    reduce1 eqDec_state3 steps_m3b =
    steps_m3b'.
    Proof.
     unfold reduce1. simpl. 
     eqDec_step_right (vc_sys_ms3, vc_sys_ms4) (vc_sys_vc, vc_sys_ms3) eqDec_state3.
     eqDec_step_right (vc_sys_ms3, vc_sys_ms4) (vc_sys_a, vc_sys_ms3) eqDec_state3.
     eqDec_step_left (vc_sys_ms3, vc_sys_ms4) (vc_sys_ms3, vc_sys_ms4) eqDec_state3.
     eqDec_step_right (vc_sys_ms3, vc_sys_ms4) (vc_sys_sys, vc_sys_ms4) eqDec_state3.
     simpl.
     eqDec_state_right vc_sys_vc vc_sys_ms3 eqDec_state3.
     eqDec_state_right vc_sys_a vc_sys_ms3 eqDec_state3.
     eqDec_state_left vc_sys_ms3 vc_sys_ms3 eqDec_state3.
     eqDec_state_right vc_sys_sys vc_sys_ms3 eqDec_state3.
     eqDec_state_right vc_sys_ms4 vc_sys_ms3 eqDec_state3.
     unfold steps_m3b'. reflexivity.
    Qed. 

    Lemma m3b_reduced : reducer eqDec_state3 steps_m3b steps_m3b'.
    Proof. 
        apply reduce_more.
        + rewrite example_m3b_reduce1. unfold not. intros. inversion H. 
        + rewrite example_m3b_reduce1. apply reduce_done. eauto.
    Qed. 

    Lemma example_m4b_reduce1 : 
    reduce1 eqDec_state4 steps_m4b =
    steps_m4b'.
    Proof.
     unfold reduce1. simpl. 
     eqDec_step_right (vc_sys_ms3, vc_sys_ms4) (vc_sys_vc, vc_sys_ms3) eqDec_state4.
     eqDec_step_right (vc_sys_ms3, vc_sys_ms4) (vc_sys_c, vc_sys_ms3) eqDec_state4.
     eqDec_step_left (vc_sys_ms3, vc_sys_ms4) (vc_sys_ms3, vc_sys_ms4) eqDec_state4.
     eqDec_step_right (vc_sys_ms3, vc_sys_ms4) (vc_sys_sys, vc_sys_ms4) eqDec_state4.
     simpl.
     eqDec_state_right vc_sys_vc vc_sys_ms3 eqDec_state4.
     eqDec_state_right vc_sys_c vc_sys_ms3 eqDec_state4.
     eqDec_state_left vc_sys_ms3 vc_sys_ms3 eqDec_state4.
     eqDec_state_right vc_sys_sys vc_sys_ms3 eqDec_state4.
     eqDec_state_right vc_sys_ms4 vc_sys_ms3 eqDec_state4.
     unfold steps_m4b'. reflexivity.
    Qed. 

    Lemma m4b_reduced : reducer eqDec_state4 steps_m4b steps_m4b'.
    Proof. 
        apply reduce_more.
        + rewrite example_m4b_reduce1. unfold not. intros. inversion H. 
        + rewrite example_m4b_reduce1. apply reduce_done. eauto.
    Qed.

    (* define homomorphism function *)
    Definition f (x : states_sys) : states_vc_sys_seq :=
        match x with 
        | sys_sys => vc_sys_sys 
        | sys_vc => vc_sys_vc
        | sys_ker => vc_sys_ker
        | sys_ms4 => vc_sys_ms4
    end.

    Definition g (x : states_vc_sys_seq) : option (states_sys) :=
        match x with 
        | vc_sys_sys => Some sys_sys 
        | vc_sys_vc => Some sys_vc
        | vc_sys_ker => Some sys_ker
        | vc_sys_ms4 => Some sys_ms4
        | _ => None
    end.

    Definition g' (x : states_vc_sys_seq) : (states_sys) :=
        match x with 
        | vc_sys_sys =>  sys_sys 
        | vc_sys_vc =>  sys_vc
        | vc_sys_ker =>  sys_ker
        | vc_sys_ms4 =>  sys_ms4
        | _ => sys_ms4
    end.
    
    Definition sys_all : list (attackgraph measurement corruption) :=  m1a :: m2a :: nil .

    Definition vc_sys_seq_all := m1b :: m2b' :: m3b' :: m4b' :: nil.

    Ltac cor_in_head := simpl; apply ex_head; auto.
    Ltac cor_in_tail := simpl; apply ex_tail; auto.

    Lemma m1a_supports_m1b : supports ( m1a :: nil ) (m1b :: nil).
    Proof.
      unfold supports. right.
      unfold supports_spo. intros. simpl in H0.
      destruct H0.
      + exists m1a. simp_int.
        unfold strict_partial_order. intuition; subst.
      ++ econstructor.
      +++  simpl. unfold find_cor. simpl. apply ex_tail. simpl.
           apply ex_tail. apply ex_head. simpl. eauto.
      +++ econstructor.
      ++++ unfold find_cor. simpl. apply ex_tail. apply ex_head. simp_int. 
      ++++ econstructor.
      ++ econstructor; try econstructor; try econstructor.
      ++ right. unfold time_proper_subset. split.
      +++ unfold find_time. repeat econstructor.
      +++ unfold not. intros. inversion H. subst. unfold find_time in H2. simpl in *. inversion H2.
      ++++ subst. invc H1. simpl in *. invc H0.
      ++++ subst. invc H1. subst. invc H3. simpl in *. invc H0.
           subst. invc H3.
    + invc H0.
    Qed.

    Lemma vc_sys_seq_supports_sys : supports' sys_all vc_sys_seq_all.
    Proof.
      unfold supports'. intros. simpl in H0. intuition.
      + subst. exists m1a. unfold sys_all; intuition. right.
        unfold strict_partial_order. intuition.
      ++ econstructor. 
      +++ simpl. unfold steps_m1b. apply ex_tail. apply ex_tail. apply ex_head. simpl. intuition.
      +++ econstructor. simpl. unfold steps_m1b. apply ex_tail. apply ex_head. simpl. eauto. econstructor.
      ++ econstructor.
      +++ simpl. unfold steps_m1b. unfold find_time. simpl. eauto.
      +++ econstructor. simpl. unfold steps_m1b. unfold find_time. simpl. eauto.
          econstructor.
      ++ right. unfold time_proper_subset. split.
      +++ econstructor.
      ++++ simpl. unfold steps_m1b. unfold find_time. simpl. eauto.
      ++++ econstructor. simpl. unfold steps_m1b. unfold find_time. simpl. eauto.
          econstructor.
      +++ unfold not. intros. invc H. subst. simpl in *. invc H2. subst.
          simpl in *. destruct H0. inversion H0. subst. invc H0. subst. 
          destruct H1. simpl in *. invc H. subst. invc H1.
      + subst. exists m1a. unfold sys_all. intuition. left.
        unfold isomorphism. split.
      ++ simpl. exists f. unfold homomorphism. split.
      +++ intros. simpl in *. intuition.
      ++++ invc H0. right. left. unfold f. eauto.
      ++++ invc H. left. unfold f. eauto.
      +++ intros. simpl in *. intuition; try (invc H0; simpl in *; eauto); try (invc H; simpl in *; eauto).
      ++ simpl. exists g'. unfold homomorphism. split.
      +++ intros. simpl in *. intuition.
      ++++ invc H0. right. left. unfold f. eauto.
      ++++ invc H. left. unfold f. eauto.
      +++ intros. simpl in *. intuition; try (invc H0; simpl in *; eauto); try (invc H; simpl in *; eauto).
      + exists m1a. unfold sys_all. intuition. right. subst.
        unfold strict_partial_order. intuition. 
      ++  econstructor. 
      +++ simpl. unfold steps_m3b'. apply ex_tail. apply ex_tail. apply ex_head. simpl. intuition.
      +++ econstructor. simpl. unfold steps_m3b'. apply ex_head. simpl. eauto. econstructor.
      ++ econstructor.
      +++ simpl. unfold steps_m3b'. unfold find_time. simpl. eauto.
      +++ econstructor. simpl. unfold steps_m3b'. unfold find_time. simpl. eauto.
          econstructor.
      ++ left. unfold cor_proper_subset. intuition.
      +++ econstructor.  
      ++++ simpl. unfold steps_m3b'. apply ex_tail. apply ex_tail. apply ex_head. simpl. intuition.
      ++++ econstructor. simpl. unfold steps_m3b'. apply ex_head. simpl. eauto. econstructor.
      +++ invc H. subst. invc H4. subst. invc H1. subst. invc H0.
          subst. invc H0. subst. invc H1. invc H1.
      +  exists m1a. unfold sys_all. intuition. right. subst.
      unfold strict_partial_order. intuition. 
    ++  econstructor. 
    +++ simpl. unfold steps_m3b'. apply ex_tail. apply ex_tail. apply ex_head. simpl. intuition.
    +++ econstructor. simpl. unfold steps_m3b'. apply ex_head. simpl. eauto. econstructor.
    ++ econstructor.
    +++ simpl. unfold steps_m3b'. unfold find_time. simpl. eauto.
    +++ econstructor. simpl. unfold steps_m3b'. unfold find_time. simpl. eauto.
        econstructor.
    ++ left. unfold cor_proper_subset. intuition.
    +++ econstructor.  
    ++++ simpl. unfold steps_m3b'. apply ex_tail. apply ex_tail. apply ex_head. simpl. intuition.
    ++++ econstructor. simpl. unfold steps_m3b'. apply ex_head. simpl. eauto. econstructor.
    +++ invc H. subst. invc H4. subst. invc H1. subst. invc H0.
        subst. invc H0. subst. invc H1. invc H1.
 Qed.

 (* *)
 Theorem vc_sys_seq_set_reduced : reduce_set vc_sys_seq_all vc_sys_seq_all (m2b' :: nil).
 Proof.
    unfold vc_sys_seq_all. apply set_remove. 
    + exists m2b'. split; auto with *.  admit.
    + apply set_keep.
    ++ intros. simp_int.
    +++ subst. unfold strict_partial_order in H0. invc H0. admit.
    +++ subst.  admit.
    +++ admit. 
    +++ admit.
    ++  apply set_remove. 
    +++ exists m2b'.  admit.
    +++ apply set_remove. 
    ++++ admit.
    ++++ apply set_nil.     
Admitted.
 

End vc_sys_seq_supports_sys. 


(* *********** *)
(* Example m2c *)
(* *********** *)
(* *********** *)

Module m3b.

    Set Implicit Arguments.
    
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
    Lemma eqDec_state: forall (x y : m3b.(state _ _)), {x = y} + {x <> y}.
    Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.

    Ltac eqDec_step_left step1 step2 :=
    destruct (eqDec_step eqDec_state step1 step2) as [H|H]; [clear H | contradiction].
    Ltac eqDec_step_right step1 step2 :=
    destruct (eqDec_step eqDec_state step1 step2) as [H|H]; [inversion H | clear H].
    Ltac eqDec_state_left st1 st2 :=
    destruct (eqDec_state st1 st2) as [H|H]; [clear H | contradiction].
    Ltac eqDec_state_right st1 st2 :=
    destruct (eqDec_state st1 st2) as [H|H]; [inversion H | clear H].

    Print reduce1.

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
        eqDec_state_right k m.
        eqDec_state_left m m.
        eqDec_state_right s m.
        eqDec_state_right m4 m.
        eauto.
    Qed.

    Definition m3b_steps := m3b.(steps _ _).
    Definition m3b_reduced := ((k, m4) :: (s, m4) :: nil).

    Check reducer eqDec_state m3b_steps m3b_reduced. 

    Lemma example_m3b_reducer : 
        reducer eqDec_state m3b_steps m3b_reduced.
    Proof.
        econstructor.
        + unfold m3b_steps. rewrite example_m3b. simpl. intros contra. inversion contra.
        + unfold m3b_steps. rewrite example_m3b.
          apply reduce_done. unfold reduce1. simpl. eauto.
    Qed.
    

End m3b.


(* *********** *)
(* Example m2c *)
(* *********** *)
(* *********** *)
Module m2c.

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

Definition steps_m2b : list (state_m2c * state_m2c) :=  
    (m', k) ::
    (s, m4) :: 
    (k, m4) :: 
    nil.

Definition steps_m2a : list (state_m2c * state_m2c) :=  
    (s, m4) :: 
    (k, m4) :: 
    nil.


Definition m2c : attackgraph measurement corruption := 
{|
    state := state_m2c ;
    steps := steps_m2c ;
    label := label_m2c
|}.

Definition m2b : attackgraph measurement corruption := 
{|
    state := state_m2c ;
    steps := steps_m2b ;
    label := label_m2c
|}.

Definition m2a : attackgraph measurement corruption := 
{|
    state := state_m2c ;
    steps := steps_m2a ;
    label := label_m2c
|}.

Definition m2a_nil : attackgraph measurement corruption := 
{|
    state := state_m2c ;
    steps := nil ;
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
    eqDec_step_right (m, m') (s, m4).
    eqDec_step_right (m, m') (k, m4).
    simpl.
    eqDec_state_right m' m.
    eqDec_state_right k m.
    eqDec_state_right s m.
    eqDec_state_right m4 m.
    reflexivity.
Qed.

Print time_subset. 
Lemma time_subset_m2a_m2c : time_subset m2a.(steps _ _) m2c.(steps _ _).
Proof.
    simpl. auto.
Qed.

(* TODO: this proof?? *)
Lemma not_time_subset_m2c_m2a : ~ time_subset m2c.(steps _ _) m2a.(steps _ _).
Proof.
    unfold not; intros.
    inversion H. inversion H0.
    inversion H2. clear H2.
Abort.

(* TODO: this proof too? *)
Lemma subset_nil : ~ cor_subset m2a.(steps _ _) m2a_nil.(steps _ _).
Proof.
Abort.

(* TODO *)
Lemma subset_nil_with_meas : ~ cor_subset m2c.(steps _ _) m2a_nil.(steps _ _).
Proof.
Abort.

End m2c.

(* *********** *)
(* Example m5c *)
(* *********** *)
(* *********** *)
Module m5c.

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

(* remove c to m' to have a proper subset *)
Definition steps_m5c' : list (state_m5c * state_m5c) := 
    (m, m') ::
    (v, m') ::
    (m', m4) ::
    (s, m4) ::
    nil.

(* new graph that would be proper subset *)
Definition m5c' : attackgraph measurement corruption := 
{|
    state := state_m5c ;
    steps := steps_m5c' ;
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
    
Definition m5c_steps := m5c.(steps _ _).
Definition m5c'_steps := m5c'.(steps _ _).
Definition m5c_reduced := ((c, m4) :: (v, m4) :: (s, m4) :: nil).

(* must call reduce1 twice here *)
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
    eqDec_state_right v m.
    eqDec_state_right m' m.
    eqDec_state_right m4 m.
    eqDec_state_right s m.
    simpl.
    eqDec_step_right (m', m4) (c, m').
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

Lemma example_m5c_reducer : 
reducer eqDec_state m5c_steps m5c_reduced.
Proof.
    econstructor.
    + unfold m5c_steps. simpl. unfold reduce1. simpl. 
      eqDec_step_right (m, m') (c, m').
      eqDec_step_left (m, m') (m, m').
      eqDec_step_right (m, m') (v, m').
      eqDec_step_right (m, m') (m', m4).
      eqDec_step_right (m, m') (s, m4).
      simpl.
      eqDec_state_right c m.
      eqDec_state_right m m'.
      eqDec_state_right m' m.
      eqDec_state_right v m.
      eqDec_state_right m4 m.
      eqDec_state_right s m.
      intros contra. inversion contra.
    + econstructor.
    ++ unfold m5c_steps. simpl. unfold reduce1. simpl.
        eqDec_step_right (m, m') (c, m').
        eqDec_step_left (m, m') (m, m').
        eqDec_step_right (m, m') (v, m').
        eqDec_step_right (m, m') (m', m4).
        eqDec_step_right (m, m') (s, m4).
        unfold replace_measurement.
        eqDec_state_right c m.
        eqDec_state_right m' m.
        eqDec_state_right v m.
        eqDec_state_right m4 m.
        eqDec_state_right s m.
        simpl.
        eqDec_step_right (m', m4) (c, m').
        eqDec_step_right (m', m4) (v, m').
        eqDec_step_left (m', m4) (m', m4).
        eqDec_step_right (m', m4) (s, m4).
        simpl.
        eqDec_state_right c m'.
        eqDec_state_left m' m'.
        eqDec_state_right v m'.
        eqDec_state_right s m'.
        eqDec_state_right m4 m'.
        intros contra. inversion contra.
    ++ unfold m5c_steps. rewrite example_m5c'.
       econstructor. unfold reduce1.
       simpl. reflexivity.
    Qed.

End m5c.