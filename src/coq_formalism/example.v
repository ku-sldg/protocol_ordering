(********************
 EXAMPLE ATTACK GRAPHS
 
 Proving various examples about the 
 graphs to ensure our definitions 
 are correct *)

 Require Import Coq.Lists.List.

 Require Import Order.attack_graph.
 Require Import Order.graph_strict_partial_order.
 Require Import Order.graph_normalization.
 Require Import Order.graph_equiv.
 Require Import Order.utilities.
 Require Import Order.graph_partial_order.
 Require Import Order.set_order.
 
 
 
 (* ******************* 
      sys & 
    ker-vc-sys-seq 
 ************************
    Proving ker-vc-sys-seq 
    supports sys 
  * ****************** *)
 Module vc_sys_seq_supports_sys. 
 
     Set Implicit Arguments.
 
     Inductive measurement : Type :=
     | ms : measurement
     | ms4 : measurement.
 
     Inductive adversary : Type :=
     | sys : adversary
     | ker : adversary
     | vc : adversary
     | a : adversary
     | c : adversary.
 
     Inductive states_sys : Type :=
     | sys_sys : states_sys 
     | sys_ker : states_sys
     | sys_vc : states_sys
     | sys_a : states_sys
     | sys_c : states_sys
     | sys_ms3 : states_sys
     | sys_ms4 : states_sys.
 
     Definition label_sys (st : states_sys) : measurement + adversary :=
     match st with
     | sys_sys => inr sys
     | sys_ker => inr ker
     | sys_vc => inr vc
     | sys_a => inr a
     | sys_c => inr c
     | sys_ms3 => inl ms
     | sys_ms4 => inl ms4
     end.
 
     (* 2 graphs for sys... m1a and m2a *)
     Definition steps_m1a : list (states_sys * states_sys) := 
         (sys_sys, sys_ms4) :: 
         (sys_vc, sys_ms4) ::
         nil.
     
     Definition m1a : attackgraph measurement adversary := 
     {|
         event := states_sys ;
         edges := steps_m1a ;
         label := label_sys
     |}.
 
     Definition steps_m2a : list (states_sys * states_sys) := 
         (sys_sys, sys_ms4) :: 
         (sys_ker, sys_ms4) ::
         nil.
     
     Definition m2a : attackgraph measurement adversary := 
     {|
         event := states_sys ;
         edges := steps_m2a ;
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
 
     Definition label_vc_sys_seq (st : states_vc_sys_seq) : measurement + adversary :=
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
 
     Definition m1b : attackgraph measurement adversary := 
     {|
         event := states_vc_sys_seq ;
         edges := steps_m1b ;
         label := label_vc_sys_seq
     |}.
 
     Definition steps_m2b : list (states_vc_sys_seq * states_vc_sys_seq) := 
         (vc_sys_ms3, vc_sys_ms4) :: 
         (vc_sys_vc, vc_sys_ms4) ::
         (vc_sys_sys, vc_sys_ms4) ::
         nil.
 
     Definition m2b : attackgraph measurement adversary := 
     {|
         event := states_vc_sys_seq ;
         edges := steps_m2b ;
         label := label_vc_sys_seq
     |}.
 
     Definition steps_m3b : list (states_vc_sys_seq * states_vc_sys_seq) := 
         (vc_sys_vc, vc_sys_ms3) ::
         (vc_sys_a, vc_sys_ms3) ::
         (vc_sys_ms3, vc_sys_ms4) :: 
         (vc_sys_sys, vc_sys_ms4) ::
         nil.
 
     Definition m3b : attackgraph measurement adversary := 
     {|
         event := states_vc_sys_seq ;
         edges := steps_m3b ;
         label := label_vc_sys_seq
     |}.
 
     Definition steps_m4b : list (states_vc_sys_seq * states_vc_sys_seq) := 
         (vc_sys_vc, vc_sys_ms3) ::
         (vc_sys_c, vc_sys_ms3) ::
         (vc_sys_ms3, vc_sys_ms4) :: 
         (vc_sys_sys, vc_sys_ms4) ::
         nil.
 
     Definition m4b : attackgraph measurement adversary := 
     {|
         event := states_vc_sys_seq ;
         edges := steps_m4b ;
         label := label_vc_sys_seq
     |}.
 
     (* Prove m2b, m3b and m4b reduce *)
 
     Definition steps_m2b' : list (states_vc_sys_seq * states_vc_sys_seq) := 
         (vc_sys_vc, vc_sys_ms4) ::
         (vc_sys_sys, vc_sys_ms4) ::
         nil.
 
     Definition m2b' : attackgraph measurement adversary := 
     {|
         event := states_vc_sys_seq ;
         edges := steps_m2b' ;
         label := label_vc_sys_seq
     |}.
 
     Definition steps_m3b' : list (states_vc_sys_seq * states_vc_sys_seq) := 
         (vc_sys_vc, vc_sys_ms4) ::
         (vc_sys_a, vc_sys_ms4) ::
         (vc_sys_sys, vc_sys_ms4) ::
         nil.
 
     Definition m3b' : attackgraph measurement adversary := 
     {|
         event := states_vc_sys_seq ;
         edges := steps_m3b' ;
         label := label_vc_sys_seq
     |}.
 
     Definition steps_m4b' : list (states_vc_sys_seq * states_vc_sys_seq) := 
         (vc_sys_vc, vc_sys_ms4) ::
         (vc_sys_c, vc_sys_ms4) ::
         (vc_sys_sys, vc_sys_ms4) ::
         nil.
 
     Definition m4b' : attackgraph measurement adversary := 
     {|
         event := states_vc_sys_seq ;
         edges := steps_m4b' ;
         label := label_vc_sys_seq
     |}.
 
     Lemma eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
     Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
     Lemma eqDec_adversary : forall (x y : adversary), {x = y} + {x <> y}.
     Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
     Lemma eqDec_event2: forall (x y : m2b.(event _ _)), {x = y} + {x <> y}.
     Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
     Lemma eqDec_event3: forall (x y : m3b.(event _ _)), {x = y} + {x <> y}.
     Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
     Lemma eqDec_event4: forall (x y : m4b.(event _ _)), {x = y} + {x <> y}.
     Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
 
     Ltac eqDec_edge_left step1 step2 eqDec_event :=
     destruct (eqDec_edge eqDec_event step1 step2) as [H|H]; [clear H | contradiction].
     Ltac eqDec_edge_right step1 step2 eqDec_event :=
     destruct (eqDec_edge eqDec_event step1 step2) as [H|H]; [inversion H | clear H].
     Ltac eqDec_event_left st1 st2 eqDec_event :=
     destruct (eqDec_event st1 st2) as [H|H]; [clear H | contradiction].
     Ltac eqDec_event_right st1 st2 eqDec_event :=
     destruct (eqDec_event st1 st2) as [H|H]; [inversion H | clear H].
 
     Lemma example_m2b_reduce1 : 
     reduce1 eqDec_event2 steps_m2b =
     steps_m2b'.
     Proof.
      unfold reduce1. simpl. 
      eqDec_edge_left (vc_sys_ms3, vc_sys_ms4) (vc_sys_ms3, vc_sys_ms4) eqDec_event2.
      eqDec_edge_right (vc_sys_ms3, vc_sys_ms4) (vc_sys_vc, vc_sys_ms4) eqDec_event2.
      eqDec_edge_right (vc_sys_ms3, vc_sys_ms4) (vc_sys_sys, vc_sys_ms4) eqDec_event2.
      simpl.
      eqDec_event_right vc_sys_vc vc_sys_ms3 eqDec_event2.
      eqDec_event_right vc_sys_ms4 vc_sys_ms3 eqDec_event2.
      eqDec_event_right vc_sys_sys vc_sys_ms3 eqDec_event2.
      unfold steps_m2b'. reflexivity.
     Qed. 
 
     Lemma m2b_reduced : reducer eqDec_event2 steps_m2b steps_m2b'.
     Proof. 
         apply reduce_more.
         + rewrite example_m2b_reduce1. unfold not. intros. inversion H. 
         + rewrite example_m2b_reduce1. apply reduce_done. eauto.
     Qed. 
 
     Lemma example_m3b_reduce1 : 
     reduce1 eqDec_event3 steps_m3b =
     steps_m3b'.
     Proof.
      unfold reduce1. simpl. 
      eqDec_edge_right (vc_sys_ms3, vc_sys_ms4) (vc_sys_vc, vc_sys_ms3) eqDec_event3.
      eqDec_edge_right (vc_sys_ms3, vc_sys_ms4) (vc_sys_a, vc_sys_ms3) eqDec_event3.
      eqDec_edge_left (vc_sys_ms3, vc_sys_ms4) (vc_sys_ms3, vc_sys_ms4) eqDec_event3.
      eqDec_edge_right (vc_sys_ms3, vc_sys_ms4) (vc_sys_sys, vc_sys_ms4) eqDec_event3.
      simpl.
      eqDec_event_right vc_sys_vc vc_sys_ms3 eqDec_event3.
      eqDec_event_right vc_sys_a vc_sys_ms3 eqDec_event3.
      eqDec_event_left vc_sys_ms3 vc_sys_ms3 eqDec_event3.
      eqDec_event_right vc_sys_sys vc_sys_ms3 eqDec_event3.
      eqDec_event_right vc_sys_ms4 vc_sys_ms3 eqDec_event3.
      unfold steps_m3b'. reflexivity.
     Qed. 
 
     Lemma m3b_reduced : reducer eqDec_event3 steps_m3b steps_m3b'.
     Proof. 
         apply reduce_more.
         + rewrite example_m3b_reduce1. unfold not. intros. inversion H. 
         + rewrite example_m3b_reduce1. apply reduce_done. eauto.
     Qed. 
 
     Lemma example_m4b_reduce1 : 
     reduce1 eqDec_event4 steps_m4b =
     steps_m4b'.
     Proof.
      unfold reduce1. simpl. 
      eqDec_edge_right (vc_sys_ms3, vc_sys_ms4) (vc_sys_vc, vc_sys_ms3) eqDec_event4.
      eqDec_edge_right (vc_sys_ms3, vc_sys_ms4) (vc_sys_c, vc_sys_ms3) eqDec_event4.
      eqDec_edge_left (vc_sys_ms3, vc_sys_ms4) (vc_sys_ms3, vc_sys_ms4) eqDec_event4.
      eqDec_edge_right (vc_sys_ms3, vc_sys_ms4) (vc_sys_sys, vc_sys_ms4) eqDec_event4.
      simpl.
      eqDec_event_right vc_sys_vc vc_sys_ms3 eqDec_event4.
      eqDec_event_right vc_sys_c vc_sys_ms3 eqDec_event4.
      eqDec_event_left vc_sys_ms3 vc_sys_ms3 eqDec_event4.
      eqDec_event_right vc_sys_sys vc_sys_ms3 eqDec_event4.
      eqDec_event_right vc_sys_ms4 vc_sys_ms3 eqDec_event4.
      unfold steps_m4b'. reflexivity.
     Qed. 
 
     Lemma m4b_reduced : reducer eqDec_event4 steps_m4b steps_m4b'.
     Proof. 
         apply reduce_more.
         + rewrite example_m4b_reduce1. unfold not. intros. inversion H. 
         + rewrite example_m4b_reduce1. apply reduce_done. eauto.
     Qed.
 
     (* define isomorphism function *)
     Definition f (x : states_sys) : states_vc_sys_seq :=
         match x with 
         | sys_sys => vc_sys_sys 
         | sys_vc => vc_sys_vc
         | sys_ker => vc_sys_ker
         | sys_a => vc_sys_a
         | sys_c => vc_sys_c
         | sys_ms3 => vc_sys_ms3
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
     
     Definition sys_all : list (attackgraph measurement adversary) :=  m1a :: m2a :: nil .
 
     Definition vc_sys_seq_all := m1b :: m2b' :: m3b' :: m4b' :: nil.
 
     Ltac cor_in_head := simpl; apply ex_head; auto.
     Ltac cor_in_tail := simpl; apply ex_tail; auto.
 
     Lemma m1a_supports_m1b : supports ( m1a :: nil ) (m1b :: nil).
     Proof.
         unfold supports. intros. simpl in H0. intuition. 
         exists m1a. simpl in *. split.
         + left. reflexivity.
         + right. subst. unfold strict_partial_order. intuition.
         ++ econstructor.
         +++ simpl. unfold steps_m1b. apply ex_tail. apply ex_tail. apply ex_head. simpl. intuition.
         +++  econstructor. simpl. unfold steps_m1b. apply ex_tail. apply ex_head. simpl. eauto. econstructor.
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
     Qed.
 
     Ltac inversion_any :=
       match goal with
       | [H : _ |- _ ] => inversion H
       end.
 
     Lemma vc_sys_seq_supports_sys : supports sys_all vc_sys_seq_all.
     Proof.
       unfold supports. intros. simpl in H0. intuition.
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
         unfold isomorphism. exists f. unfold f. repeat split; intros.
       ++ destruct st1, st2; try (simpl in *; intuition; inversion_any).
       ++ destruct st1, st2; try (simpl in *; intuition; inversion_any).
       ++ destruct st; auto.
       ++ destruct st1, st2; try reflexivity; inversion_any.
       ++ destruct st'.
       +++ exists sys_sys; reflexivity.
       +++ exists sys_ker; reflexivity.
       +++ exists sys_vc; reflexivity.
       +++ exists sys_a; reflexivity.
       +++ exists sys_c; reflexivity.
       +++ exists sys_ms3; reflexivity.
       +++ exists sys_ms4; reflexivity.
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
 
 End vc_sys_seq_supports_sys. 
 

 



 (* ***********************************
    Attack tree normalization examples
    ***********************************
    ********************************* *)


 (* *********** *)
 (* Example m2c *)
 (* *********** *)
 (* *********** *)
 
 Module m3b.
 
     Set Implicit Arguments.
     
     Inductive measurement : Type :=
     | ms : measurement
     | ms4 : measurement.
     
     Inductive adversary : Type :=
     | sys : adversary
     | ker : adversary.
     
     Inductive state_m3b : Type :=
     | s : state_m3b 
     | k : state_m3b
     | m : state_m3b
     | m4 : state_m3b.
     
     Definition label_m3b (st : state_m3b) : measurement + adversary :=
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
     
     Definition m3b : attackgraph measurement adversary := 
     {|
         event := state_m3b ;
         edges := steps_m3b ;
         label := label_m3b
     |}.
     
     Lemma eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
     Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
     Lemma eqDec_adversary : forall (x y : adversary), {x = y} + {x <> y}.
     Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
     Lemma eqDec_event: forall (x y : m3b.(event _ _)), {x = y} + {x <> y}.
     Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
 
     Ltac eqDec_edge_left step1 step2 :=
     destruct (eqDec_edge eqDec_event step1 step2) as [H|H]; [clear H | contradiction].
     Ltac eqDec_edge_right step1 step2 :=
     destruct (eqDec_edge eqDec_event step1 step2) as [H|H]; [inversion H | clear H].
     Ltac eqDec_event_left st1 st2 :=
     destruct (eqDec_event st1 st2) as [H|H]; [clear H | contradiction].
     Ltac eqDec_event_right st1 st2 :=
     destruct (eqDec_event st1 st2) as [H|H]; [inversion H | clear H].
 
     Lemma example_m3b : 
     (reduce1 eqDec_event m3b.(edges _ _)) =
     ((k, m4) :: (s, m4) :: nil).
     Proof.
         unfold reduce1.
         simpl. 
         eqDec_edge_right (m, m4) (k, m).
         eqDec_edge_left (m, m4) (m, m4).
         eqDec_edge_right (m, m4) (s, m4).
         simpl.
         eqDec_event_right k m.
         eqDec_event_left m m.
         eqDec_event_right s m.
         eqDec_event_right m4 m.
         eauto.
     Qed.
 
     Definition m3b_edges := m3b.(edges _ _).
     Definition m3b_reduced := ((k, m4) :: (s, m4) :: nil).
 
     Check reducer eqDec_event m3b_edges m3b_reduced. 
 
     Lemma example_m3b_reducer : 
         reducer eqDec_event m3b_edges m3b_reduced.
     Proof.
         econstructor.
         + unfold m3b_edges. rewrite example_m3b. simpl. intros contra. inversion contra.
         + unfold m3b_edges. rewrite example_m3b.
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
 
 Inductive adversary : Type :=
 | sys : adversary
 | ker : adversary.
 
 Inductive state_m2c : Type :=
 | s : state_m2c
 | k : state_m2c
 | m : state_m2c
 | m' : state_m2c
 | m4 : state_m2c.
 
 Definition label_m2c (st : state_m2c) : measurement + adversary :=
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
 
 
 Definition m2c : attackgraph measurement adversary := 
 {|
     event := state_m2c ;
     edges := steps_m2c ;
     label := label_m2c
 |}.
 
 Definition m2b : attackgraph measurement adversary := 
 {|
     event := state_m2c ;
     edges := steps_m2b ;
     label := label_m2c
 |}.
 
 Definition m2a : attackgraph measurement adversary := 
 {|
     event := state_m2c ;
     edges := steps_m2a ;
     label := label_m2c
 |}.
 
 Definition m2a_nil : attackgraph measurement adversary := 
 {|
     event := state_m2c ;
     edges := nil ;
     label := label_m2c
 |}.
 
 
 Lemma eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
 Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
 Lemma eqDec_adversary : forall (x y : adversary), {x = y} + {x <> y}.
 Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
 Lemma eqDec_event : forall (x y : m2c.(event _ _)), {x = y} + {x <> y}.
 Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
 
 Ltac eqDec_edge_left step1 step2 :=
     destruct (eqDec_edge eqDec_event step1 step2) as [H|H]; [clear H | contradiction].
 Ltac eqDec_edge_right step1 step2 :=
     destruct (eqDec_edge eqDec_event step1 step2) as [H|H]; [inversion H | clear H].
 Ltac eqDec_event_left st1 st2 :=
     destruct (eqDec_event st1 st2) as [H|H]; [clear H | contradiction].
 Ltac eqDec_event_right st1 st2 :=
     destruct (eqDec_event st1 st2) as [H|H]; [inversion H | clear H].
 
 Lemma example_m2c : 
     (reduce1 eqDec_event m2c.(edges _ _)) =
     ((m', k) :: (s, m4) :: (k, m4) :: nil).
 Proof.
     unfold reduce1.
     simpl. 
     eqDec_edge_left (m, m') (m, m').
     eqDec_edge_right (m, m') (m', k).
     eqDec_edge_right (m, m') (s, m4).
     eqDec_edge_right (m, m') (k, m4).
     simpl.
     eqDec_event_right m' m.
     eqDec_event_right k m.
     eqDec_event_right s m.
     eqDec_event_right m4 m.
     reflexivity.
 Qed.

 End m2c.
 
 (* *********** *)
 (* Example m5c *)
 (* *********** *)
 (* *********** *)
 Module m5c.
 
 Inductive measurement : Type :=
 | ms : measurement
 | ms4 : measurement.
 
 Inductive adversary : Type :=
 | sys : adversary
 | vc : adversary
 | cc : adversary.
 
 Inductive state_m5c : Type :=
 | s : state_m5c
 | v : state_m5c
 | c : state_m5c
 | m : state_m5c
 | m' : state_m5c
 | m4 : state_m5c.
 
 Definition label_m5c (st : state_m5c) : measurement + adversary :=
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
 
 Definition m5c : attackgraph measurement adversary := 
 {|
     event := state_m5c ;
     edges := steps_m5c ;
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
 Definition m5c' : attackgraph measurement adversary := 
 {|
     event := state_m5c ;
     edges := steps_m5c' ;
     label := label_m5c
 |}.
 
 Lemma eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
 Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
 Lemma eqDec_adversary : forall (x y : adversary), {x = y} + {x <> y}.
 Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
 Lemma eqDec_event : forall (x y : m5c.(event _ _)), {x = y} + {x <> y}.
 Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
 
 
 Ltac eqDec_edge_left step1 step2 :=
     destruct (eqDec_edge eqDec_event step1 step2) as [H|H]; [clear H | contradiction].
 Ltac eqDec_edge_right step1 step2 :=
     destruct (eqDec_edge eqDec_event step1 step2) as [H|H]; [inversion H | clear H].
 Ltac eqDec_event_left st1 st2 :=
     destruct (eqDec_event st1 st2) as [H|H]; [clear H | contradiction].
 Ltac eqDec_event_right st1 st2 :=
     destruct (eqDec_event st1 st2) as [H|H]; [inversion H | clear H].
     
 Definition m5c_edges := m5c.(edges _ _).
 Definition m5c'_edges := m5c'.(edges _ _).
 Definition m5c_reduced := ((c, m4) :: (v, m4) :: (s, m4) :: nil).
 
 (* must call reduce1 twice here *)
 Lemma example_m5c' : 
     (reduce1 eqDec_event (reduce1 eqDec_event m5c.(edges _ _))) =
     ((c, m4) :: (v, m4) :: (s, m4) :: nil).
 Proof.
     unfold reduce1.
     simpl.
     eqDec_edge_right (m, m') (c, m').
     eqDec_edge_left (m, m') (m, m').
     eqDec_edge_right (m, m') (v, m').
     eqDec_edge_right (m, m') (m', m4).
     eqDec_edge_right (m, m') (s, m4).
     simpl.
     eqDec_event_right c m.
     eqDec_event_right v m.
     eqDec_event_right m' m.
     eqDec_event_right m4 m.
     eqDec_event_right s m.
     simpl.
     eqDec_edge_right (m', m4) (c, m').
     eqDec_edge_right (m', m4) (v, m').
     eqDec_edge_left (m', m4) (m', m4).
     eqDec_edge_right (m', m4) (s, m4).
     simpl.
     eqDec_event_right c m'.
     eqDec_event_left m' m'.
     eqDec_event_right v m'.
     eqDec_event_right s m'.
     eqDec_event_right m4 m'.
     reflexivity.
 Qed.
 
 Lemma example_m5c_reducer : 
 reducer eqDec_event m5c_edges m5c_reduced.
 Proof.
     econstructor.
     + unfold m5c_edges. simpl. unfold reduce1. simpl. 
       eqDec_edge_right (m, m') (c, m').
       eqDec_edge_left (m, m') (m, m').
       eqDec_edge_right (m, m') (v, m').
       eqDec_edge_right (m, m') (m', m4).
       eqDec_edge_right (m, m') (s, m4).
       simpl.
       eqDec_event_right c m.
       eqDec_event_right m m'.
       eqDec_event_right m' m.
       eqDec_event_right v m.
       eqDec_event_right m4 m.
       eqDec_event_right s m.
       intros contra. inversion contra.
     + econstructor.
     ++ unfold m5c_edges. simpl. unfold reduce1. simpl.
         eqDec_edge_right (m, m') (c, m').
         eqDec_edge_left (m, m') (m, m').
         eqDec_edge_right (m, m') (v, m').
         eqDec_edge_right (m, m') (m', m4).
         eqDec_edge_right (m, m') (s, m4).
         unfold replace_measurement.
         eqDec_event_right c m.
         eqDec_event_right m' m.
         eqDec_event_right v m.
         eqDec_event_right m4 m.
         eqDec_event_right s m.
         simpl.
         eqDec_edge_right (m', m4) (c, m').
         eqDec_edge_right (m', m4) (v, m').
         eqDec_edge_left (m', m4) (m', m4).
         eqDec_edge_right (m', m4) (s, m4).
         simpl.
         eqDec_event_right c m'.
         eqDec_event_left m' m'.
         eqDec_event_right v m'.
         eqDec_event_right s m'.
         eqDec_event_right m4 m'.
         intros contra. inversion contra.
     ++ unfold m5c_edges. rewrite example_m5c'.
        econstructor. unfold reduce1.
        simpl. reflexivity.
     Qed.
 
 End m5c.