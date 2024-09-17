(********************
 EXAMPLE ATTACK TREES
 
 Proving various examples about the 
 attack trees to ensure our definitions 
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
    ker-vc-sys (P):
     *target: @p4 (vc p4 sys)

    rtm-ker-vc-sys (Q):
     *target: @p3 [a p4 vc +<+ @p4 vc p4 sys]
 ************************
    Proving 
    P <= Q
  * ****************** *)
  Module ker_vc_sys_leq_rtm_ker_vc_sys.
 
  Set Implicit Arguments.

  Inductive measurement : Type :=
  | ms : measurement
  | fin : measurement.

  Inductive adversary : Type :=
  | sys : adversary
  | ker : adversary
  | vc : adversary
  | c : adversary.

(* ATTACK TREES FOR PROTOCOL P *)

  Inductive states_P : Type :=
  | P_sys : states_P 
  | P_ker : states_P
  | P_vc : states_P
  | P_c : states_P
  | P_ms : states_P
  | P_fin : states_P.

  Definition label_P (st : states_P) : measurement + adversary :=
  match st with
  | P_sys => inr sys
  | P_ker => inr ker
  | P_vc => inr vc
  | P_c => inr c
  | P_ms => inl ms
  | P_fin => inl fin
  end.

  (* Five attack trees for P
         a1, a2, a3, a4, a5 *)
  Definition steps_a1 : list (states_P * states_P) := 
      (P_sys, P_fin) ::
      (P_vc, P_fin) ::
      (P_ms, P_vc) ::
      nil.
  
  Definition a1 : attackgraph measurement adversary := 
  {|
      event := states_P ;
      edges := steps_a1 ;
      label := label_P
  |}.

  Definition steps_a2 : list (states_P * states_P) := 
      (P_sys, P_fin) :: 
      (P_ker, P_fin) ::
      (P_ms, P_ker) ::
      nil.
  
  Definition a2 : attackgraph measurement adversary := 
  {|
      event := states_P ;
      edges := steps_a2 ;
      label := label_P
  |}.

  Definition steps_a3 : list (states_P * states_P) := 
      (P_sys, P_fin) :: 
      (P_ms, P_fin) ::
      (P_ker, P_ms) ::
      nil.
  
  Definition a3 : attackgraph measurement adversary := 
  {|
      event := states_P ;
      edges := steps_a3 ;
      label := label_P
  |}.  

  Definition steps_a4 : list (states_P * states_P) := 
      (P_sys, P_fin) :: 
      (P_ms, P_fin) ::
      (P_vc, P_ms) ::
      (P_ker, P_ms) ::
      nil.
  
  Definition a4 : attackgraph measurement adversary := 
  {|
      event := states_P ;
      edges := steps_a4 ;
      label := label_P
  |}.

  Definition steps_a5 : list (states_P * states_P) := 
      (P_sys, P_fin) :: 
      (P_ms, P_fin) ::
      (P_vc, P_ms) ::
      (P_c, P_ms) ::
      nil.
  
  Definition a5 : attackgraph measurement adversary := 
  {|
      event := states_P ;
      edges := steps_a5 ;
      label := label_P
  |}.


 (* Normalize attack trees a3, a4 and a5 *)

 Definition steps_a3' : list (states_P * states_P) := 
    (P_sys, P_fin) ::   
    (P_ker, P_fin) ::
    nil.

Definition a3' : attackgraph measurement adversary := 
{|
    event := states_P ;
    edges := steps_a3' ;
    label := label_P
|}.

Definition steps_a4' : list (states_P * states_P) := 
    (P_sys, P_fin) ::    
    (P_vc, P_fin) ::
    (P_ker, P_fin) ::
    nil.

Definition a4' : attackgraph measurement adversary := 
{|
    event := states_P ;
    edges := steps_a4' ;
    label := label_P
|}.

Definition steps_a5' : list (states_P * states_P) := 
    (P_sys, P_fin) ::    
    (P_vc, P_fin) ::
    (P_c, P_fin) ::
    nil.

Definition a5' : attackgraph measurement adversary := 
{|
    event := states_P ;
    edges := steps_a5' ;
    label := label_P
|}.

Lemma eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
Lemma eqDec_adversary : forall (x y : adversary), {x = y} + {x <> y}.
Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
Lemma eqDec_eventa3: forall (x y : a3.(event _ _)), {x = y} + {x <> y}.
Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
Lemma eqDec_eventa4: forall (x y : a4.(event _ _)), {x = y} + {x <> y}.
Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
Lemma eqDec_eventa5: forall (x y : a4.(event _ _)), {x = y} + {x <> y}.
Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.

Ltac eqDec_edge_left step1 step2 eqDec_event :=
destruct (eqDec_edge eqDec_event step1 step2) as [H|H]; [clear H | contradiction].
Ltac eqDec_edge_right step1 step2 eqDec_event :=
destruct (eqDec_edge eqDec_event step1 step2) as [H|H]; [inversion H | clear H].
Ltac eqDec_event_left st1 st2 eqDec_event :=
destruct (eqDec_event st1 st2) as [H|H]; [clear H | contradiction].
Ltac eqDec_event_right st1 st2 eqDec_event :=
destruct (eqDec_event st1 st2) as [H|H]; [inversion H | clear H].

Lemma a3_reduce1 : 
reduce1 eqDec_eventa3 steps_a3 =
steps_a3'.
Proof.
 unfold reduce1. simpl.
 eqDec_edge_right (P_ms, P_fin) (P_sys, P_fin) eqDec_eventa3.
 eqDec_edge_left (P_ms, P_fin) (P_ms, P_fin) eqDec_eventa3.
 eqDec_edge_right (P_ms, P_fin) (P_ker, P_ms) eqDec_eventa3.
 simpl.
 eqDec_event_right P_fin P_ms eqDec_eventa3.
 eqDec_event_right P_sys P_ms eqDec_eventa3.
 eqDec_event_right P_ker P_ms eqDec_eventa3.
 eqDec_event_left P_ms P_ms eqDec_eventa3.
 unfold steps_a3'. reflexivity.
Qed. 

Lemma a3_reduced : reducer eqDec_eventa3 steps_a3 steps_a3'.
Proof. 
    apply reduce_more.
    + rewrite a3_reduce1. unfold not. intros. inversion H. 
    + rewrite a3_reduce1. apply reduce_done. eauto.
Qed. 

Lemma a4_reduce1 : 
reduce1 eqDec_eventa4 steps_a4 =
steps_a4'.
Proof.
 unfold reduce1. simpl. 
 eqDec_edge_right (P_ms, P_fin) (P_vc, P_ms) eqDec_eventa4.
 eqDec_edge_left (P_ms, P_fin) (P_ms, P_fin) eqDec_eventa4.
 eqDec_edge_right (P_ms, P_fin) (P_sys, P_fin) eqDec_eventa4.
 eqDec_edge_right (P_ms, P_fin) (P_ker, P_ms) eqDec_eventa4.
 simpl.
 eqDec_event_right P_vc P_ms eqDec_eventa4.
 eqDec_event_left P_ms P_ms eqDec_eventa4.
 eqDec_event_right P_sys P_ms eqDec_eventa4.
 eqDec_event_right P_fin P_ms eqDec_eventa4.
 eqDec_event_right P_ker P_ms eqDec_eventa4.
 unfold steps_a4'. reflexivity.
Qed. 

Lemma a4_reduced : reducer eqDec_eventa4 steps_a4 steps_a4'.
Proof. 
    apply reduce_more.
    + rewrite a4_reduce1. unfold not. intros. inversion H. 
    + rewrite a4_reduce1. apply reduce_done. eauto.
Qed. 

Lemma a5_reduce1 : 
reduce1 eqDec_eventa5 steps_a5 =
steps_a5'.
Proof.
 unfold reduce1. simpl. 
 eqDec_edge_right (P_ms, P_fin) (P_vc, P_ms) eqDec_eventa5.
 eqDec_edge_right (P_ms, P_fin) (P_c, P_ms) eqDec_eventa5.
 eqDec_edge_left (P_ms, P_fin) (P_ms, P_fin) eqDec_eventa5.
 eqDec_edge_right (P_ms, P_fin) (P_sys, P_fin) eqDec_eventa5.
 simpl.
 eqDec_event_right P_vc P_ms eqDec_eventa5.
 eqDec_event_right P_c P_ms eqDec_eventa5.
 eqDec_event_left P_ms P_ms eqDec_eventa5.
 eqDec_event_right P_sys P_ms eqDec_eventa5.
 eqDec_event_right P_fin P_ms eqDec_eventa5.
 unfold steps_a5'. reflexivity.
Qed. 

Lemma a5_reduced : reducer eqDec_eventa5 steps_a5 steps_a5'.
Proof. 
    apply reduce_more.
    + rewrite a5_reduce1. unfold not. intros. inversion H. 
    + rewrite a5_reduce1. apply reduce_done. eauto.
Qed.



(* NORMALIZED ATTACK TREES FOR PROTOCOL Q *)

  Inductive states_Q : Type :=
  | Q_sys : states_Q 
  | Q_ker : states_Q
  | Q_vc : states_Q
  | Q_c : states_Q
  | Q_ms : states_Q
  | Q_fin : states_Q.

  Definition label_Q (st : states_Q) : measurement + adversary :=
  match st with
  | Q_sys => inr sys
  | Q_ker => inr ker
  | Q_vc => inr vc
  | Q_c => inr c 
  | Q_ms => inl ms 
  | Q_fin => inl fin
  end.

(* Five attack trees for Q
     b1, b2, b3, b4, b5 *)
     Definition steps_b1 : list (states_Q * states_Q) := 
        (Q_sys, Q_fin) ::
        (Q_vc, Q_fin) ::
        (Q_ms, Q_vc) ::
        nil.
    
    Definition b1 : attackgraph measurement adversary := 
    {|
        event := states_Q ;
        edges := steps_b1 ;
        label := label_Q
    |}.
  
    Definition steps_b2 : list (states_Q * states_Q) := 
        (Q_sys, Q_fin) :: 
        (Q_ker, Q_fin) ::
        (Q_ms, Q_ker) ::
        nil.
    
    Definition b2 : attackgraph measurement adversary := 
    {|
        event := states_Q ;
        edges := steps_b2 ;
        label := label_Q
    |}.
  
    Definition steps_b3 : list (states_Q * states_Q) := 
        (Q_sys, Q_fin) :: 
        (Q_ker, Q_fin) ::
        (Q_ms, Q_ker) ::
        nil.
    
    Definition b3 : attackgraph measurement adversary := 
    {|
        event := states_Q ;
        edges := steps_b3 ;
        label := label_Q
    |}.
  
    Definition steps_b4 : list (states_Q * states_Q) := 
        (Q_sys, Q_fin) :: 
        (Q_vc, Q_fin) ::
        (Q_ker, Q_fin) ::
        (Q_ms, Q_ker) ::
        nil.
    
    Definition b4 : attackgraph measurement adversary := 
    {|
        event := states_Q ;
        edges := steps_b4 ;
        label := label_Q
    |}.
  
    Definition steps_b5 : list (states_Q * states_Q) := 
        (Q_sys, Q_fin) :: 
        (Q_vc, Q_fin) ::
        (Q_c, Q_fin) ::
        nil.
    
    Definition b5 : attackgraph measurement adversary := 
    {|
        event := states_Q ;
        edges := steps_b5 ;
        label := label_Q
    |}.

 

  (* Define isomorphism function *)
  Definition f (x : states_P) : states_Q :=
      match x with 
      | P_sys => Q_sys 
      | P_vc => Q_vc
      | P_ker => Q_ker
      | P_c => Q_c
      | P_ms => Q_ms
      | P_fin => Q_fin
  end.

  Definition g (x : states_Q) : option (states_P) :=
      match x with 
      | Q_sys => Some P_sys 
      | Q_vc => Some P_vc
      | Q_ker => Some P_ker
      | Q_fin => Some P_fin
      | _ => None
  end.

  Definition g' (x : states_Q) : (states_P) :=
      match x with 
      | Q_sys =>  P_sys 
      | Q_vc =>  P_vc
      | Q_ker =>  P_ker
      | Q_fin =>  P_fin
      | _ => P_fin
  end.
  
  Definition P_all :=  a1 :: a2 :: a3' :: a4' :: a5' :: nil .

  Definition Q_all := b1 :: b2 :: b3 :: b4 :: b5 :: nil.

  Ltac cor_in_head := simpl; apply ex_head; auto.
  Ltac cor_in_tail := simpl; apply ex_tail; auto.

  Ltac inversion_any :=
    match goal with
    | [H : _ |- _ ] => inversion H
    end.

  Lemma ker_vc_sys_leq_rtm_ker_vc_sys : supports P_all Q_all.
  Proof.
    unfold supports. intros. simpl in H0. intuition.
    + subst. exists a1. unfold P_all; intuition.  left.
    unfold isomorphism. exists f. unfold f. repeat split; intros.
    ++ destruct st1, st2; try (simpl in *; intuition; inversion_any).
    ++ destruct st1, st2; try (simpl in *; intuition; inversion_any).
    ++ destruct st; auto.
    ++ destruct st1, st2; try reflexivity; inversion_any.
    ++ destruct st'.
    +++ exists P_sys; reflexivity.
    +++ exists P_ker; reflexivity.
    +++ exists P_vc; reflexivity.
    +++ exists P_c; reflexivity.
    +++ exists P_ms; reflexivity.
    +++ exists P_fin; reflexivity.
    + subst. exists a2. unfold P_all; intuition.  left.
        unfold isomorphism. exists f. unfold f. repeat split; intros.
    ++ destruct st1, st2; try (simpl in *; intuition; inversion_any).
    ++ destruct st1, st2; try (simpl in *; intuition; inversion_any).
    ++ destruct st; auto.
    ++ destruct st1, st2; try reflexivity; inversion_any.
    ++ destruct st'.
    +++ exists P_sys; reflexivity.
    +++ exists P_ker; reflexivity.
    +++ exists P_vc; reflexivity.
    +++ exists P_c; reflexivity.
    +++ exists P_ms; reflexivity.
    +++ exists P_fin; reflexivity.
    +  exists a3'. unfold P_all. intuition. right. subst.
        unfold strict_partial_order. intuition. 
    ++  econstructor. 
    +++ simpl. unfold steps_b3. apply ex_head. simpl. intuition.
    +++ econstructor. simpl. unfold steps_b3. apply ex_tail. apply ex_head. simpl. eauto. econstructor.
    ++ econstructor.
    +++ simpl. unfold steps_b3. unfold find_time. simpl. eauto.
    +++ econstructor. simpl. unfold steps_b3. unfold find_time. simpl. eauto.
        econstructor.
    ++ right. unfold time_proper_subset. intuition.
    +++ econstructor.  
    ++++ unfold find_time. simpl. auto.
    ++++ econstructor. unfold find_time. simpl. auto. econstructor.
    +++ invc H; subst. invc H4; subst. invc H5; subst. invc H3; subst.
        invc H0; subst. invc H. invc H0; subst. invc H3; subst. invc H.
        invc H3.
    + subst. exists a4'. unfold P_all. intuition. right. subst.
        unfold strict_partial_order. intuition. 
    ++  econstructor. 
    +++ simpl. unfold steps_b4. apply ex_head. simpl. intuition.
    +++ econstructor. simpl. unfold steps_b4. apply ex_tail. apply ex_head. simpl. eauto. econstructor.
    ++++ simpl. unfold steps_b4. apply ex_tail. apply ex_tail. apply ex_head. simpl. auto. 
    ++++ econstructor.
    ++ econstructor.
    +++ simpl. unfold steps_b4. unfold find_time. simpl. eauto.
    +++ econstructor. simpl. unfold steps_b4. unfold find_time. simpl. eauto.
        econstructor.
    ++++ econstructor.
    ++++ econstructor.
    ++ right. unfold time_proper_subset. intuition.
    +++ econstructor.  
    ++++ unfold find_time. simpl. auto.
    ++++ econstructor. unfold find_time. simpl. auto. econstructor.
    +++++ econstructor.
    +++++ econstructor.
    +++ invc H; subst. invc H4; subst. invc H5; subst. invc H6; subst.
        invc H4; subst. invc H0; subst. invc H. invc H0; subst. invc H4; subst. invc H.
        invc H4. subst. invc H0. invc H. subst. invc H0; subst.
    + subst. exists a5'. unfold P_all; intuition.  left.
    unfold isomorphism. exists f. unfold f. repeat split; intros.
    ++ destruct st1, st2; try (simpl in *; intuition; inversion_any).
    ++ destruct st1, st2; try (simpl in *; intuition; inversion_any).
    ++ destruct st; auto.
    ++ destruct st1, st2; try reflexivity; inversion_any.
    ++ destruct st'.
    +++ exists P_sys; reflexivity.
    +++ exists P_ker; reflexivity.
    +++ exists P_vc; reflexivity.
    +++ exists P_c; reflexivity.
    +++ exists P_ms; reflexivity.
    +++ exists P_fin; reflexivity.
Qed.

End ker_vc_sys_leq_rtm_ker_vc_sys. 





 (* ******************* 
    vc-sys (P):
     *target: @p4 (vc p4 sys)

    a-vc-sys-seq (Q):
     *target: @p3 [a p4 vc +<+ @p4 vc p4 sys]
 ************************
    Proving 
    P <= Q
  * ****************** *)
 Module vc_sys_leq_a_vc_sys_seq. 
 
     Set Implicit Arguments.
 
     Inductive measurement : Type :=
     | ms : measurement
     | fin : measurement.
 
     Inductive adversary : Type :=
     | sys : adversary
     | ker : adversary
     | vc : adversary
     | a : adversary
     | c : adversary.
 
(* ATTACK TREES FOR PROTOCOL P *)

     Inductive states_P : Type :=
     | P_sys : states_P 
     | P_ker : states_P
     | P_vc : states_P
     | P_a: states_P
     | P_c : states_P
     | P_ms : states_P
     | P_fin : states_P.
 
     Definition label_P (st : states_P) : measurement + adversary :=
     match st with
     | P_sys => inr sys
     | P_ker => inr ker
     | P_vc => inr vc
     | P_a => inr a
     | P_c => inr c
     | P_ms => inl ms
     | P_fin => inl fin
     end.
 
     (* Two attack trees for P
            a1 and a2 *)
     Definition steps_a1 : list (states_P * states_P) := 
         (P_sys, P_fin) :: 
         (P_vc, P_fin) ::
         nil.
     
     Definition a1 : attackgraph measurement adversary := 
     {|
         event := states_P ;
         edges := steps_a1 ;
         label := label_P
     |}.
 
     Definition steps_a2 : list (states_P * states_P) := 
         (P_sys, P_fin) :: 
         (P_ker, P_fin) ::
         nil.
     
     Definition a2 : attackgraph measurement adversary := 
     {|
         event := states_P ;
         edges := steps_a2 ;
         label := label_P
     |}.
 
(* ATTACK TREES FOR PROTOCOL Q *)

     Inductive states_Q : Type :=
     | Q_sys : states_Q 
     | Q_ker : states_Q
     | Q_vc : states_Q
     | Q_a : states_Q
     | Q_c : states_Q
     | Q_ms : states_Q
     | Q_fin : states_Q.
 
     Definition label_Q (st : states_Q) : measurement + adversary :=
     match st with
     | Q_sys => inr sys
     | Q_ker => inr ker
     | Q_vc => inr vc
     | Q_a => inr a
     | Q_c => inr c 
     | Q_ms => inl ms 
     | Q_fin => inl fin
     end.
 
(* Two attack trees for Q
        b1, b2, b3, and b4 *)
     Definition steps_b1 : list (states_Q * states_Q) := 
         (Q_ms, Q_vc) :: 
         (Q_vc, Q_fin) ::
         (Q_sys, Q_fin) ::
         nil.
 
     Definition b1 : attackgraph measurement adversary := 
     {|
         event := states_Q ;
         edges := steps_b1 ;
         label := label_Q
     |}.
 
     Definition steps_b2 : list (states_Q * states_Q) := 
         (Q_ms, Q_fin) :: 
         (Q_vc, Q_fin) ::
         (Q_sys, Q_fin) ::
         nil.
 
     Definition b2 : attackgraph measurement adversary := 
     {|
         event := states_Q ;
         edges := steps_b2 ;
         label := label_Q
     |}.
 
     Definition steps_b3 : list (states_Q * states_Q) := 
         (Q_vc, Q_ms) ::
         (Q_a, Q_ms) ::
         (Q_ms, Q_fin) :: 
         (Q_sys, Q_fin) ::
         nil.
 
     Definition b3 : attackgraph measurement adversary := 
     {|
         event := states_Q ;
         edges := steps_b3 ;
         label := label_Q
     |}.
 
     Definition steps_b4 : list (states_Q * states_Q) := 
         (Q_vc, Q_ms) ::
         (Q_c, Q_ms) ::
         (Q_ms, Q_fin) :: 
         (Q_sys, Q_fin) ::
         nil.
 
     Definition b4 : attackgraph measurement adversary := 
     {|
         event := states_Q ;
         edges := steps_b4 ;
         label := label_Q
     |}.
 
     (* Normalize attack trees b2, b3 and b4 *)
 
     Definition steps_b2' : list (states_Q * states_Q) := 
         (Q_vc, Q_fin) ::
         (Q_sys, Q_fin) ::
         nil.
 
     Definition b2' : attackgraph measurement adversary := 
     {|
         event := states_Q ;
         edges := steps_b2' ;
         label := label_Q
     |}.
 
     Definition steps_b3' : list (states_Q * states_Q) := 
         (Q_vc, Q_fin) ::
         (Q_a, Q_fin) ::
         (Q_sys, Q_fin) ::
         nil.
 
     Definition b3' : attackgraph measurement adversary := 
     {|
         event := states_Q ;
         edges := steps_b3' ;
         label := label_Q
     |}.
 
     Definition steps_b4' : list (states_Q * states_Q) := 
         (Q_vc, Q_fin) ::
         (Q_c, Q_fin) ::
         (Q_sys, Q_fin) ::
         nil.
 
     Definition b4' : attackgraph measurement adversary := 
     {|
         event := states_Q ;
         edges := steps_b4' ;
         label := label_Q
     |}.
 
     Lemma eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
     Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
     Lemma eqDec_adversary : forall (x y : adversary), {x = y} + {x <> y}.
     Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
     Lemma eqDec_event2: forall (x y : b2.(event _ _)), {x = y} + {x <> y}.
     Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
     Lemma eqDec_event3: forall (x y : b3.(event _ _)), {x = y} + {x <> y}.
     Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
     Lemma eqDec_event4: forall (x y : b4.(event _ _)), {x = y} + {x <> y}.
     Proof. destruct x, y; try (left; reflexivity); try (right; intros contra; inversion contra). Qed.
 
     Ltac eqDec_edge_left step1 step2 eqDec_event :=
     destruct (eqDec_edge eqDec_event step1 step2) as [H|H]; [clear H | contradiction].
     Ltac eqDec_edge_right step1 step2 eqDec_event :=
     destruct (eqDec_edge eqDec_event step1 step2) as [H|H]; [inversion H | clear H].
     Ltac eqDec_event_left st1 st2 eqDec_event :=
     destruct (eqDec_event st1 st2) as [H|H]; [clear H | contradiction].
     Ltac eqDec_event_right st1 st2 eqDec_event :=
     destruct (eqDec_event st1 st2) as [H|H]; [inversion H | clear H].
 
     Lemma b2_reduce1 : 
     reduce1 eqDec_event2 steps_b2 =
     steps_b2'.
     Proof.
      unfold reduce1. simpl. 
      eqDec_edge_left (Q_ms, Q_fin) (Q_ms, Q_fin) eqDec_event2.
      eqDec_edge_right (Q_ms, Q_fin) (Q_vc, Q_fin) eqDec_event2.
      eqDec_edge_right (Q_ms, Q_fin) (Q_sys, Q_fin) eqDec_event2.
      simpl.
      eqDec_event_right Q_vc Q_ms eqDec_event2.
      eqDec_event_right Q_fin Q_ms eqDec_event2.
      eqDec_event_right Q_sys Q_ms eqDec_event2.
      unfold steps_b2'. reflexivity.
     Qed. 
 
     Lemma b2_reduced : reducer eqDec_event2 steps_b2 steps_b2'.
     Proof. 
         apply reduce_more.
         + rewrite b2_reduce1. unfold not. intros. inversion H. 
         + rewrite b2_reduce1. apply reduce_done. eauto.
     Qed. 
 
     Lemma b3_reduce1 : 
     reduce1 eqDec_event3 steps_b3 =
     steps_b3'.
     Proof.
      unfold reduce1. simpl. 
      eqDec_edge_right (Q_ms, Q_fin) (Q_vc, Q_ms) eqDec_event3.
      eqDec_edge_right (Q_ms, Q_fin) (Q_a, Q_ms) eqDec_event3.
      eqDec_edge_left (Q_ms, Q_fin) (Q_ms, Q_fin) eqDec_event3.
      eqDec_edge_right (Q_ms, Q_fin) (Q_sys, Q_fin) eqDec_event3.
      simpl.
      eqDec_event_right Q_vc Q_ms eqDec_event3.
      eqDec_event_right Q_a Q_ms eqDec_event3.
      eqDec_event_left Q_ms Q_ms eqDec_event3.
      eqDec_event_right Q_sys Q_ms eqDec_event3.
      eqDec_event_right Q_fin Q_ms eqDec_event3.
      unfold steps_b3'. reflexivity.
     Qed. 
 
     Lemma b3_reduced : reducer eqDec_event3 steps_b3 steps_b3'.
     Proof. 
         apply reduce_more.
         + rewrite b3_reduce1. unfold not. intros. inversion H. 
         + rewrite b3_reduce1. apply reduce_done. eauto.
     Qed. 
 
     Lemma b4_reduce1 : 
     reduce1 eqDec_event4 steps_b4 =
     steps_b4'.
     Proof.
      unfold reduce1. simpl. 
      eqDec_edge_right (Q_ms, Q_fin) (Q_vc, Q_ms) eqDec_event4.
      eqDec_edge_right (Q_ms, Q_fin) (Q_c, Q_ms) eqDec_event4.
      eqDec_edge_left (Q_ms, Q_fin) (Q_ms, Q_fin) eqDec_event4.
      eqDec_edge_right (Q_ms, Q_fin) (Q_sys, Q_fin) eqDec_event4.
      simpl.
      eqDec_event_right Q_vc Q_ms eqDec_event4.
      eqDec_event_right Q_c Q_ms eqDec_event4.
      eqDec_event_left Q_ms Q_ms eqDec_event4.
      eqDec_event_right Q_sys Q_ms eqDec_event4.
      eqDec_event_right Q_fin Q_ms eqDec_event4.
      unfold steps_b4'. reflexivity.
     Qed. 
 
     Lemma b4_reduced : reducer eqDec_event4 steps_b4 steps_b4'.
     Proof. 
         apply reduce_more.
         + rewrite b4_reduce1. unfold not. intros. inversion H. 
         + rewrite b4_reduce1. apply reduce_done. eauto.
     Qed.
 
     (* Define isomorphism function *)
     Definition f (x : states_P) : states_Q :=
         match x with 
         | P_sys => Q_sys 
         | P_vc => Q_vc
         | P_ker => Q_ker
         | P_a => Q_a
         | P_c => Q_c
         | P_ms => Q_ms
         | P_fin => Q_fin
     end.
 
     Definition g (x : states_Q) : option (states_P) :=
         match x with 
         | Q_sys => Some P_sys 
         | Q_vc => Some P_vc
         | Q_ker => Some P_ker
         | Q_fin => Some P_fin
         | _ => None
     end.
 
     Definition g' (x : states_Q) : (states_P) :=
         match x with 
         | Q_sys =>  P_sys 
         | Q_vc =>  P_vc
         | Q_ker =>  P_ker
         | Q_fin =>  P_fin
         | _ => P_fin
     end.
     
     Definition P_all :=  a1 :: a2 :: nil .
 
     Definition Q_all := b1 :: b2' :: b3' :: b4' :: nil.
 
     Ltac cor_in_head := simpl; apply ex_head; auto.
     Ltac cor_in_tail := simpl; apply ex_tail; auto.
 
     Ltac inversion_any :=
       match goal with
       | [H : _ |- _ ] => inversion H
       end.
 
     Lemma vc_sys_leq_a1_vc_sys_seq : supports P_all Q_all.
     Proof.
       unfold supports. intros. simpl in H0. intuition.
       + subst. exists a1. unfold P_all; intuition. right.
         unfold strict_partial_order. intuition.
       ++ econstructor. 
       +++ simpl. unfold steps_b1. apply ex_tail. apply ex_tail. apply ex_head. simpl. intuition.
       +++ econstructor. simpl. unfold steps_b1. apply ex_tail. apply ex_head. simpl. eauto. econstructor.
       ++ econstructor.
       +++ simpl. unfold steps_b1. unfold find_time. simpl. eauto.
       +++ econstructor. simpl. unfold steps_b1. unfold find_time. simpl. eauto.
           econstructor.
       ++ right. unfold time_proper_subset. split.
       +++ econstructor.
       ++++ simpl. unfold steps_b1. unfold find_time. simpl. eauto.
       ++++ econstructor. simpl. unfold steps_b1. unfold find_time. simpl. eauto.
           econstructor.
       +++ unfold not. intros. invc H. subst. simpl in *. invc H2. subst.
           simpl in *. destruct H0. inversion H0. subst. invc H0. subst. 
           destruct H1. simpl in *. invc H. subst. invc H1.
       + subst. exists a1. unfold P_all. intuition. left.
         unfold isomorphism. exists f. unfold f. repeat split; intros.
       ++ destruct st1, st2; try (simpl in *; intuition; inversion_any).
       ++ destruct st1, st2; try (simpl in *; intuition; inversion_any).
       ++ destruct st; auto.
       ++ destruct st1, st2; try reflexivity; inversion_any.
       ++ destruct st'.
       +++ exists P_sys; reflexivity.
       +++ exists P_ker; reflexivity.
       +++ exists P_vc; reflexivity.
       +++ exists P_a; reflexivity.
       +++ exists P_c; reflexivity.
       +++ exists P_ms; reflexivity.
       +++ exists P_fin; reflexivity.
       + exists a1. unfold P_all. intuition. right. subst.
         unfold strict_partial_order. intuition. 
       ++  econstructor. 
       +++ simpl. unfold steps_b3'. apply ex_tail. apply ex_tail. apply ex_head. simpl. intuition.
       +++ econstructor. simpl. unfold steps_b3'. apply ex_head. simpl. eauto. econstructor.
       ++ econstructor.
       +++ simpl. unfold steps_b3'. unfold find_time. simpl. eauto.
       +++ econstructor. simpl. unfold steps_b3'. unfold find_time. simpl. eauto.
           econstructor.
       ++ left. unfold adv_proper_subset. intuition.
       +++ econstructor.  
       ++++ simpl. unfold steps_b3'. apply ex_tail. apply ex_tail. apply ex_head. simpl. intuition.
       ++++ econstructor. simpl. unfold steps_b3'. apply ex_head. simpl. eauto. econstructor.
       +++ invc H. subst. invc H4. subst. invc H1. subst. invc H0.
           subst. invc H0. subst. invc H1. invc H1.
       +  exists a1. unfold P_all. intuition. right. subst.
       unfold strict_partial_order. intuition. 
     ++  econstructor. 
     +++ simpl. unfold steps_b3'. apply ex_tail. apply ex_tail. apply ex_head. simpl. intuition.
     +++ econstructor. simpl. unfold steps_b3'. apply ex_head. simpl. eauto. econstructor.
     ++ econstructor.
     +++ simpl. unfold steps_b3'. unfold find_time. simpl. eauto.
     +++ econstructor. simpl. unfold steps_b3'. unfold find_time. simpl. eauto.
         econstructor.
     ++ left. unfold adv_proper_subset. intuition.
     +++ econstructor.  
     ++++ simpl. unfold steps_b3'. apply ex_tail. apply ex_tail. apply ex_head. simpl. intuition.
     ++++ econstructor. simpl. unfold steps_b3'. apply ex_head. simpl. eauto. econstructor.
     +++ invc H. subst. invc H4. subst. invc H1. subst. invc H0.
         subst. invc H0. subst. invc H1. invc H1.
  Qed.
 
 End vc_sys_leq_a_vc_sys_seq. 