(******************************
Trying to reduce graph before comparison 

Assumptions 
1. Measurement events are not predicatable by an adversary
2. Adversary does not know future measurement events 

By: Sarah Johnson and Anna Fritz
Date: Sept 11, 2023 *)

(* TODO: prove the isomorphism is an equivalence relation 
         - equivalence to only take into consideration states in the steps *)

Require Import Coq.Lists.List.

(* Attack graph is parameterized over measurement and corruption events *)
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

    (* steps are equivalent or not equivalent *)
    Lemma eqDec_step : forall (x y : G.(state _ _) * G.(state _ _)), {x = y} + {x <> y}.
    Proof.
        intros x y;
        destruct x as [stx stx']; destruct y as [sty sty'].
        destruct eqDec_state with (x:=stx) (y:=sty).
        + destruct eqDec_state with (x:=stx') (y:=sty').
        ++ subst. left. eauto.  
        ++ right. intros contra. rewrite pair_equal_spec in contra. destruct contra. contradiction.
        + destruct eqDec_state with (x:=stx') (y:=sty').
        ++ right. intros contra. rewrite pair_equal_spec in contra. destruct contra. contradiction.
        ++ right. intros contra. rewrite pair_equal_spec in contra. destruct contra. contradiction.
    Qed.

    (* list of steps are decidably equal *)
    Lemma eqDec_list_steps: forall (x y : list (G.(state _ _) * G.(state _ _))), {x = y} + {x <> y}.
    Proof.
        apply list_eq_dec. apply eqDec_step.
    Qed.

    Fixpoint replace_measurement_incomplete (Steps : list (G.(state _ _) * G.(state _ _))) (st st' : (G.(state _ _))) : 
                                 list (G.(state _ _) * G.(state _ _)) := 
        match Steps with 
        | (st1, st2) :: Steps' => if (eqDec_state st st2)
                                  then (st1, st') :: replace_measurement_incomplete Steps' st st' 
                                  else (st1, st2) :: replace_measurement_incomplete Steps' st st'
        | nil => Steps 
        end. 

    (* Replace all occurences of st by st' in Steps *)
    Fixpoint replace_measurement (Steps : list (G.(state _ _) * G.(state _ _))) 
    (st st' : G.(state _ _)) : 
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

    Lemma replace_measurement_same : forall Steps st st', 
    replace_measurement_incomplete Steps st st' = replace_measurement Steps st st'.
    Proof.
        intros. simpl. induction Steps. 
        + eauto.
        + simpl. rewrite IHSteps. simpl.
        (* although I think replace_measurement_incomplete is sufficient... I can't prove they are the same. *)
    Abort.

    (* Inductively defined replace_measurement *)
    Inductive replace_measurement' (Steps : list (G.(state _ _) * G.(state _ _))) (st st' : G.(state _ _)) : list (G.(state _ _) * G.(state _ _)) -> Prop := 
    | TheEnd : replace_measurement' Steps st st' nil.
    
    Fixpoint find_measurement (AllSteps Steps : list (G.(state _ _) * G.(state _ _))) : 
                                list (G.(state _ _) * G.(state _ _)) := 
    match Steps with 
    | (st, st') :: Steps' => match (G.(label _ _) st) with 
                             | inr c1 => find_measurement AllSteps Steps' 
                             | inl m1 => match (G.(label _ _) st') with 
                                         (* if both m1 and m2 are measurement events then you can replace them *)
                                         | inl m2 => replace_measurement (remove eqDec_step (st, st') AllSteps) st st' 
                                         | _ => find_measurement AllSteps Steps'
                                         end
                             end
    | nil => AllSteps
    end.
        
    Definition reduce1 (Steps : list (G.(state _ _) * G.(state _ _))) : list (G.(state _ _) * G.(state _ _)) :=
    find_measurement Steps Steps.

    (* We cannot define a recursive fixpoint because of 
     * Coq's termination checker since it's not obvious 
     * the list is getting smaller. Instead, we must write 
     * an inductively defined proposition to express that 
     * the graphs eventually reduce. This definition relies
     * on reduce1 to state that if reduce1 returns itself 
     * then the graph cannot be further reduced. If reduce1
     * does not return itself, then the reduction call is
     * recursed. *)
    Inductive reducer : list (G.(state _ _) * G.(state _ _)) -> list (G.(state _ _) * G.(state _ _)) -> Prop :=
    | reduce_done : forall x, reduce1 x = x -> reducer x x
    | reduce_more : forall x y, reduce1 x <> x -> reducer (reduce1 x) y -> reducer x y.  

    Theorem  reducer_trans : forall x y, reducer x y -> forall z, reducer y z -> reducer x z.
    Proof.
        intros x y Hxy. induction Hxy.
        + eauto.
        + intros. apply reduce_more; eauto.
    Qed.
    (* want reducer to be more similiar to equivalence *)  

End Reducer.

(**************************
    STRICTLY LESS THAN 
 **************************)

Section Comparison. 

Context {measurement : Type}.
Context {corruption : Type}.
(* need two attack graphs for comparison now *)
Context {G : attackgraph measurement corruption}.
Context {G2 : attackgraph measurement corruption}.

(* Labels and States must have decidable equality *)
Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
Hypothesis eqDec_corruption : forall (x y : corruption), {x = y} + {x <> y}.
Hypothesis eqDec_state : forall (x y : G.(state _ _)), {x = y} + {x <> y}.

Print eqDec_step.

Fixpoint existsb ( A : Type) (f : A -> Prop) (l:list A) : Prop := 
    match l with 
      | nil => False
      | a::l => f a \/ existsb A f l
    end.

    (* fun st2 => G2.(label _ _) st2 = inr c *) 

(* corruption events of x are a subset of corruption events in y *)
Fixpoint subset {G1 G2 : attackgraph measurement corruption} 
                (x : list (G1.(state _ _) * G1.(state _ _))) (y : list (G2.(state _ _) * G2.(state _ _))) : Prop :=
  match x with 
  | nil => True
  | (st, _ ) :: xs => match (G1.(label _ _) st) with 
                     | inr c => existsb _ (fun step => match step with 
                                                       | (st2, _ ) => G2.(label _ _) st2 = inr c
                                                       end) y                
                     (* existsb _ (fun st2 => G2.(label _ _) st2 = inr c) (fst (split y)) *)
                     | _ => subset xs y 
                     end
  end.

  Definition proper_subset (x: list (G.(state _ _) * G.(state _ _))) (y:list (G2.(state _ _) * G2.(state _ _))) := subset x y /\ ~ subset y x. 

(* We say a is strictly less than b (a < b) if 
 * 1. b has more corruption events 
 * OR 
 * 2. b has more time constrained corruption events  *)

 (* define strictly less for corruption events as a proper subset relation *) 


End Comparison.

(**************************
    EQUIVALENCE
 **************************)

Section Equivalence. 

(* We aim to say two graphs are equivalent if thier reduced forms are isomorphic *)

End Equivalence. 


(*   Class strict_partial_order {X : Type} (R : relation X) := {
    irreflexive := forall a : X, ~ R a a ; 
    asymmetric := forall a b : X, R a b -> ~ R b a ;
    transitive := forall a b c: X, R a b -> R b c -> R a c 
  }. 
  *)

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
    eqDec_step_right (m, m') (s, m4).
    eqDec_step_right (m, m') (k, m4).
    simpl.
    eqDec_state_right m' m.
    eqDec_state_right k m.
    eqDec_state_right s m.
    eqDec_state_right m4 m.
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

Definition steps_m5b : list (state_m5c * state_m5c) := 
    (c, m') ::
    (v, m') ::
    (m', m4) ::
    (s, m4) ::
    nil.


Definition m5b : attackgraph measurement corruption := 
{|
    state := state_m5c ;
    steps := steps_m5b ;
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