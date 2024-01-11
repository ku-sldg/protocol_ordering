(******************************
     GRAPH NORMALIZATION

 Here we create "reducer" which 
 reduces graphs to normal form 
 to better reason about their 
 equivalence. 

By: Sarah Johnson and Anna Fritz
Date: Sept 11, 2023 *)

Require Import Coq.Lists.List.
Require Export Order.attack_graph.
Require Import Order.utilities.

Section Reducer.

    Context {measurement : Type}.
    Context {corruption : Type}.
    Context {G : attackgraph measurement corruption}.

    (* Labels and States must have decidable equality *)
    Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
    Hypothesis eqDec_corruption : forall (x y : corruption), {x = y} + {x <> y}.
    Hypothesis eqDec_state :  forall (x y : G.(state _ _)), {x = y} + {x <> y}.

    (* steps are equivalent or not equivalent *)
    Lemma eqDec_step : forall (x y : (G.(state _ _) * G.(state _ _))), {x = y} + {x <> y}.
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
        intros G0. apply list_eq_dec. apply eqDec_step.
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

    Fixpoint find_measurement (AllSteps Steps : list (G.(state _ _) * G.(state _ _))) :  list (G.(state _ _) * G.(state _ _)) := 
    match Steps with 
    | (st, st') :: Steps' => match (G.(label _ _) st) with 
                             | inr c1 => find_measurement AllSteps Steps' 
                             | inl m1 => match (G.(label _ _) st') with 
                                         (* if both m1 and m2 are measurement events then you can replace them *)
                                         | inl m2 => replace_measurement (remove (eqDec_step ) (st, st') AllSteps) st st' 
                                         | _ => find_measurement AllSteps Steps'
                                         end
                             end
    | nil => AllSteps
    end.

    (* finding measurement x in x should return x? *)
    Lemma find_measurement_helper : forall (x : list(G.(state _ _) * G.(state _ _))), find_measurement x x = x.
    Proof.
        intros. induction x.
        + auto.
        + (* simpl. destruct a. destruct (G.(label _ _) s) eqn:l_a .
        ++ destruct (G.(label _ _) s0) eqn:l_a2.
        +++ simpl in *. destruct ((eqDec_step G) (s, s0) (s, s0)).
        ++++ simpl. unfold remove. unfold replace_measurement.*)
    Abort.

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

    Definition step_update (g1 : attackgraph measurement corruption) (newSteps : list (g1.(state _ _) * g1.(state _ _))) :=  {| state := g1.(state _ _) ; steps := newSteps ; label := g1.(label _ _) |}. 

    Theorem  reducer_deterministic : forall (x y z : list (G.(state _ _) * G.(state _ _))), 
        reducer x y -> reducer x z -> y = z.
    Proof.
        intros.
        generalize dependent z.
        induction H.
        + intros. inversion H0; subst; eauto.
          contradiction.
        + intros. inversion H1; subst.
        ++ contradiction.
        ++ apply IHreducer. eauto.
    Qed.
    
    (* if a graph reduces from x to y and then y to z then you can say x reduces to z *)
    Theorem  reducer_trans : forall (x : list(G.(state _ _) * G.(state _ _))) (y : list(G.(state _ _) * G.(state _ _))) , reducer x y -> forall (z : list(G.(state _ _) * G.(state _ _))) , reducer y z -> reducer x z.
    Proof.
        intros x y Hxy. induction Hxy.
        + eauto.
        + intros. apply reduce_more; eauto.
    Qed.

End Reducer.