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

Section Reducer.

    Context {measurement : Type}.
    Context {corruption : Type}.
    (* Context {G : attackgraph measurement corruption}.*)

    (* Labels and States must have decidable equality *)
    Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
    Hypothesis eqDec_corruption : forall (x y : corruption), {x = y} + {x <> y}.
    Hypothesis eqDec_state :  forall (G : attackgraph measurement corruption) (x y : G.(state _ _)), {x = y} + {x <> y}.

    (* steps are equivalent or not equivalent *)
    Lemma eqDec_step : forall (G : attackgraph measurement corruption) (x y : (G.(state _ _) * G.(state _ _))), {x = y} + {x <> y}.
    Proof.
        intros G x y;
        destruct x as [stx stx']; destruct y as [sty sty'].
        destruct eqDec_state with (G := G) (x:=stx) (y:=sty).
        + destruct eqDec_state with (x:=stx') (y:=sty').
        ++ subst. left. eauto.  
        ++ right. intros contra. rewrite pair_equal_spec in contra. destruct contra. contradiction.
        + destruct eqDec_state with (x:=stx') (y:=sty').
        ++ right. intros contra. rewrite pair_equal_spec in contra. destruct contra. contradiction.
        ++ right. intros contra. rewrite pair_equal_spec in contra. destruct contra. contradiction.
    Qed.

    (* list of steps are decidably equal *)
    Lemma eqDec_list_steps: forall `{G : attackgraph measurement corruption} (x y : list (G.(state _ _) * G.(state _ _))), {x = y} + {x <> y}.
    Proof.
        intros G. apply list_eq_dec. apply eqDec_step.
    Qed.

    Fixpoint replace_measurement_incomplete {G: attackgraph measurement corruption} (Steps : list (G.(state _ _) * G.(state _ _))) (st st' : (G.(state _ _))) : 
                                 list (G.(state _ _) * G.(state _ _)) := 
        match Steps with 
        | (st1, st2) :: Steps' => if (eqDec_state G st st2)
                                  then (st1, st') :: replace_measurement_incomplete Steps' st st' 
                                  else (st1, st2) :: replace_measurement_incomplete Steps' st st'
        | nil => Steps 
        end. 

    (* Replace all occurences of st by st' in Steps *)
    Fixpoint replace_measurement {G : attackgraph measurement corruption} (Steps : list (G.(state _ _) * G.(state _ _))) 
    (st st' : G.(state _ _)) : 
    list (G.(state _ _) * G.(state _ _)) :=
    match Steps with
    | (st1, st2) :: Steps' => 
        if (eqDec_state G st1 st)
        then if (eqDec_state G st2 st)
            then (st', st') :: replace_measurement Steps' st st'
            else (st', st2) :: replace_measurement Steps' st st'
        else if (eqDec_state G st2 st)
            then (st1, st') :: replace_measurement Steps' st st'
            else (st1, st2) :: replace_measurement Steps' st st'
    | nil => Steps
    end.
    
    Print eqDec_step.
    Print remove.

    Fixpoint find_measurement {G : attackgraph measurement corruption} (AllSteps Steps : list (G.(state _ _) * G.(state _ _))) :  list (G.(state _ _) * G.(state _ _)) := 
    match Steps with 
    | (st, st') :: Steps' => match (G.(label _ _) st) with 
                             | inr c1 => find_measurement AllSteps Steps' 
                             | inl m1 => match (G.(label _ _) st') with 
                                         (* if both m1 and m2 are measurement events then you can replace them *)
                                         | inl m2 => replace_measurement (remove (eqDec_step _ ) (st, st') AllSteps) st st' 
                                         | _ => find_measurement AllSteps Steps'
                                         end
                             end
    | nil => AllSteps
    end.

    (* finding measurement x in x should return x? *)
    Lemma find_measurement_helper : forall (G : attackgraph measurement corruption) (x : list(G.(state _ _) * G.(state _ _))), find_measurement x x = x.
    Proof.
        intros. induction x.
        + auto.
        + (* simpl. destruct a. destruct (G.(label _ _) s) eqn:l_a .
        ++ destruct (G.(label _ _) s0) eqn:l_a2.
        +++ simpl in *. destruct ((eqDec_step G) (s, s0) (s, s0)).
        ++++ simpl. unfold remove. unfold replace_measurement.*)
    Abort.

    Definition reduce1 `{G : attackgraph measurement corruption} (Steps : list (G.(state _ _) * G.(state _ _))) : list (G.(state _ _) * G.(state _ _)) :=
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
    Inductive reducer {G : attackgraph measurement corruption} : list (G.(state _ _) * G.(state _ _)) -> list (G.(state _ _) * G.(state _ _)) -> Prop :=
    | reduce_done : forall x, reduce1 x = x -> reducer x x
    | reduce_more : forall x y, reduce1 x <> x -> reducer (reduce1 x) y -> reducer x y.  

    Definition reduce_graph g1 := reducer (g1.(steps _ _)).  

    (* a graph may always reduce to itself *)
    Theorem reducer_refl : forall (G : attackgraph measurement corruption) (x : list(G.(state _ _) * G.(state _ _))), reducer x x.
    Proof.
        intros.
        induction x.
        + econstructor. unfold reduce1. eauto.
        + apply reduce_done. unfold reduce1. 
    Abort.
    (* Proof is hard and might not be possible? *)


    (* if a graph reduces from x to y and then y to z then you can say x reduces to z *)
    Theorem  reducer_trans : forall (G : attackgraph measurement corruption) (x : list(G.(state _ _) * G.(state _ _))) (y : list(G.(state _ _) * G.(state _ _))) , reducer x y -> forall (z : list(G.(state _ _) * G.(state _ _))) , reducer y z -> reducer x z.
    Proof.
        intros G x y Hxy. induction Hxy.
        + eauto.
        + intros. apply reduce_more; eauto.
    Qed.

    (* prove reducer is total... ie it holds for any two lists *)

    Print eqDec_step.
    Print reducer. 

    Theorem  reducer_total : forall (G : attackgraph measurement corruption) (x : list(G.(state _ _) * G.(state _ _))) (y : list(G.(state _ _) * G.(state _ _))), reducer x y.
    Proof.
        intros. induction x.
        + econstructor. eauto. 
        pose proof list_eq_dec.
        pose proof (eqDec_step G).
        induction X with (A := (state measurement corruption G * state measurement corruption G )) (l := x) (l' := y).
        intuition.

        
    Qed.
    




End Reducer.