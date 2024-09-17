(******************************
     ATTACK TREE NORMALIZATION

 Here we create "reducer" which 
 reduces attack trees to normal form. 

By: Sarah Johnson and Anna Fritz
Date: Sept 11, 2023 *)

Require Import Coq.Lists.List.
Require Export Order.attack_graph.
Require Import Order.utilities.

Section Reducer.

    Context {measurement : Type}.
    Context {adversary : Type}.
    Context {G : attackgraph measurement adversary}.

    (* Labels and Events must have decidable equality *)
    Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
    Hypothesis eqDec_adversary : forall (x y : adversary), {x = y} + {x <> y}.
    Hypothesis eqDec_event :  forall (x y : G.(event _ _)), {x = y} + {x <> y}.

    (* Edges have decidable equality *)
    Lemma eqDec_edge : forall (x y : (G.(event _ _) * G.(event _ _))), {x = y} + {x <> y}.
    Proof.
        intros x y;
        destruct x as [stx stx']; destruct y as [sty sty'].
        destruct eqDec_event with (x:=stx) (y:=sty).
        + destruct eqDec_event with (x:=stx') (y:=sty').
        ++ subst. left. eauto.  
        ++ right. intros contra. rewrite pair_equal_spec in contra. destruct contra. contradiction.
        + destruct eqDec_event with (x:=stx') (y:=sty').
        ++ right. intros contra. rewrite pair_equal_spec in contra. destruct contra. contradiction.
        ++ right. intros contra. rewrite pair_equal_spec in contra. destruct contra. contradiction.
    Qed.

    (* Lists of edges have decidable equality *)
    Lemma eqDec_list_edges : forall (x y : list (G.(event _ _) * G.(event _ _))), {x = y} + {x <> y}.
    Proof.
        intros G0. apply list_eq_dec. apply eqDec_edge.
    Qed.

    (* Replace all occurences of st by st' in edges *)
    Fixpoint replace_measurement (edges : list (G.(event _ _) * G.(event _ _))) 
    (st st' : G.(event _ _)) : 
    list (G.(event _ _) * G.(event _ _)) :=
    match edges with
    | (st1, st2) :: edges' => 
        if (eqDec_event st1 st)
        then if (eqDec_event st2 st)
            then (st', st') :: replace_measurement edges' st st'
            else (st', st2) :: replace_measurement edges' st st'
        else if (eqDec_event st2 st)
            then (st1, st') :: replace_measurement edges' st st'
            else (st1, st2) :: replace_measurement edges' st st'
    | nil => edges
    end.

    (* Find consecutive measurement events *)
    (* Then replace the former measurement event by the latter *)
    Fixpoint find_measurement (Alledges edges : list (G.(event _ _) * G.(event _ _))) :  list (G.(event _ _) * G.(event _ _)) := 
    match edges with 
    | (st, st') :: edges' => match (G.(label _ _) st) with 
                             | inr c1 => find_measurement Alledges edges' 
                             | inl m1 => match (G.(label _ _) st') with 
                                         (* if both m1 and m2 are measurement events then you can replace m1 with m2 *)
                                         | inl m2 => replace_measurement (remove (eqDec_edge ) (st, st') Alledges) st st' 
                                         | _ => find_measurement Alledges edges'
                                         end
                             end
    | nil => Alledges
    end.

    (* Perform one step of the normalization process *)
    Definition reduce1 (edges : list (G.(event _ _) * G.(event _ _))) : list (G.(event _ _) * G.(event _ _)) :=
    find_measurement edges edges.


    (* We cannot define a recursive fixpoint because of 
     * Coq's termination checker since it's not obvious 
     * the list is getting smaller. Instead, we must write 
     * an inductively defined proposition to express that 
     * the attack trees eventually reduce. This definition 
     * relies on reduce1. If reduce1 returns itself 
     * then the attack tree cannot be further reduced. If 
     * reduce1 does not return itself, then the reduction 
     * call is repeated. *)
    Inductive reducer : list (G.(event _ _) * G.(event _ _)) -> list (G.(event _ _) * G.(event _ _)) -> Prop :=
    | reduce_done : forall x, reduce1 x = x -> reducer x x
    | reduce_more : forall x y, reduce1 x <> x -> reducer (reduce1 x) y -> reducer x y.  


    Theorem  reducer_deterministic : forall (x y z : list (G.(event _ _) * G.(event _ _))), 
        reducer x y -> 
        reducer x z -> 
        y = z.
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
    
    Theorem  reducer_trans : forall (x : list(G.(event _ _) * G.(event _ _))) (y : list(G.(event _ _) * G.(event _ _))) , 
        reducer x y -> 
        forall (z : list(G.(event _ _) * G.(event _ _))), reducer y z -> 
        reducer x z.
    Proof.
        intros x y Hxy. induction Hxy.
        + eauto.
        + intros. apply reduce_more; eauto.
    Qed.

End Reducer.