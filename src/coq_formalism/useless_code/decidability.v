(* TODO ... from graph_equiv.v *)
Theorem homomorphism_dec : forall g1 g2, 
{exists f, homomorphism g1 g2 f} + {~ exists f, homomorphism g1 g2 f}.
Proof.
  intros. unfold homomorphism. 
  pose proof in_dec_steps g1 as in_g1.  
  pose proof in_dec_steps g2 as in_g2. 
  pose proof step_eq_dec g2 as step_dec_g2.
  pose proof step_eq_dec g1 as step_dec_g1.
  destruct g1 as [g1_state g1_steps g1_lab]. 
  destruct g2 as [g2_state g2_steps g2_lab].
  simpl in *.
  induction g2_steps.
  (* g2 steps is nil *)
  + simpl. destruct g1_steps eqn:H'.
  (* g1 steps also nil *)
  ++ simpl. left. eexists. split. intros. invc H.
     intros. invc H.
  (* g2 nil and g1 not nil *)
  ++ simpl in *. right. unfold not. intros. invc H. invc H0. subst. destruct p.
     specialize H with g g0. intuition.
  (* g2 steps not nil *)
  + destruct IHg2_steps.
  ++ admit.
  ++ unfold not in n.  destruct n.   
Abort.  