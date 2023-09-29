(***************************
  Various Ltac code *)

Ltac invc H := inversion H; clear H.  

Ltac inv H := inversion H; subst.

Ltac invsc H := inversion H; subst; clear H. 

Ltac dest_sp H v := destruct H as [v]; intuition.

Ltac destruct_all q2 q3 q' H1 := destruct H1 as [q2 H1];  destruct H1 as [q3 H1];  destruct H1 as [q']; intuition.

Ltac exists_all q1 q2 q' := exists q1; exists q2; exists q'.