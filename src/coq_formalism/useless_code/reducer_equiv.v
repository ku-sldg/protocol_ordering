  (*******************************
   * Want to check equivalence of 
   * reduced graphs *)
  (******************)
  (* TODO two graphs are equal if you first reduce then prove isomorphic 
   * reduce x to y 
   * reduce a to b 
   * prove the reduced form is also isomorphic *)

   Section Reducer_Equivalence. 

   Import Equivalence.
 
   Context {measurement : Type}.
   Context {adversary : Type}.
   Context {G1 : attackgraph measurement adversary}.
   Context {G2 : attackgraph measurement adversary}.
 
   (* Labels and States must have decidable equality *)
   Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
   Hypothesis eqDec_adversary : forall (x y : adversary), {x = y} + {x <> y}.
   Hypothesis eqDec_state1 : forall (x y : G1.(state _ _)), {x = y} + {x <> y}.
   Hypothesis eqDec_state2 : forall (x y : G2.(state _ _)), {x = y} + {x <> y}.
   
   Print reducer.
   
   (* isomorphism of reduced graphs *) 
   Definition reducer_isomorphism (y : list(G1.(state _ _) * G1.(state _ _))) 
                                  (b : list(G2.(state _ _) * G2.(state _ _))) := 
   ((reducer eqDec_state1 (G1.(steps _ _)) y) /\ reducer eqDec_state2 (G2.(steps _ _)) b) ->
   isomorphism (step_update G1 y) (step_update G2 b).
 
   (* want to prove this is also an equivalence relation *)
   (* Theorem reducer_isomorphism_refl : forall b z, reducer_isomorphism b b.
   Proof.
     intuition. 
   Abort.
   
   Theorem reducer_isomorphism_sym : forall a b, reducer_isomorphism a b -> reducer_isomorphism b a.
   Proof.
   Abort. 
   
   
   Theorem reducer_isomorphism_trans : forall G1 G2 G3 a b c, (reducer_isomorphism G1 G2 a b /\ reducer_isomorphism G2 G3 b c) -> reducer_isomorphism G1 G3 a c.
   Proof.
     intuition.
     unfold reducer_isomorphism in *.
     intuition. simpl in *.
     (* we have nothing about the fact that G2 actually reduces to b *)
     (* I'm not sure how to solve this problem ... *)
   Abort. *) 
 
 End Reducer_Equivalence.