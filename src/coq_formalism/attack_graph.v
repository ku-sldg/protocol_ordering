Require Import Coq.Lists.List.

(*************************
 ** ATTACK GRAPHS 
 ** Represented as a record type parameterized over 
 ** measurement and adversary events *)
Record attackgraph (measurement adversary : Type) : Type := 
{
    state : Type ;
    steps : list (state * state) ;
    label : state -> measurement + adversary
}.