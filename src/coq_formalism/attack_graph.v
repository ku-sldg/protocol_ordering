Require Import Coq.Lists.List.

(*************************
 ** ATTACK GRAPHS 
 ** Represented as a record type parameterized over 
 ** measurement and corruption events *)
Record attackgraph (measurement corruption : Type) : Type := 
{
    state : Type ;
    steps : list (state * state) ;
    label : state -> measurement + corruption
}.