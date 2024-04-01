Require Import Coq.Lists.List.

(*************************
 ** ATTACK GRAPHS 
 ** Represented as a record type parameterized over 
 ** measurement and adversary events *)
Record attackgraph (measurement adversary : Type) : Type := 
{
    event : Type ;
    edges : list (event * event) ;
    label : event -> measurement + adversary
}.