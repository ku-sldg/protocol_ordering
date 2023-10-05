Require Import Coq.Lists.List.

(* Attack graph is parameterized over measurement and corruption events *)
Record attackgraph (measurement corruption : Type) : Type := 
{
    state : Type ;
    steps : list (state * state) ;
    label : state -> measurement + corruption
}.


Definition get_steps {meas cor : Type} (a : attackgraph meas cor) := a.(steps _ _).

(* Assumptions: 
 * - complete : every set of attack graphs is complete (has every possible graph) *)