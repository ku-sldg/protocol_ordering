(*************************
 File contains example labeled transition systems
 to ensure out definition of weak bisimulation
 is correct. 

 To run this file, you must ensure you comile simulation.v 
 using "coqc simulation.v". Once completed, the file should
 load propertly. 
 
 By: Anna Fritz
 Date: August 25th, 2023 *)


Require Import simulation.

Print weakSimulation.
Print LTS.

(* set of labels *)
Inductive label : Set := 
| l_vc
| l_sys 
| l_ms4
| r_vc.

Inductive state_m1a : Set := 
| vc1 
| sys1 
| ms41.

Inductive init_m1a : state_m1a -> Prop := 
| m1a_sys : init_m1a sys1
| m1a_vc : init_m1a vc1.

Inductive step_m1a : state_m1a -> state_m1a -> Prop := 
| sys_ms4 : step_m1a sys1 ms41
| vc_ms4 : step_m1a vc1 ms41. 

Check sl.

Definition labeling_m1a (s : state_m1a) : label + sl :=
match s with 
| vc1 => inl l_vc
| sys1 => inl l_sys
| ms41 => inl l_ms4
end.

Definition m1a_LTS : LTS := {|
    st := state_m1a ; 
    initial := init_m1a ;
    step := step_m1a ;
    l := labeling_m1a
|}.











