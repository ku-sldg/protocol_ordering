(**** Labeled Graph Homomorphism 
      By: Anna Fritz 
      Date: July 18, 2023 
      
      Definitions and Properties taken from Paul Rowe's paper: 
        "On Orderings in Security Models" *)

Require Import Coq.Classes.RelationClasses. 
Require Import Coq.Relations.Relation_Definitions.

Module LabeledGraphHomomorphism. 

(* A directed, labeled, acyclic graph consists of : 
    - N : a finite set of nodes
    - E : finite set of edges 
    - l : labeling function from nodes to some set of labels  *)

Class graph (N L : Set ) := {
    E : N -> N -> Prop ;
    l : N -> L
}.

(* Graph homomorphism is a mapping between graphs that 
    respects the graph's structure.
    
    Given two graphs, there exists some mapping over the vertices such that every edge*)
Class labeled_graph_homomorphism (NG: Set) (NH: Set) (l':Set) `{G : graph NG l'} `{H : graph NH l'} := {
    f : NG -> NH ;
    edge_relation : forall v v', 
            E v v' -> 
            E (f v) (f v') ;
    label_relation : forall n, 
            l n = l (f n)
}.
(* In this definition, need to assume the graphs have the same set of labels *)


Module Example_Chase_m1_m1. 
(****************************************
   Example from Chase model finder output 
   with protocols sys1 and ker_vc-sys-seq *)

   (* graphs must have the same set of labels *)
   Inductive labels : Set := 
   | start'
   | sys' 
   | vc'
   | meas'. 

   (* set of vertices of the graph *)
   Inductive ng := 
   | start : ng 
   | sys : ng 
   | vc : ng 
   | meas : ng.
   
   (* edges of the sys graph*)
   Inductive eg : ng -> ng -> Prop := 
   | start_meas_g : eg start meas
   | sys_meas_g : eg sys meas
   | vc_meas_g : eg vc meas.

   Definition lg (n: ng) : labels :=
   match n with 
   | start => start'
   | sys => sys' 
   | vc => vc'
   | meas => meas'
   end.  
   
   #[global] Instance G : graph ng labels := {E := eg ; l := lg }.
   
   (* set of vertices of the graph *)
   Inductive nh := 
   | start_h : nh 
   | sys_h : nh 
   | vc_h : nh 
   | meas_h : nh.
   
   (* edges of the sys graph*)
   Inductive eh : nh -> nh -> Prop := 
   | start_meas_h : eh start_h meas_h
   | sys_meas_h : eh sys_h meas_h
   | vc_meas_h : eh vc_h meas_h
   | start_vc : eh start_h vc_h. 

   Definition lh (n: nh) : labels :=
   match n with 
   | start_h => start'
   | sys_h => sys' 
   | vc_h => vc' 
   | meas_h => meas'
   end.  
   
   #[global] Instance H : graph nh labels := {E := eh ; l := lh }.

   Print reflexive. 
   
   (* reflexive mapping function *)
   Definition mapping' (v : ng): nh := 
     match v with 
     | start => start_h 
     | sys => sys_h
     | vc => vc_h
     | meas => meas_h
   end.

   Print labeled_graph_homomorphism.
   
   (* proving there is a homomorphism between m1 (left) and m1 (right) *)
   #[local] Instance m1_m1_homomorphism : labeled_graph_homomorphism ng nh labels.
   Proof.
     exists mapping'; intros. 
     + inversion H0; try (simpl; econstructor).
     + induction n; simpl; reflexivity.   
   Qed.
   
   End Example_Chase_m1_m1.

End LabeledGraphHomomorphism.

