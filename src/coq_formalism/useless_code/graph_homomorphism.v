(**** Graph homomorphism 
      By: Anna Fritz 
      Date: July 13, 2023 *)

Require Import Coq.Classes.RelationClasses. 
Require Import Coq.Relations.Relation_Definitions.

Module GraphHomomorphism. 

(* Classify types of graphs 
   - set of vertices
   - set of edges *)

Class graph (vertex : Set ) := {
      edge : vertex -> vertex -> Prop
}.

(* Graph homomorphism is a mapping between graphs that 
   respects the graph's structure.
   
   Given two graphs, there exists some mapping over the vertices such that every edge*)
Class graph_homomorphism (V V': Set) (G : graph V) (G' : graph V') := {
      f : V -> V' ;
      edge_relation : forall v v', 
            edge v v' -> 
            edge (f v) (f v')
}.


(****************************************
   Example of graph homomorphism from 
   https://www.geeksforgeeks.org/graph-homomorphism/ 
   Modified slightly. *)

Module Example_gfg. 

Inductive g_vert : Set := 
| a : g_vert 
| b : g_vert 
| c : g_vert
| d : g_vert 
| e : g_vert.

Inductive g_edge : g_vert -> g_vert -> Prop := 
| a_b : g_edge a b
| b_c : g_edge b c 
| c_d : g_edge c d
| d_e : g_edge d e
| e_a : g_edge e a.

(* first graph g *)
#[local] Instance g : graph g_vert := { edge := g_edge }.

Inductive g'_vert : Set := 
| x : g'_vert
| y : g'_vert 
| z : g'_vert.

Inductive g'_edge : g'_vert -> g'_vert -> Prop := 
| x_y : g'_edge x y 
| y_z : g'_edge y z 
| z_x : g'_edge z x
| x_z : g'_edge x z.

(* second graph g' *)
#[local] Instance g' : graph g'_vert := { edge := g'_edge}.

(* function to relate g and g' *)
Definition mapping (v : g_vert): g'_vert := 
  match v with 
  | a => x 
  | b => y 
  | c => z 
  | d => x 
  | e => z
end.

(* prove homomorphism between g and g' *)
#[local] Instance g_g'_homomorphism : graph_homomorphism g_vert g'_vert g g'.
Proof. 
  exists mapping.
  intros. inversion H; try (simpl; econstructor).
Qed.

End Example_gfg.

(****************************************
   Example from Chase model finder output 
   with protocols sys1 and ker_vc-sys-seq *)
Module Example_Chase_m1_m1. 

(* set of vertices of the graph *)
Inductive m_vert := 
| start : m_vert 
| sys : m_vert 
| vc : m_vert 
| meas : m_vert.

(* edges of the sys graph*)
Inductive m_edge_left : m_vert -> m_vert -> Prop := 
| start_meas_l : m_edge_left start meas
| sys_meas_l : m_edge_left sys meas
| vc_meas_l : m_edge_left vc meas.

(* edges of the ker_vc-sys-seq graph *)
Inductive m_edge_right : m_vert -> m_vert -> Prop := 
| start_meas_r : m_edge_right start meas
| sys_meas_r : m_edge_right sys meas
| vc_meas_r : m_edge_right vc meas
| start_vc_r : m_edge_right start vc.

#[global] Instance m1_left : graph m_vert := {edge := m_edge_left}.

#[local] Instance m1_right : graph m_vert := {edge := m_edge_right}.

(* reflexive mapping function *)
Definition mapping' (v : m_vert): m_vert := 
  match v with 
  | start => start 
  | sys => sys
  | vc => vc
  | meas => meas
end.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

(* proving there is a homomorphism between m1 (left) and m1 (right) *)
#[local] Instance m1_m1_homomorphism : graph_homomorphism m_vert m_vert m1_left m1_right.
Proof.
  exists mapping'.
  intros. inversion H; try (simpl; econstructor).
Qed.

End Example_Chase_m1_m1.

(****************************************
   Example from Chase model finder output 
   with protocols sys1 (model 1) 
   and ker_vc-sys-seq (model 2) *)

Module Example_Chase_m1_m2.

(* set of vertices of the graph *)
Inductive m_vert := 
| start : m_vert 
| sys : m_vert 
| vc : m_vert 
| meas : m_vert
| ker : m_vert.

(* edges of left model 1*)
Inductive m_edge_left : m_vert -> m_vert -> Prop := 
| start_meas_l : m_edge_left start meas
| sys_meas_l : m_edge_left sys meas
| vc_meas_l : m_edge_left vc meas.

(* define edges for right model 2 *)
Inductive m_edge_right_2 : m_vert -> m_vert -> Prop := 
| start_meas_r_2 : m_edge_right_2 start meas
| sys_meas_r_2 : m_edge_right_2 sys meas
| ker_meas_r_2 : m_edge_right_2 ker meas
| start_vc_r_2 : m_edge_right_2 start ker.

#[global] Instance m1_left : graph m_vert := {edge := m_edge_left}.

#[local] Instance m2_right : graph m_vert := {edge := m_edge_right_2}. 

(* reflexive mapping function *)
Definition mapping (v : m_vert): m_vert := 
  match v with 
  | start => start 
  | sys => sys
  | vc => vc
  | meas => meas
  | ker => ker
end.

(* This proof doesn't complete because there is no edge relation in the right graph between vc and meas *)
#[local] Instance m1_m2_homomorphism : graph_homomorphism m_vert m_vert m1_left m2_right.
  exists mapping.
  intros; inversion H; try (simpl; econstructor).
  + simpl. 
Abort.

(* However, we could define a new mapping function and the proof would complete *)
Definition mapping' (v : m_vert): m_vert := 
  match v with 
  | start => start 
  | sys => sys
  | vc => ker
  | meas => meas
  | ker => ker
end.

#[local] Instance m1_m2_homomorphism : graph_homomorphism m_vert m_vert m1_left m2_right.
  exists mapping'.
  intros; inversion H; try (simpl; econstructor).
Qed.
(* Now the proof completes. I'm not sure how we could disallow this mapping between vc and ker because a homomorphism says that a mapping must simply exist so to say there is not a homomorphism would mean that no mapping exists (which is not the case here).

I think we want to disallow a relationship between m1_left and m2_right because the vc node on the left is not represented on the right. 

Maybe we should consider a subset relation between graphs or adding labels to the homomorphism. 
*)

End Example_Chase_m1_m2.

