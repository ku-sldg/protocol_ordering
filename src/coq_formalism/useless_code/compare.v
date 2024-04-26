(************************
 * COMPARE SETS 
 * top level file used to
 * obtain over sets of
 * attack graphs 
 *************************)

Require Import Coq.Lists.List.

Require Import Order.attack_graph.
Require Import Order.graph_strict_partial_order.
Require Import Order.graph_normalization.
Require Import Order.graph_equiv.
Require Import Order.utilities.
Require Import Order.graph_partial_order.
Require Import Order.set_equiv.
Require Import Order.set_order.

Section Compare.

  Context {measurement : Type}.
  Context {adversary : Type}. 

  (* 4 mutually exclusive ordering relations 
   * less than or equal to 
   * greater than or equal to 
   * equal 
   * incomparable *)

  Inductive ord := 
  | lte 
  | gte 
  | eq
  | incomp. 

  Inductive compare (g1 g2 : list (attackgraph measurement adversary)) : ord -> Prop :=
  | lte' : supports g1 g2 -> compare g1 g2 lte
  | gte' : supports g2 g1 -> compare g1 g2 gte
  | eq' : set_eq g1 g2 -> compare g1 g2 eq
  | incomp' : ~ supports g1 g2 -> ~ supports g2 g1 -> ~ set_eq g1 g2 -> compare g1 g2 incomp.

End Compare.