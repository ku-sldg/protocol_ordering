(************************
 * comparison over sets of
 * attack graphs 
 *************************)

Require Import Coq.Lists.List.

Require Import Order.attack_graph.
Require Import Order.strict_partial_order.
Require Import Order.reduce.
Require Import Order.equiv.
Require Import Order.utilities.
Require Import Order.partial_order.
Require Import Order.set_equiv.
Require Import Order.supports.

Section Compare.

  Context {measurement : Type}.
  Context {corruption : Type}. 

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

  Inductive compare (g1 g2 : list (attackgraph measurement corruption)) : ord -> Prop :=
  | lte' : supports g1 g2 -> compare g1 g2 lte
  | gte' : supports g2 g1 -> compare g1 g2 gte
  | eq' : set_eq g1 g2 -> compare g1 g2 eq
  | incomp' : ~ supports g1 g2 -> ~ supports g2 g1 -> ~ set_eq g1 g2 -> compare g1 g2 incomp.

End Compare.