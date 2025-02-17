Require Import Coq.Lists.List.

Require Import Order.utilities.ltacs.
Require Import Order.utilities.lists.
Require Import Order.utilities.existsb.
Require Import Order.utilities.labelSubsets.
Require Import Order.utilities.supports.

Require Import Order.attacktree.
Require Import Order.attacktree_normalization.
Require Import Order.attacktree_ordering.
Require Import Order.set_minimization.
Require Import Order.set_ordering.


Section ProtocolOrdering.
    Context {components : Type}.

    Inductive orderT : Type :=
    | equiv : orderT
    | leq : orderT
    | geq : orderT
    | incomparable : orderT.


    Definition order_fix (P Q : list (attacktree components)) : orderT :=
    if (equivDec P Q) then equiv else
    if (leqDec P Q)   then leq else
    if (leqDec Q P)   then geq else
                           incomparable.

End ProtocolOrdering.
