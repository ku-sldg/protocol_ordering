
Require Import Coq.Lists.List.




Ltac inv H := inversion H; subst; clear H.

Ltac destruct_iso HIso :=
    destruct HIso as [f HIso];
    destruct HIso as [HBij HIso];
    destruct HBij as [HInj HSur];
    destruct HIso as [HEdg HLab].

