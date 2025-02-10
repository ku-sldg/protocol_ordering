Require Import Coq.Lists.List.


Section Supports.
(*
    Context {X : Type}.
    Context {preorder : X -> X -> Prop}.

    Hypothesis preorder_reflexive : 
        forall x, preorder x x.
    Hypothesis preorder_transitive : 
        forall x y z, preorder x y -> preorder y z -> preorder x z.

    Hypothesis preorderDec : 
        forall x y, {preorder x y} + {~ preorder x y}.
*)

    Definition supports {X : Type} (order : X -> X -> Prop) (S T : list X) : Prop :=
        forall H, In H T ->
        exists G, In G S /\ order G H.

    Hint Unfold supports : core.

    Lemma supports_reflexive : forall X (order : X -> X -> Prop), 
        (forall x, order x x) ->
        forall S, supports order S S.
    Proof.
        intros X order HRefl S H HIn;
        exists H; split; auto.
    Qed.

    Lemma supports_transitive : forall X (order : X -> X -> Prop), 
        (forall x y z, order x y -> 
                       order y z -> 
                       order x z) ->
        forall S T U, supports order S T ->
                      supports order T U ->
                      supports order S U.
    Proof.
        intros X order HTrans S T U HST HTU u HIn;
        apply HTU in HIn; destruct HIn as [t HIn]; destruct HIn as [HIn];
        apply HST in HIn; destruct HIn as [s HIn]; destruct HIn;
        exists s; split; auto; eapply HTrans; eauto.
    Qed.



    Fixpoint getRelatedElement_fix 
            {X : Type} (order : X -> X -> Prop) (orderDec : forall x y, {order x y} + {~ order x y}) H S : 
        Prop :=
    match S with 
    | G::S' => if (orderDec G H)
               then True 
               else getRelatedElement_fix order orderDec H S'
    | nil => False
    end.

(*
How does this differ from the previous function??
Particularly if order is a fixpoint?
*)

    Fixpoint getRelatedElement_fix'
            {X : Type} (order_fix : X -> X -> Prop) H S : 
        Prop :=
    match S with 
    | G::S' => order_fix G H \/ getRelatedElement_fix' order_fix H S'
    | nil => False
    end.



    Fixpoint supports_fix 
            {X : Type} (order : X -> X -> Prop) (orderDec : forall x y, {order x y} + {~ order x y}) S T : 
        Prop :=
    match T with
    | H::T' => getRelatedElement_fix order orderDec H S /\ supports_fix order orderDec S T'
    | nil => True
    end.

    Lemma getRelatedElement_exists : forall X (order : X -> X -> Prop) orderDec H S,
        getRelatedElement_fix order orderDec H S <->
        exists G, In G S /\ order G H.
    Proof.
        intros X order orderDec H S; split; intros HRel.
        - induction S; simpl in HRel; try (inversion HRel; fail);
          destruct (orderDec a H).
        -- exists a; split; simpl; auto.
        -- apply IHS in HRel; destruct HRel as [G HRel]; destruct HRel;
           exists G; split; simpl; auto.
        - induction S; simpl; destruct HRel as [G HRel]; destruct HRel as [HIn HOrd];
          try (inversion HIn; fail);
          destruct (orderDec a H); auto;
          destruct HIn; subst; try contradiction;
          apply IHS; exists G; split; auto.
    Qed.


    Lemma supports_same : forall X (order : X -> X -> Prop) orderDec S T,
        supports_fix order orderDec S T <->
        supports order S T.
    Proof.
        intros X order orderDec S T; split; intros HSup.
        - intros H HIn; induction T; try (inversion HIn; fail);
          simpl in HSup; destruct HSup; destruct HIn; subst;
          [ eapply getRelatedElement_exists | apply IHT ]; eauto.
        - induction T; simpl; auto; split;
          [ apply getRelatedElement_exists
          | apply IHT; intros H HIn ];
          apply HSup; simpl; auto.
    Qed.

End Supports.