Lemma conjunctionDec : forall (P Q : Prop),
    {P} + {~P} ->
    {Q} + {~Q} ->
    {P /\ Q} + {~ (P /\ Q)}.
Proof.
    intros P Q PDec QDec; destruct PDec, QDec;
    try (right; intros contra; destruct contra; contradiction);
    left; split; auto.
Defined.

Lemma disjunctionDec : forall (P Q : Prop),
    {P} + {~P} ->
    {Q} + {~Q} ->
    {P \/ Q} + {~ (P \/ Q)}.
Proof.
    intros P Q PDec QDec; destruct PDec, QDec;
    try (left; auto; fail);
    right; intros contra; destruct contra; contradiction.
Defined.


Lemma negationDec : forall (P : Prop),
    {P} + {~P} ->
    {~P} + {~~P}.
Proof.
    intros P PDec; destruct PDec;
    [ right; intros contra; contradiction
    | left; auto].
Defined.
