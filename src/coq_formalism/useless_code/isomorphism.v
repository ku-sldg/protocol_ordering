Require Import Coq.Lists.List.


(* Attack graph is parameterized over measurement and corruption events *)
Record attackgraph (measurement corruption : Type) : Type := 
{
    state : Type ;
    steps : list (state * state) ;
    label : state -> measurement + corruption
}.

(************************
    A DIFFERENT WAY
   TO DEFINE ISOMORPHISM 

   as motivated by 
   https://www.tildedave.com/2019/07/18/formalizing-lagranges-theorem-in-coq.html 
   ************************)

   Definition ListInjective' (A B: Type) (f: A -> B) (l: list A) :=
    (forall x y: A, In x l -> In y l -> f x = f y -> x = y).

   (* Definition ListInjective (g1 : attackgraph measurement corruption) (g2: attackgraph measurement corruption) (f : g1.(state _ _) -> g2.(state _ _)) (l :list (state measurement corruption g1 * state measurement corruption g1))  :=
    (forall x y, In x l -> In y l -> f x = f y -> x = y).*)
  
  Definition ListSurjective' (A B: Type) (f: A -> B) (l: list B) (l': list A) :=
    (forall x: B, In x l -> exists y, In y l' /\ f y = x).

  Definition ListSurjective (g1 : attackgraph measurement corruption) (g2: attackgraph measurement corruption) (f : g1.(state _ _) -> g2.(state _ _)) l l' :=
    (forall x, In x l -> exists y, In y l' /\ f y = x).

  Definition ListLabelPreserve (g1 : attackgraph measurement corruption) (g2: attackgraph measurement corruption) (f : g1.(state _ _) -> g2.(state _ _)) :=  
    (forall st1 st2, In (st1,st2) g1.(steps _ _) -> 
    g1.(label _ _) st1 = g2.(label _ _) (f st1) /\ g1.(label _ _) st2 = g2.(label _ _) (f st2)).
  
  Definition ListIsomorphism' (A B: Type) (f: A -> B) (l1: list A) (l2: list B) :=
    ListInjective' f l1 /\
    ListSurjective' f l2 l1 /\
    (forall d, In d l1 -> In (f d) l2).

(************************
    A DIFFERENT WAY
   TO DEFINE ISOMORPHISM 

    BIJECTIVE HOMOMORPHISM 
   ************************)


  (* injective = one-to-one*)
Definition injective `{g1 : attackgraph measurement corruption } `{g2: attackgraph measurement corruption} (f : g1.(state _ _) -> g2.(state _ _)) := forall x y, (f x = f y) -> x = y. 
(* surjective = onto *)
Definition surjective `{g1 : attackgraph measurement corruption } `{g2: attackgraph measurement corruption} (f : g1.(state _ _) -> g2.(state _ _)) := forall x, exists y,  x = f y. 
Definition bijective `{g1 : attackgraph measurement corruption } `{g2: attackgraph measurement corruption} (f : g1.(state _ _) -> g2.(state _ _)) := injective f /\ surjective f.

Lemma inverse {X Y : attackgraph measurement corruption} (f : (X.(state _ _)) -> (Y.(state _ _))) :
  bijective f -> {g : (Y.(state _ _)) -> (X.(state _ _)) | (forall x, g (f x) = x) /\
                               (forall y, f (g y) = y) }.
Proof.
intros [inj sur].
apply constructive_definite_description.
assert (H : forall y, exists! x, f x = y).
{ intros y.
  destruct (sur y) as [x xP].
  exists x; split; trivial. eauto.
  intros x' x'P.
  apply inj. rewrite <- xP. eauto. }
exists (fun y => proj1_sig (constructive_definite_description _ (H y))).
split.
- split.
  + intros x.
    destruct (constructive_definite_description _ _).
    simpl.
    now apply inj.
  + intros y.
    now destruct (constructive_definite_description _ _).
- intros g' [H1 H2].
  apply functional_extensionality.
  intros y.
  destruct (constructive_definite_description _ _) as [x e].
  simpl.
  now rewrite <- e, H1.
Qed.
    
  Definition isomorphism' (G1 : attackgraph measurement corruption) (G2: attackgraph measurement corruption) : Prop := 
  (exists (f : G1.(state _ _) -> G2.(state _ _)), homomorphism G1 G2 f /\ bijective f).

  Theorem isomorphism'_refl : forall g1, isomorphism' g1 g1.
  Proof.
    intros. unfold isomorphism'. exists (fun x => x).
    split.
    + simpl in *. unfold homomorphism. intros.  eauto. 
    + unfold bijective. unfold injective, surjective.
    split.
    ++ intros.  eauto.
    ++ intros. eexists; eauto.
  Qed.

  Theorem isomorphism'_sym : forall g1 g2, isomorphism' g1 g2 -> isomorphism' g2 g1.
  Proof.
    intros. unfold isomorphism' in *.
    destruct H as [fg1g2 H]. destruct H.
    pose proof (inverse H0). destruct X as [fg2g1 X]. destruct X as [ g1inv g2inv].
    exists fg2g1. split.
    + unfold bijective, homomorphism in *. intuition.
    ++ clear H2.  unfold injective, surjective in *. 
       assert (H' : surjective fg1g2). { eauto. }
       unfold surjective in H'.
       specialize H3 with st1. destruct H3 as [st1'].
       specialize H' with st2. destruct H' as [st2'].
       specialize H1 with st1' st2'.
       intuition. admit.
  Abort.   