(**** Labeled Graph Homomorphism 
      By: Anna Fritz 
      Date: July 18, 2023 
      
      Defining supports and covers and other interesting 
      properties taken from Paul Rowe's paper: 
      "On Orderings in Security Models" *)

Require Import Coq.Relations.Relations.       
Require Import Coq.Sets.Ensembles.

From mathcomp Require Import ssreflect.

(* Defining supports and covers over a general homomorphism *)
Module homomorphism. 

  Context {L : Set}.  

  (* could make L implicit since it exists in the context... maybe should optimize once finished *)
  Class graph := {
    N : Set ; 
    E : N -> N -> Prop ;
    l : N -> L
  }.

  (* preorder over graphs  *)
  Definition homomorphism (G : graph) (H : graph) (f : G.(N) -> H.(N)) : Prop := 
      forall v v', E v v' -> E (f v) (f v') /\
      forall n, l n = l (f n).
 
  Print homomorphism. 

  Notation "x < y" := (homomorphism x y) (at level 70). 

  (* Properties over homomorphisms *)
  Lemma  homomorphism_refl : forall x, exists (f : N -> N), (x < x) f .
  Proof.
      intros. unfold homomorphism. exists (fun x => x). split; intros; eauto.
  Qed.   

  Lemma  homomorphism_trans : forall x y z, 
      ( exists (fxy: N-> N), (x < y) fxy ) -> 
      ( exists (gyz: N-> N), (y < z) gyz ) -> 
      exists (hxz: N-> N), (x < z) hxz.
  Proof.
      intros x y z Hxy Hyz. 
      intros.
      destruct Hxy as [fxy xy]. destruct Hyz as [gyz yz].
      unfold homomorphism in *. 
      exists (fun x => gyz (fxy (x))).
      intros v v'' H; split.
      + specialize xy with v v''.
        destruct xy. eauto.
        specialize yz with (fxy v) (fxy v'').
        destruct yz. eauto.
        eauto.  
      + intros. 
        specialize xy with v v''.
        destruct xy. eauto.
        specialize H1 with n. rewrite H1. 
        specialize yz with (fxy v) (fxy v'').
        destruct yz. eauto.
        specialize H3 with (fxy n).
        rewrite H3.
        eauto.  
    Qed. 

  (********** 
      COVERS 
     *********)

  Definition covers (TT : Ensemble graph) (SS : Ensemble graph) : Prop := 
      forall (G : graph), In _ SS G ->
      ( exists (H : graph), In _ TT H /\ exists f, homomorphism G H f ) .

  Inductive downward_closure (SS P : Ensemble graph) : graph -> Prop := 
  | dc : Included _ SS P -> 
        forall G, In _ P G -> 
        (exists H, In _ SS H /\ exists f, homomorphism G H f) -> 
        downward_closure SS P G. 
  
  (* Could define downward closure as a subset... 
     but I'm not sure what they gets us*)
  Definition dc_subset (SS P : Ensemble graph) := 
    Included _ SS P -> 
    forall G, In _ P G -> 
    { G : graph | (exists H, In _ SS H /\ exists f, homomorphism G H f)}.


  (********** 
      SUPPORTS 
     *********)

  Definition supports (SS : Ensemble graph) (TT : Ensemble graph) : Prop := 
      forall (H : graph), In _ TT H ->
      ( exists (G : graph), In _ SS G /\ exists f, homomorphism G H f ) .

  Lemma supports_refl : forall SS, supports SS SS.
    unfold supports. intros. exists H; split; eauto. apply homomorphism_refl.
  Qed.
  
  Lemma supports_trans : forall SS TT PP, supports SS TT -> supports TT PP -> supports SS PP.
     unfold supports. intros SS TT PP Hst Htp h' Hh'.
     specialize Htp with h'.
     destruct Htp; eauto.
     specialize Hst with x.
     destruct Hst. destruct H; eauto.
     destruct H. destruct H0.
     exists x0; split; eauto.
     apply homomorphism_trans with (y := x); eauto.
  Qed. 

  Inductive upward_closure (SS PP : Ensemble graph) : graph -> Prop := 
  | uc : Included _ SS PP -> 
      forall H, In _ PP H -> 
      (exists G, In _ SS G /\ exists f, homomorphism G H f) -> 
      upward_closure SS PP H. 


  Lemma subset_dc : forall P SS: Ensemble graph, 
     Included _ SS P -> Included _ SS (downward_closure SS P).
  Proof.
      intros. unfold Included.
      intros. unfold In. simpl in *. apply dc.
      + eauto.
      + unfold Included in H. apply H. eauto.
      + exists x. split. 
      ++ eauto.
      ++ apply homomorphism_refl. 
  Qed.

  Lemma subset_uc : forall P SS: Ensemble graph, 
  Included _ SS P -> Included _ SS (upward_closure SS P).
  Proof.
    intros. unfold Included.
    intros. unfold In. simpl in *. apply uc.
    + eauto.
    + unfold Included in H. apply H. eauto.
    + exists x. split. 
    ++ eauto.
    ++ apply homomorphism_refl. 
    Qed.

  Ltac inv H := inversion H; subst.
  Ltac invc H := inversion H; subst; clear H. 
  Ltac incl H1 x := unfold Included in H1; specialize H1 with x.
  Ltac cov H1 x := unfold covers in H1; specialize H1 with x.

  (* Proving the downward closure of S is a subset of the downward closure of T iff T covers S *)
  Theorem three : forall SS TT PP, 
  Included _ SS PP -> Included _ TT PP -> 
  Included _ (downward_closure SS PP) (downward_closure TT PP) <-> covers TT SS.
  Proof.
      split; intros.
      (* dc implies covers... this is proved by the definition of covers *)
      + unfold covers. intros. 
        unfold Included in H1.
        apply subset_dc in H.
        unfold Included in H. 
        apply subset_dc in H0.
        unfold Included in H0.
        eapply H1 in H; eauto.
        destruct H. apply H4.  
      (* covers implies dc *)
      + unfold Included. intros K H2. apply dc. 
      ++ eauto.
      ++ inversion H2. eauto.
      ++ unfold covers in H1.
         destruct H2.
         destruct H4.
         destruct H4. apply H1 in H4.
         destruct H4. destruct H4.
         exists x0. split; eauto.
         apply homomorphism_trans with (y := x); eauto.
Qed. 

  (* Proving the upward closure of S is a subset of the upward closure of T iff T supports S *)
  Theorem three' : forall SS TT PP, 
          Included _ SS PP -> Included _ TT PP -> 
          Included _ (upward_closure SS PP) (upward_closure TT PP) <-> supports TT SS.
  Proof.
    split; intros.
    (* uc implies supports... this is proved by the definition of supports *)
    + unfold supports. intros. 
      apply subset_uc in H.
      apply subset_uc in H0.
      unfold Included in *.
      eapply H1 in H; eauto.
      destruct H. apply H5.  
    (* supports implies uc *)
    + unfold Included. intros K H2. apply uc. 
    ++ eauto.
    ++ inversion H2. eauto.
    ++ unfold supports in H1.
       destruct H2.
       destruct H5.
       destruct H5. apply H1 in H5.
       destruct H5. destruct H5.
       exists x0. split; eauto.
       apply homomorphism_trans with (y := x); eauto.
Qed.

End homomorphism.

(* Need to make the set of nodes of the graph finite to prove that the homomorphism is a partial order
 * (ie : reflexive : a <= a 
 *       antisymmetric : a <= b & b <= a -> a = b 
         transitive : a <= b & b <= c -> a <= c ) *)

(* As stated from Paul : 
 * If we only allow injective homomorphisms, then the preorder is actually a partial order (up to isomorphism) because injective homomorphisms in both directions between (finite) graphs G and H imply that G and H are isomorphic. *)

From mathcomp Require Import fintype.
Check finType.

Module finite_homomorphism.

Context {L : Set}.  

  (* could make L implicit since it exists in the context... maybe should optimize once finished *)
  Class graph := {
    N : Set ; 
    E : N -> N -> Prop ;
    l : N -> L
  }.
  
  (* Properties over the function *)
  Definition injective (G : graph) (H: graph) (f : G.(N) -> H.(N)) := forall x y : N, (f x = f y) -> x = y. 
  Definition surjective (G : graph) (H: graph) (f : G.(N) -> H.(N)) := forall x, exists y,  x = f y. 
  Definition bijective (G : graph) (H: graph) (f : G.(N) -> H.(N)) := injective G H f /\ surjective G H f. 

  (* preorder over graphs  *)
  Definition homomorphism (G : graph) (H : graph) (f : G.(N) -> H.(N)) : Prop := 
      injective G H f /\  
      forall v v', E v v' -> E (f v) (f v') /\
      forall n, l n = l (f n).

  (* An isomorphism is a bijection that is also a homomorphism *)
  Definition isomorphism (G : graph) (H : graph) (f : G.(N) -> H.(N)) : Prop := 
    surjective G H f /\ homomorphism G H f.

  Notation "x <= y" := (homomorphism x y) (at level 70).
  Notation "x h= y" := (isomorphism x y) (at level 70).

   (* Properties over homomorphisms *)
   Lemma  homomorphism_refl : forall x, exists (f : N -> N), (x <= x) f .
   Proof.
       intros. unfold homomorphism. exists (fun x => x). split; intros; eauto.
       unfold injective.
       intros. eauto. 
   Qed.   
 
   Lemma  homomorphism_trans : forall x y z, 
       ( exists (fxy: N-> N), (x <= y) fxy ) -> 
       ( exists (gyz: N-> N), (y <= z) gyz ) -> 
       exists (hxz: N-> N), (x <= z) hxz.
   Proof.
       intros x y z Hxy Hyz. 
       intros.
       destruct Hxy as [fxy xy]. destruct Hyz as [gyz yz].
       unfold homomorphism in *. 
       exists (fun x => gyz (fxy (x))).
       split.
       + inversion xy. inversion yz.
         unfold injective in *.
         intros. clear H0. clear H2.
         apply H. specialize H1 with (fxy x0) (fxy y0).
         apply H1. eauto.
       + intros v v'' H; split; destruct xy as [ H1 xy]; clear H1; destruct yz as [H2 yz]; clear H2.
       ++ specialize xy with v v''.
         destruct xy. eauto.
         specialize yz with (fxy v) (fxy v'').
         destruct yz. eauto.
         eauto.  
       ++ intros. 
         specialize xy with v v''.
         destruct xy. eauto.
         specialize H1 with n. rewrite H1. 
         specialize yz with (fxy v) (fxy v'').
         destruct yz. eauto.
         specialize H3 with (fxy n).
         rewrite H3.
         eauto.  
     Qed.   
        
   Lemma homomorphism_antisym : forall x y, 
        ( exists f, (x <= y) f ) ->  
        ( exists g, (y <= x) g ) -> 
         exists h, (x h= y) h.
    Proof.
      unfold homomorphism. unfold isomorphism.
      intros.
      destruct H as [fxy H].
      destruct H as [fxy_inj H].
      destruct H0 as [gyx H0].
      destruct H0 as [gyx_inj H0].
      unfold surjective. unfold homomorphism.
      exists fxy. split.
      + clear H. clear H0.  unfold injective in *.
        intros y0.
        assert (Hinv : exists fxy_inv, (forall x, fxy_inv (fxy x) = x) /\ (forall y, fxy (fxy_inv y) = y) ).
        { 

        }
        remember (gyx x0) as y0. exists y0. subst.
        specialize fxy_inj with b (gyx b).   

       eauto.
      split.
      split.

      destruct fxy_inj.
      destruct H as [fxy_edge fxy_lab].  
    
        
(* change function to a map  

  map is finite and the map is total 
   - map as a list so map is finite 
   - *)
(* TO DOs:  Prove supports and covers are a preorder *)
