(**************************
    STRICT PARTIAL ORDER
    OVER ATTACK TREES
    parameterized over 
    an arbitrary adversary 
    event ordering
 **************************)

Require Import Coq.Lists.List.
Require Export Order.attack_graph.
Require Import Order.utilities.

 Section Parameterized_Strict_Partial_Order. 

 Context {measurement : Type}.
 Context {adversary : Type}.

 Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
 Hypothesis eqDec_adversary : forall (x y : adversary), {x = y} + {x <> y}.
 Hypothesis eqDec_event : forall (G : attackgraph measurement adversary) (x y : G.(event _ _)), {x = y} + {x <> y}.

(* Attack tree ordering is parameterized over an adversary event ordering *)
Context {adv_event_spo : adversary -> adversary -> Prop}.
 
(* The ordering is a strict partial order *)
Hypothesis adv_event_spo_irrefl : forall (x : adversary), ~ adv_event_spo x x.
Hypothesis adv_event_spo_asym : forall (x y :adversary), adv_event_spo x y -> ~ adv_event_spo y x.
Hypothesis adv_event_spo_trans : forall (x y z : adversary), adv_event_spo x y -> adv_event_spo y z -> adv_event_spo x z.

Definition event_spo (x y : measurement + adversary) : Prop :=
    match x, y with
    | inr c1, inr c2 => adv_event_spo c1 c2
    | inl m, _ => False
    | _, inl m => False
    end.

(********
   Facts about existsb *)
 Fixpoint existsb ( A : Type) (f : A -> Prop) (l:list A) : Prop := 
     match l with 
       | nil => False
       | a::l => f a \/ existsb A f l
     end.
 
 Inductive existsb_ind ( A : Type) (f : A -> Prop) : (list A) -> Prop :=
 | ex_head : forall a l, f a -> existsb_ind _ f (a::l)
 | ex_tail : forall a l, existsb_ind _ f l -> existsb_ind _ f (a::l).
 
 
 (* Prove if inductive definition holds then fixpoint definition also holds *)
 Lemma existsb_ind_impl_fix : forall A f l, existsb_ind A f l -> existsb A f l.
 Proof.
     intros. induction H.
     + simpl. left. eauto.
     + simpl. right. eauto.  
 Qed.
 
 (* Prove if fixpoint definition holds then inductive definition also holds *)
 Lemma existsb_fix_impl_ind : forall A f l, existsb A f l -> existsb_ind A f l.
 Proof.
     intros. induction l.
     + simpl in *. inversion H.
     + simpl in *. inversion H.
     ++ apply ex_head. eauto.
     ++ apply ex_tail. apply IHl. eauto.  
 Qed.
 
 (* existsb holds iff there exists some element in the list, x, such that f x holds *)
 Lemma existsb_exists :
   forall (A : Type) (f : A -> Prop) (l:list A), existsb _ f l <-> exists x, In x l /\ f x.
 Proof.
   induction l; simpl; intuition; firstorder.
   subst; auto.
 Qed.
 
 
 (* This proof is obviously done by the definition of included *)
 Lemma In_a_l1_l2 : forall (A : Type) (l1 l2:list A) (a:A), In a l1 -> incl l1 l2 -> In a l2.
 Proof.
     intuition.
 Qed.
 
 (* if f is satisfied on l1 and l1 is included in l2 then f is satisfied on l2 *)
 Lemma existsb_a_l1_l2 : forall (A : Type) (f : A -> Prop) (l1 l2:list A), existsb _ f l1 -> incl l1 l2 -> existsb _ f l2.
 Proof.
     intuition.
     apply existsb_exists in H.
     destruct H.
     destruct H.
     apply existsb_exists.
     exists x.
     split; intuition.
 Qed.
 
(********************************
 
     DEFINING SUBSETS of
     ADVERSARY EVENTS and
     TIME-CONSTRAINED ADVERSARY EVENTS
 
 We say x is strictly less than y (x < y) if 
 * 1. x is an adversary event subset of y AND 
      x is a time-constrained adversary event proper subset of y
 * OR 
 * 2. x is a time-constrained adversary event subset of y AND 
      x is an adversary event proper subset of y
where 
    an adversary event is any event with an adversary label and
    a time-constrained adversary event is any adversary event that occurs between measurement events
 *)
 
 (****** ADVERSARY EVENTS SUBSET *)
 
 (* adversary events of x are a subset of adversary events in y *)
 Fixpoint adv_subset {G1 G2 : attackgraph measurement adversary} 
                 (x : list (G1.(event _ _) * G1.(event _ _))) (y : list (G2.(event _ _) * G2.(event _ _))) : Prop :=
   match x with 
   | nil => True
   | x :: xs => match (G1.(label _ _) (fst(x))) with 
                      | inr c => (existsb _ (fun step => match step with 
                                                        | (st2, _ ) => (G2.(label _ _) st2 = inr c) \/ (event_spo (G2.(label _ _) st2) (inr c))
                                                        end) y ) /\ adv_subset xs y              
                      | inl r => adv_subset xs y 
                      end
   end.
 
 (* Proper subset using the fixpoint definition *)
 Definition adv_proper_subset_fix {G1 G2 : attackgraph measurement adversary} 
 (x : list (G1.(event _ _) * G1.(event _ _))) (y : list (G2.(event _ _) * G2.(event _ _))) := adv_subset x y /\ ~ adv_subset y x. 
 
 (* Determine if an adversary event in G1 is present in y
  * input: one event in G1 (no need to recurse through G1) and list to search *)
 Definition find_adv {G1 G2 : attackgraph measurement adversary} (st : G1.(event _ _)) (y : list (G2.(event _ _) * G2.(event _ _))) : Prop := 
     match (G1.(label _ _) st) with 
     | inr c => existsb_ind _ (fun step => match step with 
                                     | (st2, _ ) => (G2.(label _ _) st2 = inr c) \/ (event_spo (G2.(label _ _) st2) (inr c))
                                     end) y                
     | inl r => True 
     end. 
 
 (* Inductively defined adversary subset *)
 Inductive adv_subset_ind {G1 G2 : attackgraph measurement adversary} : 
 list (G1.(event _ _) * G1.(event _ _)) -> (list (G2.(event _ _) * G2.(event _ _))) -> Prop :=
 | sub_nil : forall y, adv_subset_ind nil y
 | sub_head : forall x xs y, find_adv (fst x) y -> adv_subset_ind xs y -> adv_subset_ind (x::xs) y.
 
 
 (* If adversary event is in xs then it is in (x::xs) *)
 Lemma find_cons : forall G1 (x0: (G1.(event _ _) * G1.(event _ _))) x (xs : list (G1.(event _ _) * G1.(event _ _))), 
     find_adv (fst x0) (xs) -> find_adv (fst x0) (x :: xs).
 Proof.
     intros. unfold find_adv in *.
     destruct (G1.(label _ _) (fst x0)).
     + auto.
     + simpl in *. apply ex_tail. auto.
 Qed.
 
 (* Need this helper lemma to prove transitivity *)
 Lemma find_adv_helper : forall G1 G2 G3 (x: (G1.(event _ _) * G1.(event _ _)))
                          (ys:list (event measurement adversary G2 * event measurement adversary G2)), 
                          find_adv (fst x) (ys) -> forall (zs : list (G3.(event _ _) * G3.(event _ _))), adv_subset_ind ys zs -> find_adv (fst x) zs.
 Proof.
     intros G1 G2 G3 x ys H. intros. 
     unfold find_adv in *. destruct (G1.(label _ _) (fst x)).
     + auto.
     + induction H0 as [ | y ys zs].
     ++ inversion H.
     ++ inversion H; subst. 
     +++ unfold find_adv in H0. destruct (G2.(label _ _) (fst y)) eqn:contra; auto.
     ++++ destruct y. simpl in *. destruct H3.
     +++++ rewrite H2 in contra.
         inversion contra.
     +++++ rewrite contra in H2. simpl in H2. inversion H2.
     ++++ destruct y. simpl in *. destruct H3.
     +++++ rewrite H2 in contra. inversion contra. subst. auto.
     +++++ rewrite contra in H2. simpl in H2.  clear IHadv_subset_ind H1. induction H0; subst.
     ++++++ destruct a1. destruct H0.
     +++++++ eapply ex_head. rewrite H0. right. simpl. auto.
     +++++++ eapply ex_head. destruct (label measurement adversary G3 e1).
     ++++++++ simpl in H0. inversion H0.
     ++++++++ simpl in *. right. eapply adv_event_spo_trans; eauto.
     ++++++ eapply ex_tail. apply IHexistsb_ind.
     +++ apply IHadv_subset_ind. auto.
Qed. 

 

 Lemma adv_subset_ind_trans : forall G1 G2 (xs : list (G1.(event _ _) * G1.(event _ _))) (ys : list (G2.(event _ _) * G2.(event _ _))), 
 adv_subset_ind xs ys -> 
 forall G3 (zs : list (G3.(event _ _) * G3.(event _ _))), adv_subset_ind ys zs ->
 adv_subset_ind xs zs.
 Proof.
     intros G1 G2. intros xs ys Hxy. intros G3 zs Hyz.
     induction Hxy as [ | x xs ys ].
     + constructor.
     + constructor.
     ++ eapply find_adv_helper; eauto.
     ++ apply IHHxy. apply Hyz. 
 Qed. 
 
 (* Prove fixpoint definition is equal to inductive def *)
 Theorem adv_subset_eq : forall G1 G2 (xs: list (G1.(event _ _) * G1.(event _ _))) ( ys : list (G2.(event _ _) * G2.(event _ _))), adv_subset_ind xs ys <-> adv_subset xs ys.
 Proof.
     intros; split; intros.
     (* prove inductive implies fixpoint *)
     + induction H as [ | x xs ys ].
     ++ constructor.
     ++ simpl in *. unfold find_adv in H. destruct (G1.(label _ _) (fst x)).
     +++ eauto.
     +++ apply existsb_ind_impl_fix in H. auto.
     (* prove fixpoint implies inductive *)
     + induction xs.
     ++ constructor.
     ++ simpl in *. destruct (G1.(label _ _) (fst a)) as [ | a' ] eqn:Hlab.
     +++ econstructor. 
     ++++ unfold find_adv. rewrite Hlab. auto.
     ++++ simpl in *. auto.
     +++ constructor. 
     ++++ unfold find_adv. rewrite Hlab. inversion H.
         apply existsb_fix_impl_ind in H0.
          auto.
     ++++ inversion H. auto.
 Qed.
 
 (* Proper subset using the inductive definition *)
 Definition adv_proper_subset {G1 G2 : attackgraph measurement adversary} 
 (x : list (G1.(event _ _) * G1.(event _ _))) (y : list (G2.(event _ _) * G2.(event _ _))) := adv_subset_ind x y /\ ~ adv_subset_ind y x. 
 
 (*******************************************
 Prove the proper subset of adversary events is a strict partial order *)
 
 (* define strictly less for adversary events as a proper subset relation *) 
 (* Class strict_partial_order {X : Type} (R : X -> X -> Prop) := {
     irreflexive := forall a : X, ~ R a a ; 
     asymmetric := forall a b : X, R a b -> ~ R b a ;
     transitive := forall a b c: X, R a b -> R b c -> R a c 
     }. *)
     
 Theorem adv_irr : forall (g1 : attackgraph measurement adversary) (x : list (g1.(event _ _) * g1.(event _ _)) ), ~ adv_proper_subset x x.
     Proof.
     intros. unfold adv_proper_subset. unfold not. intros. inversion H. contradiction.
     Qed.
 
 Theorem adv_asym : forall (g1 g2 : attackgraph measurement adversary)  (x : list (g1.(event _ _) * g1.(event _ _)) ) (y : list (g2.(event _ _) * g2.(event _ _)) ), adv_proper_subset x y -> ~ adv_proper_subset y x.
     Proof.
     intros. unfold adv_proper_subset in *. inversion H. unfold not. intros. inversion H2. auto.
     Qed.
 
 Theorem adv_trans : forall (g1 g2 g3 : attackgraph measurement adversary) (xs : list (g1.(event _ _) * g1.(event _ _)) ) (ys : list (g2.(event _ _) * g2.(event _ _)) ), 
 adv_proper_subset xs ys -> 
 forall (zs : list (g3.(event _ _) * g3.(event _ _)) ), adv_proper_subset ys zs -> 
 adv_proper_subset xs zs.
     Proof.
     unfold adv_proper_subset in *. split.
     + intuition; eapply adv_subset_ind_trans; eauto.
     + unfold not. intros. intuition. apply H4. eapply adv_subset_ind_trans; eauto.
     Qed. 
 
 (****** TIME CONSTRAINED adversary EVENT SUBSET *)
 
 (* Adversary events of x are a subset of adversary events in y *)
 Fixpoint time_subset {G1 G2 : attackgraph measurement adversary} 
                 (x : list (G1.(event _ _) * G1.(event _ _))) (y : list (G2.(event _ _) * G2.(event _ _))) : Prop :=
     match x with 
     | nil => True
     | (st1, st2 ) :: xs => match G1.(label _ _) st1 , G1.(label _ _) st2 with 
                         | inl m , inr c => ( existsb _ (fun step => match step with 
                                                         | (st1', st2') => ((G2.(label _ _) st2' = inr c) \/ (event_spo (G2.(label _ _) st2') (inr c))) /\ G2.(label _ _) st1' = inl m
                                                         end) y ) /\ time_subset xs y               
                         | _ , _ => time_subset xs y 
                         end
     end.
 
 (* Determine if a time constrained adversary event in G1 is present in y
 * input: one step in G1 (no need to recurse through G1) and list to search (y) *)
 Definition find_time {G1 G2 : attackgraph measurement adversary} (st1 : G1.(event _ _) *  G1.(event _ _)) (y : list (G2.(event _ _) * G2.(event _ _))) : Prop := 
     match G1.(label _ _) (fst(st1)) , G1.(label _ _) (snd(st1))  with 
     | inl m , inr c => ( existsb_ind _ (fun step => match step with 
                                     | (st1', st2') => ((G2.(label _ _) st2' = inr c) \/ (event_spo (G2.(label _ _) st2') (inr c))) /\ G2.(label _ _) st1' = inl m
                                     end) y )                
     | _ , _ => True 
     end. 
 
 (* Inductively defined adversary subset *)
 Inductive time_subset_ind {G1 G2 : attackgraph measurement adversary} : 
 list (G1.(event _ _) * G1.(event _ _)) -> (list (G2.(event _ _) * G2.(event _ _))) -> Prop :=
 | time_nil : forall y, time_subset_ind nil y
 | time_head : forall x xs y, find_time x y -> time_subset_ind xs y -> time_subset_ind (x::xs) y.
 
 (* Prove fixpoint definition is equal to inductive def *)
 Theorem time_subset_eq : forall G1 G2 (xs: list (G1.(event _ _) * G1.(event _ _))) ( ys : list (G2.(event _ _) * G2.(event _ _))), time_subset_ind xs ys <-> time_subset xs ys.
 Proof.
     intros; split; intros.
     (* prove inductive implies fixpoint *)
     + induction H as [ | x xs ys ].
     ++ constructor.
     ++ simpl in *. destruct (G1.(label _ _) (fst x)) eqn:Hfst; eauto.
     +++ destruct (G1.(label _ _) (snd x)) eqn:Hsnd; eauto.
     ++++ destruct x. simpl in *. rewrite Hfst. rewrite Hsnd. auto.
     ++++ destruct x. simpl in *. rewrite Hfst. rewrite Hsnd. split.
     +++++ unfold find_time in H. simpl in *. rewrite Hfst in H. rewrite Hsnd in H.
           apply existsb_ind_impl_fix in H. auto.
     +++++ auto.
     +++ destruct x. simpl in *. rewrite Hfst. auto.
     (* prove fixpoint implies inductive *)
     + induction xs.
     ++ constructor.
     ++ constructor. 
     +++ unfold find_time. simpl in *. destruct (G1.(label _ _) (fst a)) eqn:Hfst; eauto.
         destruct (G1.(label _ _) (snd a)) eqn:Hsnd; destruct a; simpl in *; eauto.
         rewrite Hfst in H. rewrite Hsnd in H. inversion H. apply existsb_fix_impl_ind in H0. auto.
     +++ simpl in *. destruct (G1.(label _ _) (fst a)) eqn:Hfst; eauto.
     ++++ destruct (G1.(label _ _) (snd a)) eqn:Hsnd; destruct a.
     +++++ simpl in *; eauto. 
         rewrite Hfst in H. rewrite Hsnd in H.
         eauto.
     +++++ simpl in *; eauto. 
           rewrite Hfst in H. rewrite Hsnd in H. inversion H. eauto.
     ++++ destruct (G1.(label _ _) (snd a)) eqn:Hsnd; destruct a.
     +++++ simpl in *; eauto. 
         rewrite Hfst in H. eauto.
     +++++ simpl in *; eauto. 
           rewrite Hfst in H. eauto.
 Qed.
 
 Lemma find_time_helper : forall G1 G2 G3 (x: (G1.(event _ _) * G1.(event _ _)))
                          (ys:list (event measurement adversary G2 * event measurement adversary G2)), 
                          find_time x ys -> forall (zs : list (G3.(event _ _) * G3.(event _ _))), time_subset_ind ys zs -> find_time x zs.
 Proof.
     intros G1 G2 G3 x ys H. intros. 
     unfold find_time in *. destruct (G1.(label _ _) (fst x)); auto.
     destruct (G1.(label _ _) (snd x)); auto.
     induction H0 as [ | y ys zs].
     + inversion H.
     + inversion H; subst.
     ++ clear H. unfold find_time in H0. destruct (G2.(label _ _) (fst y)) eqn:Hfst; auto.
     (* fst y is a measurement event *)
     +++ destruct (G2.(label _ _) (snd y)) eqn:contra ; auto.
     (* snd y is a measurement  *)
     ++++ destruct y. simpl in *. inversion H3. destruct H3. destruct H3.
     +++++ rewrite H3 in contra.
         inversion contra.
     +++++ rewrite contra in H3. simpl in H3. inversion H3.
     ++++ destruct y. simpl in *. destruct H3. destruct H.
     +++++ rewrite H in contra. inversion contra. subst. rewrite H2 in Hfst.
            inversion Hfst. subst. auto.
     +++++ rewrite contra in H. clear IHtime_subset_ind H1. induction H0; subst.
     ++++++ destruct a1. destruct H0. destruct H0.
     +++++++ eapply ex_head. rewrite H0. split.
     ++++++++ right. simpl. auto.
     ++++++++ rewrite H1. rewrite <- H2. rewrite Hfst. auto.
     +++++++ eapply ex_head. destruct (label measurement adversary G3 e2).
     ++++++++ simpl in H0. inversion H0.
     ++++++++ simpl in *. split.
     +++++++++ right. eapply adv_event_spo_trans; eauto.
     +++++++++ rewrite H1. rewrite <- H2. rewrite Hfst. auto.
     ++++++ eapply ex_tail. apply IHexistsb_ind.
     (* fst y is a adversary event *)
     +++ destruct (G2.(label _ _) (snd y)) eqn:contra ; auto.
     ++++ destruct y. simpl in contra. destruct H3. destruct H.
     +++++ simpl in *. rewrite H in contra. inversion contra.
     +++++ rewrite contra in H. simpl in H. inversion H.
     ++++ destruct y. simpl in contra. destruct H3. destruct H.
     +++++ simpl in *. rewrite Hfst in H2. inversion H2.
     +++++ simpl in *. rewrite Hfst in H2. inversion H2. 
     ++ apply IHtime_subset_ind. auto. 
 Qed.
 
 Theorem time_subset_ind_trans : forall G1 G2 (xs : list (G1.(event _ _) * G1.(event _ _))) (ys : list (G2.(event _ _) * G2.(event _ _))), 
 time_subset_ind xs ys -> 
 forall G3 (zs : list (G3.(event _ _) * G3.(event _ _))), time_subset_ind ys zs ->
 time_subset_ind xs zs.
 Proof.
     intros G1 G2. intros xs ys Hxy. intros G3 zs Hyz.
     induction Hxy as [ | x xs ys ].
     + constructor.
     + constructor.
     ++ eapply find_time_helper; eauto.
     ++ apply IHHxy. apply Hyz. 
 Qed.
 
 (* Proper subset using the inductive definition *)
 Definition time_proper_subset {G1 G2 : attackgraph measurement adversary} 
 (x : list (G1.(event _ _) * G1.(event _ _))) (y : list (G2.(event _ _) * G2.(event _ _))) := time_subset_ind x y /\ ~ time_subset_ind y x.
 
 Theorem time_irr : forall (g1 : attackgraph measurement adversary) (x : list (g1.(event _ _) * g1.(event _ _)) ), ~ time_proper_subset x x.
 Proof.
     intros. unfold time_proper_subset. unfold not. intros. inversion H. contradiction.
 Qed.
 
 Theorem time_asym : forall (g1 g2 : attackgraph measurement adversary)  (x : list (g1.(event _ _) * g1.(event _ _)) ) (y : list (g2.(event _ _) * g2.(event _ _)) ), time_proper_subset x y -> ~ time_proper_subset y x.
 Proof.
     intros. unfold time_proper_subset in *. inversion H. unfold not. intros. inversion H2. auto.
 Qed.
 
 Theorem time_trans : forall (g1 g2 g3 : attackgraph measurement adversary) (xs : list (g1.(event _ _) * g1.(event _ _)) ) (ys : list (g2.(event _ _) * g2.(event _ _)) ), 
 time_proper_subset xs ys -> 
 forall (zs : list (g3.(event _ _) * g3.(event _ _)) ), time_proper_subset ys zs -> 
 time_proper_subset xs zs.
 Proof.
     unfold time_proper_subset in *. split.
     + intuition; eapply time_subset_ind_trans; eauto.
     + unfold not. intros. intuition. apply H4. eapply time_subset_ind_trans; eauto.
 Qed. 
 
(*******************************
  STRICT PARTIAL ORDER 
  ******************************)

 Definition strict_partial_order (g1 g2 : attackgraph measurement adversary) : Prop :=
    (adv_subset_ind (g1.(edges _ _)) (g2.(edges _ _)) /\ time_subset_ind (g1.(edges _ _)) (g2.(edges _ _))) /\ (adv_proper_subset (g1.(edges _ _)) (g2.(edges _ _)) \/ time_proper_subset (g1.(edges _ _)) (g2.(edges _ _))).
 
 Theorem spo_irr : forall (g1 : attackgraph measurement adversary), ~ strict_partial_order g1 g1.
 Proof.
     intros. unfold strict_partial_order. unfold not. intros. intuition.
     + unfold adv_proper_subset in H0; invc H0; intuition.
     + unfold time_proper_subset in H0; invc H0; intuition.
 Qed.
 
 Theorem spo_asym : forall (g1 g2 : attackgraph measurement adversary), strict_partial_order g1 g2 -> ~ strict_partial_order g2 g1.
 Proof.
     intros. unfold strict_partial_order in *. unfold not. intros. intuition.
     + unfold adv_proper_subset in H; invc H; intuition.
     + unfold time_proper_subset in H; invc H; intuition.
     + unfold adv_proper_subset in H; invc H; intuition.
     + unfold time_proper_subset in H; invc H; intuition.
 Qed.
 
 Ltac try_left := left; eapply adv_trans; eauto.
 Ltac try_right := right; eapply time_trans; eauto.
 
 Theorem spo_trans : forall (g1 g2 g3 : attackgraph measurement adversary), 
 strict_partial_order g1 g2 -> 
 forall g3, strict_partial_order g2 g3 -> 
 strict_partial_order g1 g3.
 Proof.
     intuition. unfold strict_partial_order in *; intuition;
     try (eapply adv_subset_ind_trans; eauto); try (eapply time_subset_ind_trans; eauto).
     + try_left.
     + left. unfold adv_proper_subset in *. split. 
     ++ eapply adv_subset_ind_trans; eauto.
     ++ intuition. apply H7. eapply adv_subset_ind_trans; eauto.
     + left. unfold adv_proper_subset in *. split. 
     ++ eapply adv_subset_ind_trans; eauto.
     ++ intuition. apply H7. eapply adv_subset_ind_trans; eauto.
     + try_right.
 Qed. 
 
 
 End Parameterized_Strict_Partial_Order.