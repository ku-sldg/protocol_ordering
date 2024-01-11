(**************************
    STRICTLY LESS THAN 

 Defining strict partial order
 to compare two attack graphs. 
 Here we define < and > . 

 By: Anna Fritz and Sarah Johnson
 Date: Sept 21, 2023
 **************************)

Require Import Coq.Lists.List.
Require Export Order.attack_graph.
Require Import Order.utilities.

 Section Strict_Partial_Order. 

 Context {measurement : Type}.
 Context {corruption : Type}.
 (* need two attack graphs for comparison now 
 Context {G : attackgraph measurement corruption}.
 Context {G2 : attackgraph measurement corruption}. *)
 
 (* Labels and States must have decidable equality *)
 Hypothesis eqDec_measurement : forall (x y : measurement), {x = y} + {x <> y}.
 Hypothesis eqDec_corruption : forall (x y : corruption), {x = y} + {x <> y}.
 Hypothesis eqDec_state : forall (G : attackgraph measurement corruption) (x y : G.(state _ _)), {x = y} + {x <> y}.
 
 Fixpoint existsb ( A : Type) (f : A -> Prop) (l:list A) : Prop := 
     match l with 
       | nil => False
       | a::l => f a \/ existsb A f l
     end.
 
 Inductive existsb_ind ( A : Type) (f : A -> Prop) : (list A) -> Prop :=
 | ex_head : forall a l, f a -> existsb_ind _ f (a::l)
 | ex_tail : forall a l, existsb_ind _ f l -> existsb_ind _ f (a::l).
 
 (********
   Facts about existsb *)
 
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
 
 (* cannot use In because of the types *)
 
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
 
     DEFINING SUBSETS 
 
 We say a is strictly less than b (a < b) if 
 * 1.a is an adversary event subset and a is a
     time-constrained adversary event proper subset
 * OR 
 * 2. a1 is a time-constrained adversary event subset and a1
      is an adversary event proper subset 
 *)
 
 (****** ADVERSARY EVENTS SUBSET *)
 
 (* corruption events of x are a subset of corruption events in y *)
 Fixpoint cor_subset {G1 G2 : attackgraph measurement corruption} 
                 (x : list (G1.(state _ _) * G1.(state _ _))) (y : list (G2.(state _ _) * G2.(state _ _))) : Prop :=
   match x with 
   | nil => True
   | x :: xs => match (G1.(label _ _) (fst(x))) with 
                      | inr c => (existsb _ (fun step => match step with 
                                                        | (st2, _ ) => G2.(label _ _) st2 = inr c
                                                        end) y ) /\ cor_subset xs y              
                      | inl r => cor_subset xs y 
                      end
   end.
 (* existsb _ (fun st2 => G2.(label _ _) st2 = inr c) (fst (split y)) *)
 
 (* Proper subset using the fixpoint definition *)
 Definition cor_proper_subset' {G1 G2 : attackgraph measurement corruption} 
 (x : list (G1.(state _ _) * G1.(state _ _))) (y : list (G2.(state _ _) * G2.(state _ _))) := cor_subset x y /\ ~ cor_subset y x. 
 
 (* determine if corruption event in G1 is present in y
  * input: one state in G1 (no need to recurse through G1) and list to search (y) *)
 Definition find_cor {G1 G2 : attackgraph measurement corruption} (st : G1.(state _ _)) (y : list (G2.(state _ _) * G2.(state _ _))) : Prop := 
     match (G1.(label _ _) st) with 
     | inr c => existsb_ind _ (fun step => match step with 
                                     | (st2, _ ) => G2.(label _ _) st2 = inr c
                                     end) y                
     | inl r => True 
     end. 
 
 (* Inductively defined corruption subset *)
 Inductive cor_subset_ind {G1 G2 : attackgraph measurement corruption} : 
 list (G1.(state _ _) * G1.(state _ _)) -> (list (G2.(state _ _) * G2.(state _ _))) -> Prop :=
 | sub_nil : forall y, cor_subset_ind nil y
 | sub_head : forall x xs y, find_cor (fst x) y -> cor_subset_ind xs y -> cor_subset_ind (x::xs) y.
 
 (* prove if x is nonempty then it cannot be a subset of nil *)
 Lemma subset_not_nil : forall G1 G2 a (x : list (G1.(state _ _) * G1.(state _ _))) (y : list (G2.(state _ _) * G2.(state _ _))), y = nil -> ~ cor_subset_ind (a::x) y.
 Proof. 
 (* proof won't work bc (a::x) could be list of measurement events *)
 Abort.
 
 (* If corruption event is in xs then it is in (x::xs) *)
 Lemma find_cons : forall G1 (x0: (G1.(state _ _) * G1.(state _ _))) x (xs : list (G1.(state _ _) * G1.(state _ _))), 
     find_cor (fst x0) (xs) -> find_cor (fst x0) (x :: xs).
 Proof.
     intros. unfold find_cor in *.
     destruct (G1.(label _ _) (fst x0)).
     + auto.
     + simpl in *. apply ex_tail. auto.
 Qed.
 
 (* Need this helper lemma to prove transitivity *)
 Lemma find_cor_helper : forall G1 G2 G3 (x: (G1.(state _ _) * G1.(state _ _)))
                          (ys:list (state measurement corruption G2 * state measurement corruption G2)), 
                          find_cor (fst x) (ys) -> forall (zs : list (G3.(state _ _) * G3.(state _ _))), cor_subset_ind ys zs -> find_cor (fst x) zs.
 Proof.
     intros G1 G2 G3 x ys H. intros. 
     unfold find_cor in *. destruct (G1.(label _ _) (fst x)).
     + auto.
     + induction H0 as [ | y ys zs].
     ++ inversion H.
     ++ inversion H; subst. 
     +++ unfold find_cor in H0. destruct (G2.(label _ _) (fst y)) eqn:contra; auto.
     ++++ destruct y. simpl in *. 
         rewrite H3 in contra.
         inversion contra.
     ++++ destruct y. simpl in *. 
     rewrite H3 in contra. inversion contra. subst. auto.
     +++ apply IHcor_subset_ind. auto. 
 Qed.  
 
Lemma cor_subset_ind_asym : forall G1 G2 (xs : list (G1.(state _ _) * G1.(state _ _))) (ys : list (G2.(state _ _) * G2.(state _ _))), cor_subset_ind xs ys -> ~ cor_subset_ind ys xs. 
Proof.
    intros. unfold not. intros. induction ys. destruct xs.
Abort. 

 Lemma cor_subset_ind_trans : forall G1 G2 (xs : list (G1.(state _ _) * G1.(state _ _))) (ys : list (G2.(state _ _) * G2.(state _ _))), 
 cor_subset_ind xs ys -> 
 forall G3 (zs : list (G3.(state _ _) * G3.(state _ _))), cor_subset_ind ys zs ->
 cor_subset_ind xs zs.
 Proof.
     intros G1 G2. intros xs ys Hxy. intros G3 zs Hyz.
     induction Hxy as [ | x xs ys ].
     + constructor.
     + constructor.
     ++ eapply find_cor_helper; eauto.
     ++ apply IHHxy. apply Hyz. 
 Qed. 
 
 (* Prove fixpoint definition is equal to inductive def *)
 Theorem cor_subset_eq : forall G1 G2 (xs: list (G1.(state _ _) * G1.(state _ _))) ( ys : list (G2.(state _ _) * G2.(state _ _))), cor_subset_ind xs ys <-> cor_subset xs ys.
 Proof.
     intros; split; intros.
     (* prove inductive implies fixpoint *)
     + induction H as [ | x xs ys ].
     ++ constructor.
     ++ simpl in *. unfold find_cor in H. destruct (G1.(label _ _) (fst x)).
     +++ eauto.
     +++ apply existsb_ind_impl_fix in H. auto.
     (* prove fixpoint implies inductive *)
     + induction xs.
     ++ constructor.
     ++ simpl in *. destruct (G1.(label _ _) (fst a)) as [ | a' ] eqn:Hlab.
     +++ econstructor. 
     ++++ unfold find_cor. rewrite Hlab. auto.
     ++++ simpl in *. auto.
     +++ constructor. 
     ++++ unfold find_cor. rewrite Hlab. inversion H.
         apply existsb_fix_impl_ind in H0.
          auto.
     ++++ inversion H. auto.
 Qed.
 
 (* Proper subset using the inductive definition *)
 Definition cor_proper_subset {G1 G2 : attackgraph measurement corruption} 
 (x : list (G1.(state _ _) * G1.(state _ _))) (y : list (G2.(state _ _) * G2.(state _ _))) := cor_subset_ind x y /\ ~ cor_subset_ind y x. 
 
 (*******************************************
 Prove the proper subset of corruption events is a strict partial order *)
 
 (* define strictly less for corruption events as a proper subset relation *) 
 (* Class strict_partial_order {X : Type} (R : X -> X -> Prop) := {
     irreflexive := forall a : X, ~ R a a ; 
     asymmetric := forall a b : X, R a b -> ~ R b a ;
     transitive := forall a b c: X, R a b -> R b c -> R a c 
     }. *)
     
 Theorem cor_irr : forall (g1 : attackgraph measurement corruption) (x : list (g1.(state _ _) * g1.(state _ _)) ), ~ cor_proper_subset x x.
     Proof.
     intros. unfold cor_proper_subset. unfold not. intros. inversion H. contradiction.
     Qed.
 
 Theorem cor_asym : forall (g1 g2 : attackgraph measurement corruption)  (x : list (g1.(state _ _) * g1.(state _ _)) ) (y : list (g2.(state _ _) * g2.(state _ _)) ), cor_proper_subset x y -> ~ cor_proper_subset y x.
     Proof.
     intros. unfold cor_proper_subset in *. inversion H. unfold not. intros. inversion H2. auto.
     Qed.
 
 Theorem cor_trans : forall (g1 g2 g3 : attackgraph measurement corruption) (xs : list (g1.(state _ _) * g1.(state _ _)) ) (ys : list (g2.(state _ _) * g2.(state _ _)) ), 
 cor_proper_subset xs ys -> 
 forall (zs : list (g3.(state _ _) * g3.(state _ _)) ), cor_proper_subset ys zs -> 
 cor_proper_subset xs zs.
     Proof.
     unfold cor_proper_subset in *. split.
     + intuition; eapply cor_subset_ind_trans; eauto.
     + unfold not. intros. intuition. apply H4. eapply cor_subset_ind_trans; eauto.
     Qed. 
 
 (****** TIME CONSTRAINED CORRUPTION EVENT SUBSET *)
 
 (* corruption events of x are a subset of corruption events in y *)
 Fixpoint time_subset {G1 G2 : attackgraph measurement corruption} 
                 (x : list (G1.(state _ _) * G1.(state _ _))) (y : list (G2.(state _ _) * G2.(state _ _))) : Prop :=
     match x with 
     | nil => True
     | (st1, st2 ) :: xs => match G1.(label _ _) st1 , G1.(label _ _) st2 with 
                         | inl m , inr c => ( existsb _ (fun step => match step with 
                                                         | (st1', st2') => G2.(label _ _) st2' = inr c /\ G2.(label _ _) st1' = inl m
                                                         end) y ) /\ time_subset xs y               
                         | _ , _ => time_subset xs y 
                         end
     end.
 
 (* determine if a time constrained corruption event in G1 is present in y
 * input: one step in G1 (no need to recurse through G1) and list to search (y) *)
 Definition find_time {G1 G2 : attackgraph measurement corruption} (st1 : G1.(state _ _) *  G1.(state _ _)) (y : list (G2.(state _ _) * G2.(state _ _))) : Prop := 
     match G1.(label _ _) (fst(st1)) , G1.(label _ _) (snd(st1))  with 
     | inl m , inr c => ( existsb_ind _ (fun step => match step with 
                                     | (st1', st2') => G2.(label _ _) st2' = inr c /\ G2.(label _ _) st1' = inl m
                                     end) y )                
     | _ , _ => True 
     end. 
 
 (* Inductively defined corruption subset *)
 Inductive time_subset_ind {G1 G2 : attackgraph measurement corruption} : 
 list (G1.(state _ _) * G1.(state _ _)) -> (list (G2.(state _ _) * G2.(state _ _))) -> Prop :=
 | time_nil : forall y, time_subset_ind nil y
 | time_head : forall x xs y, find_time x y -> time_subset_ind xs y -> time_subset_ind (x::xs) y.
 
 (* Prove fixpoint definition is equal to inductive def *)
 Theorem time_subset_eq : forall G1 G2 (xs: list (G1.(state _ _) * G1.(state _ _))) ( ys : list (G2.(state _ _) * G2.(state _ _))), time_subset_ind xs ys <-> time_subset xs ys.
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
 
 Lemma find_time_helper : forall G1 G2 G3 (x: (G1.(state _ _) * G1.(state _ _)))
                          (ys:list (state measurement corruption G2 * state measurement corruption G2)), 
                          find_time x ys -> forall (zs : list (G3.(state _ _) * G3.(state _ _))), time_subset_ind ys zs -> find_time x zs.
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
     ++++ destruct y. simpl in *. inversion H3. 
         rewrite H in contra.
         inversion contra.
     ++++ destruct y. simpl in *.
          inversion H3. rewrite H in contra. inversion contra.
          rewrite H2 in Hfst. inversion Hfst. subst. auto.
     (* fst y is a corruption event *)
     +++ destruct (G2.(label _ _) (snd y)) eqn:contra ; auto.
     ++++ destruct y. intuition. simpl in *. rewrite Hfst in H2. inversion H2.
     ++++ destruct y. intuition. simpl in *. rewrite Hfst in H2. inversion H2. 
     ++ apply IHtime_subset_ind. auto. 
 Qed.
 
 Theorem time_subset_ind_trans : forall G1 G2 (xs : list (G1.(state _ _) * G1.(state _ _))) (ys : list (G2.(state _ _) * G2.(state _ _))), 
 time_subset_ind xs ys -> 
 forall G3 (zs : list (G3.(state _ _) * G3.(state _ _))), time_subset_ind ys zs ->
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
 Definition time_proper_subset {G1 G2 : attackgraph measurement corruption} 
 (x : list (G1.(state _ _) * G1.(state _ _))) (y : list (G2.(state _ _) * G2.(state _ _))) := time_subset_ind x y /\ ~ time_subset_ind y x.
 
 Theorem time_irr : forall (g1 : attackgraph measurement corruption) (x : list (g1.(state _ _) * g1.(state _ _)) ), ~ time_proper_subset x x.
 Proof.
     intros. unfold time_proper_subset. unfold not. intros. inversion H. contradiction.
 Qed.
 
 Theorem time_asym : forall (g1 g2 : attackgraph measurement corruption)  (x : list (g1.(state _ _) * g1.(state _ _)) ) (y : list (g2.(state _ _) * g2.(state _ _)) ), time_proper_subset x y -> ~ time_proper_subset y x.
 Proof.
     intros. unfold time_proper_subset in *. inversion H. unfold not. intros. inversion H2. auto.
 Qed.
 
 Theorem time_trans : forall (g1 g2 g3 : attackgraph measurement corruption) (xs : list (g1.(state _ _) * g1.(state _ _)) ) (ys : list (g2.(state _ _) * g2.(state _ _)) ), 
 time_proper_subset xs ys -> 
 forall (zs : list (g3.(state _ _) * g3.(state _ _)) ), time_proper_subset ys zs -> 
 time_proper_subset xs zs.
 Proof.
     unfold time_proper_subset in *. split.
     + intuition; eapply time_subset_ind_trans; eauto.
     + unfold not. intros. intuition. apply H4. eapply time_subset_ind_trans; eauto.
 Qed. 
 
(*******************************
  STRICT PARTIAL ORDER 
  ******************************)

 Definition strict_partial_order (g1 g2 : attackgraph measurement corruption) : Prop :=
    (cor_subset_ind (g1.(steps _ _)) (g2.(steps _ _)) /\ time_subset_ind (g1.(steps _ _)) (g2.(steps _ _))) /\ (cor_proper_subset (g1.(steps _ _)) (g2.(steps _ _)) \/ time_proper_subset (g1.(steps _ _)) (g2.(steps _ _))).
 
 Theorem spo_irr : forall (g1 : attackgraph measurement corruption), ~ strict_partial_order g1 g1.
 Proof.
     intros. unfold strict_partial_order. unfold not. intros. intuition.
     + unfold cor_proper_subset in H0; invc H0; intuition.
     + unfold time_proper_subset in H0; invc H0; intuition.
 Qed.
 
 Theorem spo_asym : forall (g1 g2 : attackgraph measurement corruption), strict_partial_order g1 g2 -> ~ strict_partial_order g2 g1.
 Proof.
     intros. unfold strict_partial_order in *. unfold not. intros. intuition.
     + unfold cor_proper_subset in H; invc H; intuition.
     + unfold time_proper_subset in H; invc H; intuition.
     + unfold cor_proper_subset in H; invc H; intuition.
     + unfold time_proper_subset in H; invc H; intuition.
 Qed.
 
 Ltac try_left := left; eapply cor_trans; eauto.
 Ltac try_right := right; eapply time_trans; eauto.
 
 Theorem spo_trans : forall (g1 g2 g3 : attackgraph measurement corruption), 
 strict_partial_order g1 g2 -> 
 forall g3, strict_partial_order g2 g3 -> 
 strict_partial_order g1 g3.
 Proof.
     intuition. unfold strict_partial_order in *; intuition;
     try (eapply cor_subset_ind_trans; eauto); try (eapply time_subset_ind_trans; eauto).
     + try_left.
     + left. unfold cor_proper_subset in *. split. 
     ++ eapply cor_subset_ind_trans; eauto.
     ++ intuition. apply H7. eapply cor_subset_ind_trans; eauto.
     + left. unfold cor_proper_subset in *. split. 
     ++ eapply cor_subset_ind_trans; eauto.
     ++ intuition. apply H7. eapply cor_subset_ind_trans; eauto.
     + try_right.
 Qed. 
 
 (* We have proved the strict partial order is in fact a strict partial order *)
 
 End Strict_Partial_Order.