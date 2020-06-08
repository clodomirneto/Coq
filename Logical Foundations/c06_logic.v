(** Capítulo 6 - (** * Logic in Coq  (Logic) *) *)

Set Warnings "-notation-overridden,-parsing".

From LF Require Export c05_tactics.

Theorem plus_2_2_is_4 : 2 + 2 = 4.
Proof.
  simpl.
  reflexivity.
Qed.

Definition plus_fact : Prop := 2 + 2 = 4.

Theorem plus_fact_is_true : plus_fact.
Proof.
  reflexivity.
Qed.

Definition injective {A B} (f : A -> B) := forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H.
  injection H as H1.
  apply H1.
Qed.

(** Logical Connectives *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB.
  split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** Exercise: 2 stars (and_exercise)  *)
Example and_exercise : forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros [] [].
  - apply and_intro. reflexivity.
  - apply and_intro. reflexivity.
  - split.
    + inversion H.
    + inversion H.
  - split.
    + inversion H.
    + inversion H.
Qed.

Lemma and_example2 : forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite -> Hn.
  rewrite -> Hm.
  simpl.
  reflexivity.
Qed.

Lemma and_example2' : forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite -> Hn.
  rewrite -> Hm.
  simpl.
  reflexivity.
Qed.

Lemma and_example2'' : forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite -> Hn.
  rewrite -> Hm.
  simpl.
  reflexivity.
Qed.

Lemma and_example3 : forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite -> Hn.
  simpl.
  reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop, P /\ Q -> P.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  apply HP.
Qed.

(** Exercise: 1 star, optional (proj2)  *)
Lemma proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.

(** Exercise: 2 stars (and_assoc)  *)
Theorem and_assoc : forall P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  destruct H as [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

Lemma or_example : forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m H.
  destruct H as [Hn | Hm].
  - rewrite -> Hn. simpl. reflexivity.
  - rewrite Hm. rewrite <- mult_n_O. reflexivity.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma or_intro' : forall A B : Prop, B -> A \/ B.
Proof.
  intros A B HB.
  right.
  apply HB.
Qed.

Lemma zero_or_succ : forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. simpl. reflexivity.
Qed.

(** Exercise: 1 star (mult_eq_0)  *)
Lemma mult_eq_0 : forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  destruct n as [|n'].
  - left. reflexivity.
  - right. destruct m as [|m'].
    + reflexivity.
    + inversion H.
Qed.

(** Exercise: 1 star (or_commut)  *)
Theorem or_commut : forall P Q : Prop, P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H.
  - right. apply H0.
  - left. apply H0.
Qed.

Theorem ex_falso_quodlibet : forall (P : Prop), False -> P.
Proof.
  intros P H.
  inversion H.
Qed.

(** Exercise: 2 stars, optional (not_implies_our_not)  *)
Fact not_implies_our_not : forall (P : Prop), ~ P -> (forall (Q : Prop), P -> Q).
Proof.
  intros P H Q HP.
  unfold not in H.
  destruct H.
  apply HP.
Qed.

Notation "x <> y" := (~(x = y)).

Theorem zero_not_one : ~(0 = 1).
Proof.
  unfold not.
  intros contra.
  inversion contra.
Qed.

Theorem zero_not_one' : 0 <> 1.
Proof.
  unfold not.
  intros contra.
  inversion contra.
Qed.

Theorem not_False : ~ False.
Proof.
  unfold not.
  intros H.
  apply H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop, (P /\ ~P) -> Q.
Proof.
  intros P Q H.
  destruct H as [HP HNP].
  unfold not in HNP.
  apply HNP in HP.
  destruct HP.
Qed.

Theorem double_neg : forall P : Prop, P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros PF.
  apply PF.
  apply H.
Qed.

(** Exercise: 2 stars, recommended (contrapositive)  *)
Theorem contrapositive : forall (P Q : Prop), (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ.
  unfold not.
  intros HQF.
  intros HP.
  apply HQF.
  apply HPQ.
  apply HP.
Qed.

Theorem contrapositive' : forall (P Q : Prop), (P -> Q) -> (~Q -> ~P).
Proof.
  unfold not.
  intros P Q H H0 H1.
  apply H0 in H.
  destruct H.
  apply H1.
Qed.

(** Exercise: 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop, ~ (P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros HPPF.
  destruct HPPF.
  apply H0.
  apply H.
Qed.

(** Exercise: 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false' : forall P : Prop, ~ (P /\ ~P).
Proof.
  unfold not.
  intros P [HP HNP].
  destruct HNP.
  apply HP.
Qed.

Theorem not_true_is_false : forall b : bool, b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H. apply ex_falso_quodlibet. apply H. reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H. exfalso. apply H. reflexivity.
  - reflexivity.
Qed.

Lemma True_is_true : True.
Proof.
  apply I.
Qed.

Notation "P <-> Q" := (iff P Q) (at level 95, no associativity) : type_scope.

Theorem iff_sym : forall P Q : Prop, (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HPQ HQP].
  split.
  - apply HQP.
  - apply HPQ.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b.
  split.
  - apply not_true_is_false.
  - intros H. rewrite -> H. intros H'. inversion H'.
Qed.

(** Exercise: 1 star, optional (iff_properties)  *)
Theorem iff_refl : forall P : Prop, P <-> P.
Proof.
  intro P.
  split.
  - intro H. apply H.
  - intro H. apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop, (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R [HPQ HQP] [HQR HRQ].
  split.
  - intro HP. apply HQR. apply HPQ. apply HP.
  - intro HR. apply HQP. apply HRQ. apply HR.
Qed.

(** Exercise: 3 stars (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop, P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [H1 | [H2 H3]].
    + apply and_intro.
      * left. apply H1.
      * left. apply H1.
    + apply and_intro.
      * right. apply H2.
      * right. apply H3.
  - intros [[H1 | H2] [H3 | H4]].
    + left. apply H1.
    + left. apply H1.
    + left. apply H3.
    + right. apply and_intro.
      * apply H2.
      * apply H4.
Qed.

Require Import Coq.Setoids.Setoid.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc : forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 : forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite -> mult_0.
  rewrite -> mult_0.
  rewrite -> or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example : forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  apply mult_0.
  apply H.
Qed.

Lemma four_is_even : exists n : nat, eq 4 (n + n).
Proof.
  exists 2.
  simpl.
  reflexivity.
Qed.

Theorem exists_example_2 : forall n, (exists m, eq n (4 + m)) -> (exists o, eq n (2 + o)).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

(** Exercise: 1 star, recommended (dist_not_exists)  *)
Theorem dist_not_exists : forall (X : Type) (P : X -> Prop), (forall x, P x) -> not (exists x, not (P x)).
Proof.
  intros X P H.
  unfold not.
  intros [x E].
  destruct E.
  apply H.
Qed.

(** Exercise: 2 stars (dist_exists_or)  *)
Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop), (exists x, or (P x) (Q x)) <-> or (exists x, P x) (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [x [PE | QE]].
    + left. exists x. apply PE.
    + right. exists x. apply QE.
  - intros [[x HPx] | [x HQx]].
    + exists x. left. apply HPx.
    + exists x. right. apply HQx.
Qed.

(** Programming with Propositions *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl.
  right.
  right.
  right.
  left.
  reflexivity.
Qed.

Example In_example_2 : forall n, In n [2; 4] -> exists n', eq n (2 * n').
Proof.
  simpl.
  intros n [H1 | [H2 | []]].
  - exists 1. rewrite <- H1. simpl. reflexivity.
  - exists 2. rewrite <- H2. simpl. reflexivity.
Qed.

Lemma In_map : forall (A B : Type) (f : A -> B) (l : list A) (x : A), In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - simpl. intros [].
  - simpl. intros [H | H].
    + rewrite -> H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(** Exercise: 2 stars (In_map_iff)  *)

Lemma In_map_iff : forall (A B : Type) (f : A -> B) (l : list A) (y : B), In y (map f l) <-> exists x, (and (eq (f x) y) (In x l)).
Proof.
  intros A B f l y.
  split.
  - intro H.
    induction l as [|n l' IHl].
    + inversion H.
    + simpl in H.
      destruct H as [Hfy | Hiyl].
      * exists n. apply and_intro.
        { apply Hfy. }
        { simpl. left. reflexivity. }
      * apply IHl in Hiyl.
        destruct Hiyl as [x [Hfy Hiyl]].
        {
          exists x. apply and_intro.
          - apply Hfy.
          - simpl. right. apply Hiyl.
        }
  - intros [x [Hfy Hiyl]]. rewrite <- Hfy. apply In_map. apply Hiyl.
Qed.

(** **** Exercise: 2 stars (In_app_iff)  *)
Lemma In_app_iff : forall A l1 l2 (a:A), In a (l1 ++ l2) <-> In a l1 \/ In a l2.
Proof.
  intros A l1 l2 a.
  split.
  - intro H.
    induction l1 as [|n l1' IHl1].
    + simpl in H. right. apply H.
    + simpl in H.
      destruct H as [H1 | H2].
      * left. simpl. left. apply H1.
      * apply IHl1 in H2. simpl. apply or_assoc. right. apply H2.
  - intro H.
    induction l1 as [|n l1' IHl1].
    + simpl. destruct H.
      * inversion H.
      * apply H.
    + simpl in H.
      apply or_assoc in H. destruct H as [H1 | H2].
      * simpl. left. apply H1.
      * apply IHl1 in H2. simpl. right. apply H2.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | nil => True
  | h :: t => P h /\ All P t
  end.

Lemma All_In : forall T (P : T -> Prop) (l : list T), (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l.
  split.
  - intros H.
    induction l as [|n l' IHl].
    + reflexivity.
    + simpl. split.
      * apply H. simpl. left. reflexivity.
      * apply IHl. intros x H1. apply H. simpl. right. apply H1.
  - intros H. induction l as [|n l' IHl].
    + intros x H0. inversion H0.
    + simpl. intros x H0. destruct H0.
      * simpl in H. apply proj1 in H. rewrite <- H0. apply H.
      * simpl in H. apply proj2 in H. apply IHl with x in H.
        { apply H. }
        { apply H0. }
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) (n : nat) : Prop := if (oddb n) then Podd n else Peven n.

Theorem combine_odd_even_intro : forall (Podd Peven : nat -> Prop) (n : nat), (oddb n = true -> Podd n) -> (oddb n = false -> Peven n) -> combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H H0.
  unfold combine_odd_even.
  destruct (oddb n).
  - apply H. reflexivity.
  - apply H0. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd : forall (Podd Peven : nat -> Prop) (n : nat), combine_odd_even Podd Peven n -> oddb n = true -> Podd n.
Proof.
  intros Podd Peven n H H0.
  unfold combine_odd_even in H.
  rewrite H0 in H. apply H.
Qed.

Theorem combine_odd_even_elim_even : forall (Podd Peven : nat -> Prop) (n : nat), combine_odd_even Podd Peven n -> oddb n = false -> Peven n.
Proof.
  intros Podd Peven n H H0.
  unfold combine_odd_even in H.
  rewrite H0 in H.
  apply H.
Qed.

(** Applying Theorems to Arguments *)

Lemma plus_comm3_take2 : forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite -> plus_comm.
  assert (H : y + z = z + y).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Lemma plus_comm3_take3 : forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite -> plus_comm.
  rewrite -> (plus_comm y z).
  reflexivity.
Qed.

Lemma in_not_nil : forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl. destruct l.
  - simpl in H. destruct H.
  - discriminate Hl.
Qed.

Lemma in_not_nil_42_take2 : forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

Lemma in_not_nil_42_take3 : forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

Lemma in_not_nil_42_take4 : forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Lemma in_not_nil_42_take5 : forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Example lemma_application_ex : forall {n : nat} {ns : list nat}, In n (map (fun m => m * 0) ns) -> n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H) as [m [Hm _]].
  rewrite -> mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(** Coq vs. Set Theory *)

Example function_equality_ex1 : plus 3 = plus (pred 4).
Proof.
  simpl.
  reflexivity.
Qed.

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y}, (forall (x : X), f x = g x) -> f = g.

Example function_equality_ex2 : (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros x.
  apply plus_comm.
Qed.

(** Exercise: 4 stars (tr_rev_correct)  *)
Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X := rev_append l [].

Lemma rev_append_l1_l2_eq_app_rev_l1_l2: forall X (l1 l2 : list X), rev_append l1 l2 = rev l1 ++ l2.
Proof.
  intros X l1.
  induction l1 as [|n l1' IHl1].
  - reflexivity.
  - intro l2. simpl. rewrite -> IHl1. rewrite <- app_assoc. reflexivity.
Qed.

Lemma tr_rev_correct: forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  intro l.
  unfold tr_rev.
  destruct l as [|n l'].
  - reflexivity.
  - simpl. apply rev_append_l1_l2_eq_app_rev_l1_l2.
Qed.

Example even_42_bool : evenb 42 = true.
Proof.
  reflexivity.
Qed.

Example even_42_prop : exists k, eq 42 (double k).
Proof.
  exists 21.
  simpl.
  reflexivity.
Qed.

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k.
  induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** Exercise: 3 stars (evenb_double_conv)  *)
Theorem evenb_double_conv : forall n, exists k, eq n (if evenb n then double k else S (double k)).
Proof.
  induction n as [|n' IHn].
  - exists O. simpl. reflexivity.
  - destruct (evenb n') eqn:H1 in IHn.
    + rewrite -> (evenb_S n'). rewrite -> H1. simpl. inversion IHn. exists x. apply f_equal. apply H.
    + rewrite -> (evenb_S n'). rewrite -> H1. simpl. inversion IHn. exists (S x). simpl. apply f_equal. apply H.
Qed.

Theorem even_bool_prop : forall n, eq (evenb n) true <-> exists k, eq n (double k).
Proof.
  intros n.
  split.
  - intros H. destruct (evenb_double_conv n) as [k Hk]. rewrite -> Hk. rewrite -> H. exists k. reflexivity.
  - intros [k Hk]. rewrite -> Hk. apply evenb_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat, eqb n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite -> H. rewrite <- eqb_refl. reflexivity.
Qed.

Example even_1000 : exists k, eq 1000 (double k).
Proof.
  exists 500.
  simpl.
  reflexivity.
Qed.

Example even_1000' : evenb 1000 = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example even_1000'' : exists k, eq 1000 (double k).
Proof.
  apply even_bool_prop.
  simpl.
  reflexivity.
Qed.

Example not_even_1001 : evenb 1001 = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example not_even_1001' : ~(exists k, eq 1001 (double k)).
Proof.
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

Lemma plus_eqb_example : forall n m p : nat, eq (eqb n m) true -> eq (eqb (n + p) (m + p)) true.
Proof.
  intros n m p H.
  rewrite -> eqb_eq in H.
  rewrite -> H.
  rewrite -> eqb_eq.
  reflexivity.
Qed.

(** Exercise: 2 stars (logical_connectives)  *)
Lemma andb_true_iff : forall b1 b2 : bool, andb b1 b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2.
  split.
  - intro H. 
    apply and_intro.
    + rewrite andb_commutative in H. apply andb_true_elim2 in H. apply H.
    + apply andb_true_elim2 in H. apply H.
  - intro H. inversion H. rewrite -> H0. rewrite -> H1. reflexivity.
Qed.

Lemma orb_true_iff : forall b1 b2 : bool, orb b1 b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2.
  split.
  - intro H.
    destruct b1.
    + left. reflexivity.
    + destruct b2.
      * right. reflexivity.
      * inversion H.
  - destruct b1.
    + destruct b2.
      * intro H. reflexivity.
      * intro H. reflexivity.
    + destruct b2.
      * intro H. reflexivity.
      * intro H. exfalso. inversion H.
      { inversion H0. } { inversion H0. }
Qed.

(** Exercise: 1 star, standard (eqb_neq) *)
Theorem eqb_neq : forall x y : nat, eqb x y = false <-> x <> y.
Proof.
  intros x y.
  unfold not.
  split.
  - intros H1 H2. apply eqb_eq in H2. rewrite H2 in H1. inversion H1.
  - intro H. induction x as [|x' IHn].
    + destruct y as [|y'].
      * simpl. exfalso. apply H. reflexivity.
      * reflexivity.
    + destruct y as [|y'].
      * reflexivity.
      * simpl. destruct (eqb x' y') eqn:H1.
        { exfalso. apply H. apply f_equal. apply eqb_eq. apply H1. }
        { reflexivity. }
Qed.

(** Exercise: 3 stars, standard (eqb_list) *)
Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool := 
  match l1, l2 with
  | [], [] => true
  | [], _ | _, [] => false
  | h1 :: t1, h2 :: t2 => if eqb h1 h2 then eqb_list eqb t1 t2 else false
  end.

Lemma eqb_list_true_iff : forall A (eqb : A -> A -> bool),   (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) -> forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb H l1 l2.
  split.
  - generalize dependent l2.
    induction l1 as [|n l1' IHl].
    + destruct l2 as [|m l2'].
      * reflexivity.
      * intro H1. inversion H1.
    + intros l2. induction l2 as [|m l2' IHl2].
      * intro H1. inversion H1.
      * simpl. intro H1. destruct (eqb n m) eqn:He1. apply H in He1. rewrite <- He1. assert (H2 : (l1' = l2' -> (n :: l1' = n :: l2'))).  { intro Hh. rewrite Hh. reflexivity. }
        apply H2. apply IHl. { apply H1. } { inversion H1. }
  - intro H1.
    generalize dependent l2.
    induction l1 as [|n l1' IHl].
    + intros l2 H1. rewrite <- H1. reflexivity.
    + intros l2 H1.
      destruct l2 as [|m l2'].
      * inversion H1.
      * symmetry in H1. inversion H1. simpl. apply H in H2. inversion H1. rewrite -> H4 in H2. rewrite -> H2. apply IHl.  reflexivity.
Qed.

(** Exercise: 2 stars, recommended (All_forallb)  *)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

Theorem forallb_true_iff : forall X test (l : list X), forallb test l = true <-> All (fun x => eq (test x) true) l.
Proof.
  intros X test l.
  split.
  - induction l as [|n l' IHl].
    + reflexivity.
    + simpl. intro H. split.
      * rewrite <- andb_commutative in H. apply andb_true_elim2 in H. apply H.
      * apply IHl. apply andb_true_elim2 in H. apply H.
  - induction l as [|n l' IHl].
    + reflexivity.
    + simpl. intros [H1 H2]. rewrite -> H1. apply IHl in H2. rewrite -> H2. reflexivity.
Qed.

Definition excluded_middle := forall P : Prop, P \/ ~ P.

Theorem restricted_excluded_middle : forall P b, (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat), n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (eqb n m)).
  symmetry.
  apply eqb_eq.
Qed.

(** Exercise: 3 stars (excluded_middle_irrefutable)  *)
Theorem excluded_middle_irrefutable: forall (P:Prop), ~ ~ (P \/ ~ P).
Proof.
  intros P H.
  apply H.
  right.
  unfold not.
  intro HP.
  apply H.
  left.
  apply HP.
Qed.

(** Exercise: 3 stars, advanced (not_exists_dist)  *)
Theorem not_exists_dist : excluded_middle -> forall (X:Type) (P : X -> Prop), not (exists x, not (P x)) -> (forall x, P x).
Proof.
  intros E X P.
  unfold not.
  intro H.
  intro x.
  destruct E with (P x).
  apply H0.
  unfold not in H0.
  exfalso.
  apply H.
  exists x.
  apply H0.
Qed.

(** Exercise: 5 stars, optional (classical_axioms)  *)
Definition peirce := forall P Q: Prop, ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop, ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop, ~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop, (P->Q) -> (~P\/Q).

Theorem peirce_valid : excluded_middle <-> peirce.
Proof.
  split.
  - intros E P Q.
    intro H.
    destruct (E P) as [H'|H'].
    + apply H'.
    + apply H. intro HP. exfalso. apply H'. apply HP.
  - intros E H. apply (E (or H (~H)) False). intro H1. apply excluded_middle_irrefutable in H1. inversion H1.
Qed.

Theorem double_negation_elimination_valid : excluded_middle <-> double_negation_elimination.
Proof.
  split.
  - intros E P.
    destruct (E P) as [H' | H'].
    + intro HP. apply H'.
    + intro HNP. unfold not in H'. unfold not in HNP. apply HNP in H'. inversion H'.
  - intros DNE EXM. apply DNE. apply excluded_middle_irrefutable.
Qed.

Theorem de_morgan_not_and_not_valid : excluded_middle <-> de_morgan_not_and_not.
Proof.
  split.
  - intros E P Q.
    destruct (E P) as [HP | HP].
    + intro H. left. apply HP.
    + destruct (E Q) as [HQ | HQ].
      * intro H. right. apply HQ.
      * intro H. exfalso. apply H. split.
        { apply HP. }
        { apply HQ. }
  - intros D E. apply D. unfold not. intros [H1 H2]. apply H2. apply H1.
Qed.

Theorem implies_to_or_valid : excluded_middle <-> implies_to_or.
Proof.
  split.
  - intros E P Q.
    destruct (E P) as [HP | HP].
    + intro H. right. apply H. apply HP.
    + intro H. left. apply HP.
  - intros IO E. rewrite -> or_comm. apply IO. intro HE. apply HE.
Qed.