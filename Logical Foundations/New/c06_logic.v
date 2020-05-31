(** Capítulo 6 - (** * Logic in Coq  (Logic) *) *)

Set Warnings "-notation-overridden,-parsing".

From LF Require Export c05_tactics.

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof.
  simpl.
  reflexivity.
Qed.

Definition plus_fact : Prop := 2 + 2 = 4.

Theorem plus_fact_is_true :
  plus_fact.
Proof.
  reflexivity.
Qed.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H.
  injection H as H1.
  apply H1.
Qed.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, 
  A ->
  B ->
  A /\ B.
Proof.
  intros A B HA HB.
  split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
Qed.

(** Exercise: 2 stars (and_exercise)  *)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros [] [].
  -
    apply and_intro.
    reflexivity.
  -
    apply and_intro.
    reflexivity.
  -
    split.
    + inversion H.
    + inversion H.
  -
    split.
    + inversion H.
    + inversion H.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn.
  rewrite Hm.
  simpl.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn.
  rewrite Hm.
  simpl.
  reflexivity.
Qed.

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn.
  rewrite Hm.
  simpl.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  {
    apply and_exercise.
    apply H.
  }
  destruct H' as [Hn Hm].
  rewrite Hn.
  simpl.
  reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  apply HP.
Qed.

(** Exercise: 1 star, optional (proj2)  *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.

(** Exercise: 2 stars (and_assoc)  *)
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  destruct H as [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m H.
  destruct H as [Hn | Hm].
  -
    rewrite Hn.
    simpl.
    reflexivity.
  -
    rewrite Hm.
    rewrite <- mult_n_O.
    reflexivity.
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

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  -
    left.
    reflexivity.
  -
    right.
    simpl.
    reflexivity.
Qed.

(** Exercise: 1 star (mult_eq_0)  *)
Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  destruct n as [|n'].
  -
    left.
    reflexivity.
  -
    right.
    destruct m as [|m'].
    + reflexivity.
    + inversion H.
Qed.

(** Exercise: 1 star (or_commut)  *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H.
  -
    right.
    apply H0.
  -
    left.
    apply H0.
Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

(** Exercise: 2 stars, optional (not_implies_our_not)  *)
Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
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
  discriminate contra.
Qed.

Theorem zero_not_one' : 0 <> 1.
Proof.
  unfold not.
  intros contra.
  inversion contra.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not.
  intros H.
  apply H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q H.
  destruct H as [HP HNP].
  unfold not in HNP.
  apply HNP in HP.
  destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros PF.
  apply PF.
  apply H.
Qed.

(** Exercise: 2 stars, recommended (contrapositive)  *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ.
  unfold not.
  intros HQF.
  intros HP.
  apply HQF.
  apply HPQ.
  apply HP.
Qed.

Theorem contrapositive' : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  unfold not.
  intros P Q H H0 H1.
  apply H0 in H.
  destruct H.
  apply H1.
Qed.

(** Exercise: 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros HPPF.
  destruct HPPF.
  apply H0.
  apply H.
Qed.

(** Exercise: 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false' : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  unfold not.
  intros P [HP HNP].
  destruct HNP.
  apply HP.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  -
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H.
    reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  -
    unfold not in H.
    exfalso.
    apply H.
    reflexivity.
  - reflexivity.
Qed.

Lemma True_is_true : True.
Proof.
  apply I.
Qed.

Notation "P <-> Q" := (iff P Q) (at level 95, no associativity) : type_scope.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
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
  -
    intros H.
    rewrite H.
    intros H'.
    inversion H'.
Qed.

(** Exercise: 1 star, optional (iff_properties)  *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intro P.
  split.
  -
    intro H.
    apply H.
  -
    intro H.
    apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R [HPQ HQP] [HQR HRQ].
  split.
  -
    intro HP.
    apply HQR.
    apply HPQ.
    apply HP.
  -
    intro HR.
    apply HQP.
    apply HRQ.
    apply HR.
Qed.

(** Exercise: 3 stars (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [H1 | [H2 H3]].
    + apply and_intro.
      *
        left.
        apply H1.
      *
        left.
        apply H1.
    + apply and_intro.
      *
        right.
        apply H2.
      *
        right.
        apply H3.
  - intros [[H1 | H2] [H3 | H4]].
    +
      left.
      apply H1.
    +
      left.
      apply H1.
    +
      left.
      apply H3.
    +
      right.
      apply and_intro.
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

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros [H | [H | H]].
    +
      left.
      left.
      apply H.
    +
      left.
      right.
      apply H.
    +
      right.
      apply H.
  - intros [[H | H] | H].
    +
      left.
      apply H.
    +
      right.
      left.
      apply H.
    +
      right.
      right.
      apply H.
Qed.

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0.
  rewrite mult_0.
  rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  apply mult_0.
  apply H.
Qed.

(** Olhar esse erro 
Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

(** Exercise: 1 star, recommended (dist_not_exists)  *)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H.
  unfold not.
  intros [x E].
  destruct E.
  apply H.
Qed.


(** Exercise: 2 stars (dist_exists_or)  *)
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [x [PE | QE]].
    +
      left.
      exists x.
      apply PE.
    +
      right.
      exists x.
      apply QE.
  - intros [[x HPx] | [x HQx]].
    +
      exists x.
      left.
      apply HPx.
    +
      exists x.
      right.
      apply HQx.
Qed.

*)