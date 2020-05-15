(** Capítulo 7 - Inductively Defined Propositions (IndProp) *)

Set Warnings "-notation-overridden,-parsing".

From LF Require Export c06_logic.

Require Coq.omega.Omega.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Theorem ev_4' : ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n Hn.
  simpl.
  apply ev_SS.
  apply ev_SS.
  apply Hn.
Qed.

(** Exercise: 1 star, standard (ev_double)*)

Theorem ev_double : forall n, ev (double n).
Proof.
  intros n.
  induction n.
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.

Theorem ev_minus2 : forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E.
  - simpl. apply ev_0.
  - simpl. apply E.
Qed.

Theorem ev_minus2' : forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E.
  - simpl. apply ev_0.
  - simpl. apply H.
Qed.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n Hn.
  inversion Hn.
  apply H0.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H.
  inversion H.
Qed.

(** Exercise: 1 star (SSSSev__even) *)
Theorem SSSSev__even : forall n, ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H.
  inversion H1.
  apply H3.
Qed.

(** Exercise: 1 star (even5_nonsense)  *)
Theorem even5_nonsense : ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

(** Falta fazer

Lemma ev_even : forall n, ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - exists 0. reflexivity.
  - destruct IH as [k' Hk']. rewrite Hk'. exists (S k'). reflexivity.
Qed.

Theorem ev_even_iff : forall n, ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - apply ev_even.
  - intros [k Hk]. rewrite Hk. apply ev_double.
Qed.
*)

(** Exercise: 2 stars (ev_sum) *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m En Em.
  induction En.
  - simpl. apply Em.
  - simpl. apply ev_SS. apply IHEn.
Qed.

(** Exercise: 4 stars, advanced, optional (ev'_ev)  *)
Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  split.
  - intro En.
    induction En.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum.
      * apply IHEn1.
      * apply IHEn2.
  - intro En.
    induction En.
    + apply ev'_0.
    + assert (H : (S (S n) = 2 + n)).
      { reflexivity. }
      rewrite -> H. apply ev'_sum.
      * apply ev'_2.
      * apply IHEn.
Qed.