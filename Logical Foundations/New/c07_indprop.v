(** Capítulo 7 - Inductively Defined Propositions (IndProp) *)

Set Warnings "-notation-overridden,-parsing".

From LF Require Export c06_logic.

Require Coq.omega.Omega.

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS : forall n : nat, even n -> even (S (S n)).

Theorem ev_4 : even 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Theorem ev_4' : even 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n.
  simpl.
  intros Hn.
  apply ev_SS.
  apply ev_SS.
  apply Hn.
Qed.

Theorem ev_double : forall n,
  even (double n).
Proof.
  induction n as [|n' IHn].
  - apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.

Theorem ev_minus2 : forall n,
  even n -> even (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  - simpl. apply ev_0.
  - simpl. apply E'.
Qed.

Theorem evSS_ev : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  apply E'.
Qed.

Theorem one_not_even : ~ even 1.
Proof.
  intros H.
  inversion H.
Qed.

(** Exercise: 1 star (SSSSev__even) *)
Theorem SSSSev__even : forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
  intros n H.
  inversion H.
  inversion H1.
  apply H3.
Qed.

(** Exercise: 1 star (even5_nonsense)  *)
Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H.
  inversion H1.
  inversion H3.
Qed.