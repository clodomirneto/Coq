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

(** Exercise: 1 star, standard (inversion_practice) *)

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

Lemma ev_even : forall n, ev n -> exists k, eq n (double k).
Proof.
  intros n E.
  induction E.
  - exists 0. simpl. reflexivity.
  - destruct IHE. rewrite -> H. exists (S x). simpl. reflexivity.
Qed.

Theorem ev_even_iff : forall n, ev n <-> exists k, eq n (double k).
Proof.
  intros n.
  split.
  - apply ev_even.
  - intros [k Hk]. rewrite -> Hk. apply ev_double.
Qed.

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
    + assert (H : (S (S n) = 2 + n)). { reflexivity. }
      rewrite -> H. apply ev'_sum.
      * apply ev'_2.
      * apply IHEn.
Qed.

(** Exercise: 3 stars, advanced, recommended (ev_ev__ev) *)

Theorem ev_ev__ev : forall n m, ev (n + m) -> ev n -> ev m.
Proof.
  intros n m Enm En.
  generalize dependent Enm.
  induction En.
  - intro H. simpl in H. apply H.
  - intro H. simpl in H. apply ev_SS in IHEn.
    + inversion IHEn. apply H1.
    + inversion H. apply H1.
Qed.

(** Exercise: 3 stars, optional (ev_plus_plus)  *)

Theorem ev_plus_plus : forall n m p, ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p Hnm Hnp.
  assert (HH : (ev (n + m) -> ev ((n + p) + (m + p)))).
  {
  intro H.
  rewrite <- (plus_assoc n p (m + p)).
  rewrite -> (plus_assoc p m p).
  rewrite -> (plus_comm p m).
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  rewrite <- (plus_assoc (n + m) p).
  apply (ev_sum (n + m) (p + p)).
  - apply H.
  - rewrite <- double_plus. apply ev_double.
  }
  apply HH in Hnm.
  apply (ev_ev__ev (n + p)).
  - apply Hnm.
  - apply Hnp.
Qed.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Theorem test_le1 : le 3 3.
Proof.
  apply le_n.
Qed.

Theorem test_le2 : le 3 6.
Proof.
  apply le_S.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

Theorem test_le3 : le 2 1 -> 2 + 2 = 5.
Proof.
  intros H.
  inversion H.
  inversion H2.
Qed.

Definition lt (n m:nat) := le (S n) m.

Inductive square_of : nat -> nat -> Prop :=
  | sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

(** Exercise: 2 stars, standard, optional (total_relation) *)

Inductive total_relation : nat -> nat -> Prop :=
  | tr : forall n m, total_relation n m.

(** Exercise: 2 stars, optional (empty_relation)  *)

Inductive empty_relation : nat -> nat -> Prop :=
  | er : forall n m, False -> empty_relation n m.

(** Exercise: 3 stars, standard, optional (le_exercises) *)

Lemma le_trans : forall m n o, le m n -> le n o -> le m o.
Proof.
  intros m n o Hmn Hno.
  induction Hno.
  - apply Hmn.
  - apply le_S. apply IHHno. apply Hmn.
Qed.

Theorem O_le_n : forall n, le 0 n.
Proof.
  induction n.
  - apply le_n.
  - apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m, le n m -> le (S n) (S m).
Proof.
  intros n m H.
  induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m, le (S n) (S m) -> le n m.
Proof.
  intros n m H.
  inversion H.
  - apply le_n.
  - apply le_trans with (S n). apply le_S. apply le_n. apply H2.
Qed.

Theorem le_plus_l : forall a b, le a (a + b).
Proof.
  intros a b.
  induction a.
  - apply O_le_n.
  - apply n_le_m__Sn_le_Sm in IHa. apply IHa.
Qed.

Theorem plus_lt : forall n1 n2 m, lt (n1 + n2) m -> and (lt n1 m) (lt  n2 m).
Proof.
  unfold lt.
  intros n1 n2 m.
  split.
  - apply (le_trans (S n1) (S (n1 + n2))).
    + apply n_le_m__Sn_le_Sm. apply le_plus_l.
    + apply H.
  - apply (le_trans (S n2) (S (n1 + n2))).
    + apply n_le_m__Sn_le_Sm. rewrite -> plus_comm. apply le_plus_l.
    + apply H.
Qed.

Theorem lt_S : forall n m, lt n m -> lt n (S m).
Proof.
  unfold lt.
  intros n m H.
  apply le_S.
  apply H.
Qed.

Theorem leb_complete : forall n m, leb n m = true -> le n m.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  - intros n H.
    destruct n.
    + apply le_n.
    + inversion H.
  - intros n H.
    destruct n.
    + apply O_le_n.
    + simpl in H. apply IHm in H. apply n_le_m__Sn_le_Sm. apply H.
Qed.

Theorem leb_correct : forall n m, le n m -> leb n m = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  - intros n H. inversion H. simpl. reflexivity.
  - intros n H. destruct n.
    + simpl. reflexivity.
    + apply IHm. generalize dependent H. apply Sn_le_Sm__n_le_m .
Qed.

Theorem leb_true_trans : forall n m o, leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  intros n m o H H0.
  apply leb_complete in H.
  apply leb_complete in H0.
  apply leb_correct.
  generalize dependent H0.
  generalize dependent H.
  apply le_trans.
Qed.

(** Exercise: 2 stars, optional (leb_iff)  *)

Theorem leb_iff : forall n m, leb n m = true <-> le n m.
Proof.
  split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

(** Exercise: 2 stars, advanced (subsequence)  *)

Inductive subseq : list nat -> list nat -> Prop :=
| s1 : forall l, subseq [] l
| s2 : forall n l1 l2, subseq l1 l2 -> subseq (n :: l1) (n :: l2)
| s3 : forall n l1 l2, subseq l1 l2 -> subseq l1 (n :: l2).

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  induction l.
  - apply s1.
  - apply s2. apply IHl.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  induction l1.
  - destruct l2.
    + simpl. intros l3 H. apply s1.
    + simpl. intros l3 H. apply s1.
  - induction l2.
    + intros l3 H. inversion H.
    + intros l3 H. simpl. inversion H.
      * apply s2. apply IHl1. apply H1.
      * apply s3. apply IHl2. apply H2.
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros l1 l2 l3.
  generalize dependent l2.
  generalize dependent l1.
  induction l3 as [| x3 xs3 IHl3].
  intros l1 l2 H12 H23.
  inversion H23 as [ys | x ys xs Hst | x ys xs Hsa ].
  rewrite <- H in H12.
  inversion H12.
  apply s1.
  intros l1 l2 H12 H23.
  inversion H23 as [ys | x ys xs H23st | x ys xs H23sa ].
  rewrite <- H in H12.
  rewrite <- H in H23.
  inversion H12. apply s1.
  rewrite <- H1 in IHl3.
  rewrite <- H in H23.
  rewrite <- H in H12.
  rewrite <- H0.
  rewrite <- H0 in H23.
  rewrite <- H1 in H23.
  rewrite <- H1 in H23st.
  rewrite <- H1.
  inversion H12 as [ys1 | x1 ys1 xs1 H12st | x1 ys1 xs1 H12sa].
  apply s1.
  apply s2.
  apply (IHl3 ys1 ys).
  apply H12st.
  apply H23st.
  rewrite <- H2 in H12.
  rewrite <- H2 in H12sa.
  rewrite <- H2.
  apply s3.
  apply (IHl3 ys1 ys).
  apply H12sa.
  apply H23st.
  rewrite <- H in H12.
  rewrite <- H in H23.
  rewrite <- H in H23sa.
  rewrite <- H0 in H23.
  rewrite <- H0.
  rewrite <- H1 in IHl3.
  rewrite <- H1 in H23.
  rewrite <- H1 in H23sa.
  rewrite <- H1.
  inversion H12 as [ys1 | x1 ys1 xs1 H12st | x1 ys1 xs1 H12sa].
  apply s1.
  rewrite -> H0.
  apply s3.
  rewrite -> H2.
  apply (IHl3 l1 ys).
  apply H12.
  apply H23sa.
  apply s3.
  apply (IHl3 l1 ys).
  apply H12.
  apply H23sa.
Qed.

Inductive reg_exp {T : Type} : Type :=
| EmptySet : reg_exp
| EmptyStr : reg_exp
| Char : T -> reg_exp
| App : reg_exp -> reg_exp -> reg_exp
| Union : reg_exp -> reg_exp -> reg_exp
| Star : reg_exp -> reg_exp.

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall x, exp_match [x] (Char x)
| MApp : forall s1 re1 s2 re2,
           exp_match s1 re1 ->
           exp_match s2 re2 ->
           exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : forall re1 s2 re2,
              exp_match s2 re2 ->
              exp_match s2 (Union re1 re2)
| MStar0 : forall re, exp_match [] (Star re)
| MStarApp : forall s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H.
  inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl.
  apply (MApp [1]).
  + apply MChar.
  + apply (MApp [2]).
    - apply MChar.
    - apply (MApp [3]).
      * apply MChar.
      * apply MEmpty.
Qed.

Lemma MStar1 : forall T s (re : @reg_exp T), s =~ re -> s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(** Exercise: 3 stars, standard (exp_match_ex1) *)

Lemma empty_is_empty : forall T (s : list T), ~ (s =~ EmptySet).
Proof.
  intros T s H.
  inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 -> s =~ Union re1 re2.
Proof.
  intros T s re1 re2.
  intro H.
  inversion H.
  - apply (MUnionL s _ _). apply H0.
  - apply (MUnionR _ s _). apply H0.
Qed.

(** Exercise: 4 stars, optional (reg_exp_of_list_spec)  *)

Lemma reg_exp_of_list_spec : forall T (l1 l2 : list T),
  l1 =~ reg_exp_of_list l2 <-> l1 = l2.
Proof.
  split.
  - generalize dependent l1.
    induction l2 as [|m l2' IHl2].
    + simpl. intros l1 H. inversion H. reflexivity.
    + intros l1 H.
      inversion H.
      apply IHl2 in H4.
      assert (HH : (s4 =~ Char m -> s4 = [m])).
      { intro Ha. inversion Ha. rewrite H7 in H5. reflexivity. }
      rewrite HH. rewrite H4. reflexivity.
      apply H3.
  - generalize dependent l2.
    induction l1 as [|n l1' IHl1].
    + intros l2 H. rewrite <- H. simpl. apply MEmpty.
    + intros l2 H. rewrite <- H. simpl. apply (MApp [n] (Char n) l1' (reg_exp_of_list l1')).
      * apply MChar.
      * apply IHl1. reflexivity.
Qed.

Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T), s =~ re -> In x s -> In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - apply Hin.
  - apply Hin.
  - simpl. rewrite In_app_iff in *. destruct Hin as [Hin | Hin].
    + left. apply (IH1 Hin).
    + right. apply (IH2 Hin).
  - simpl. rewrite In_app_iff. left. apply (IH Hin).
  - simpl. rewrite In_app_iff. right. apply (IH Hin).
  - destruct Hin.
  - simpl. rewrite In_app_iff in Hin. destruct Hin as [Hin | Hin].
    + apply (IH1 Hin).
    + apply (IH2 Hin).
Qed.

(** Exercise: 4 stars (re_not_empty)  *)
Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
  | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
  | Star re => true
  end.

(* orb_true_iff provar isso

Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  split.
  - intros [s Hmatch].
    induction Hmatch
      as [| x'
          | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
          | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
          | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
    + reflexivity.
    + reflexivity.
    + simpl. rewrite IH1. rewrite IH2. reflexivity.
    + simpl. rewrite IH. reflexivity.
    + simpl. apply orb_true_iff. right. apply IH.
    + simpl. reflexivity.
    + reflexivity.
  - intro H. induction re.
    + inversion H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + simpl in H.
      apply andb_true_iff in H.
      destruct H.
      apply IHre1 in H.
      destruct H as [s1 H1].
      apply IHre2 in H0.
      destruct H0 as [s2 H2].
      exists (s1 ++ s2). apply (MApp _ re1 _ re2).
      * apply H1.
      * apply H2.
    + inversion H. apply orb_true_iff in H1.
      inversion H1.
      * apply IHre1 in H0. inversion H0. exists x. apply MUnionL. apply H2.
      * apply IHre2 in H0. inversion H0. exists x. apply MUnionR. apply H2.
    + exists []. apply MStar0.
Qed.
*)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'. intros s H. apply H.
  - inversion Heqre'. rewrite H0 in IH2, Hmatch1. intros s2 H1. rewrite <- app_assoc. apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * reflexivity.
      * apply H1.
Qed.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H.
  destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

(** Exercise: 2 stars, recommended (reflect_iff)  *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H.
  inversion H.
  - split.
    + intro HP. reflexivity.
    + intro HT. apply H0.
  - split.
    + intro HP. exfalso. unfold not in H0. apply H0. apply HP.
    + intro HT. inversion HT.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if eqb n m then 1 else 0) + count n l'
  end.