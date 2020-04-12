(** Capítulo 5 - (** * Tactics: More Basic Tactics *) *)

Set Warnings "-notation-overridden,-parsing".

From LF Require Export clodomir_poly.

(** Tática Apply *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n; o] = [n; p] ->
     [n; o] = [m; p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Theorem silly1' : forall (n m o p : nat),
     n = m  ->
     [n; o] = [n; p] ->
     [n; o] = [m; p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q; o] = [r; p]) ->
     [n; o] = [m; p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly2a : forall (n m : nat),
     (n, n) = (m, m)  ->
     (forall (q r : nat), (q, q) = (r, r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

(** Exercise: 2 stars, optional (silly_ex)  *)

Theorem silly_ex : (forall n, evenb n = true -> oddb (S n) = true) ->
     oddb 3 = true ->
     evenb 4 = true.
Proof.
  intros H H0.
  apply H0.
Qed.

Theorem silly3_firsttry : forall (n : nat),
     true = eqb n 5  ->
     eqb (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H.
Qed.

(** Exercise: 3 stars (apply_exercise1)  *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.
  rewrite -> H.
  symmetry.
  apply rev_involutive.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a; b] = [c; d] ->
     [c; d] = [e; f] ->
     [a; b] = [e; f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Theorem trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a; b] = [c; d] ->
     [c; d] = [e; f] ->
     [a; b] = [e; f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c; d]).
  apply eq1.
  apply eq2.
Qed.

(** Exercise: 3 stars, optional (apply_with_exercise)  *)

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p H H0.
  apply trans_eq with m.
  apply H0.
  apply H.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2 : n = pred (S n)). { reflexivity. }
  rewrite H2.
  rewrite H1.
  reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H.
  intros Hnm.
  exact Hnm.
Qed.

Theorem S_injective'' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H.
  intros Hmo Hno.
  rewrite Hmo.
  rewrite Hno.
  reflexivity.
Qed.

Theorem injection_ex1' : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  inversion H.
  reflexivity.
Qed.

Theorem injection_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm.
  rewrite Hnm.
  reflexivity.
Qed.

(** Exercise: 1 star (inversion_ex3)  *)
Example inversion_ex3 : forall (X : Type) (x y z w : X) (l j : list X),
  x :: y :: l = w :: z :: j ->
  x :: l = z :: j ->
  x = y.
Proof.
  intros X x y z w l j H H0.
  inversion H.
  inversion H0.
  apply trans_eq with x.
  symmetry.
  apply H2.
  apply H5.
Qed.

Theorem eqb_0_l : forall n,
   eqb 0 n = true -> n = 0.
Proof.
  destruct n as [| n'].
  -
    intros H.
    reflexivity.
  -
    simpl.
    intros H.
    discriminate H.
Qed.

Theorem eqb_0_l' : forall n,
   eqb 0 n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'].
  -
    simpl.
    reflexivity.
  -
    simpl.
    intros H.
    inversion H.
Qed.

Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra.
  discriminate contra.
Qed.

Theorem discriminate_ex1' : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra.
  inversion contra.
Qed.

Theorem discriminate_ex2 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra.
  discriminate contra.
Qed.

Theorem discriminate_ex2' : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra.
  inversion contra.
Qed.

(** Exercise: 1 star, standard (discriminate_ex3)  *)
Example discriminate_ex3 : forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j H.
  inversion H.
Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B ) (x y: A),
x = y -> f x = f y.
Proof.
  intros A B f x y eq.
  rewrite eq.
  reflexivity.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     eqb (S n) (S m) = b  ->
     eqb n m = b.
Proof.
  intros n m b H.
  simpl in H.
  apply H.
Qed.

Theorem silly3' : forall (n : nat),
  (eqb n 5 = true -> eqb (S (S n)) 7 = true) -> 
  true = eqb n 5  ->
  true = eqb (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H.
  apply eq in H.
  symmetry in H.
  apply H.
Qed.

(** Exercise: 3 stars, recommended (plus_n_n_injective)  *)
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n.
  induction n as [| n'].
  -
    intros m H.
    destruct m as [|m'].
    + reflexivity.
    + inversion H.
  -
    intros m H.
    destruct m as [|m'].
    + inversion H.
    +
      apply f_equal.
      apply IHn'.
      simpl in H.
      rewrite <- plus_n_Sm in H.
      rewrite <- plus_n_Sm in H.
      inversion H.
      apply H1.
Qed.

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n.
  induction n as [| n'].
  -
    simpl.
    intros m eq.
    destruct m as [| m'].
    + reflexivity.
    + inversion eq.
  -
    simpl.
    intros m eq.
    destruct m as [| m'].
    + inversion eq.
    +
      apply f_equal.
      apply IHn'.
      simpl in eq.
      inversion eq.
      reflexivity.
  Qed.

(** Exercise: 2 stars (beq_nat_true)  *)
Theorem eqb_true : forall n m,
    eqb n m = true -> n = m.
Proof.
  intro n.
  induction n as [|n' IHn].
  -
    intros m H.
    destruct m as [|m'].
    + reflexivity.
    +
      simpl in H.
      inversion H.
  -
    intros m H.
    destruct m as [|m'].
    + inversion H.
    +
      apply f_equal.
      apply IHn.
      simpl in H.
      apply H.
Qed.

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  -
    simpl.
    intros n eq.
    destruct n as [| n'].
    + reflexivity.
    + inversion eq.
  -
    intros n eq.
    destruct n as [| n'].
    + inversion eq.
    +
      apply f_equal.
      apply IHm'.
      inversion eq.
      reflexivity.
Qed.

Theorem eqb_id_true : forall x y,
  eqb_id x y = true -> x = y.
Proof.
  intros [m] [n].
  simpl.
  intros H.
  assert (H' : m = n).
  { apply eqb_true.
    apply H. 
  }
  rewrite H'.
  reflexivity.
Qed.

(** Exercise: 3 stars, recommended (gen_dep_practice) *) (**
Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     xth_error l n = None.
Proof.
  intros n X l H.
  generalize dependent n.
  induction l as [|m' l' IHl].
  - reflexivity.
  -
    intros n H.
    destruct n as [|n'].
    + inversion H.
    +
      simpl.
      inversion H.
      apply IHl.
      reflexivity.
Qed.
*)

Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  {
    rewrite mult_comm.
    apply mult_assoc.
  }
  rewrite H.
  rewrite mult_assoc.
  reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m.
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if eqb n 3 then false
  else if eqb n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n.
  unfold sillyfun.
  destruct (eqb n 3).
    -  reflexivity.
    -  destruct (eqb n 5).
      + reflexivity.
      +  reflexivity.
Qed.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [|n l' IHl].
  -
    intros l1 l2 H.
    inversion H.
    reflexivity.
  -
    destruct n as (x, y).
    simpl.
    destruct (split l').
    intros l1 l2 H.
    inversion H.
    induction l1 as [|m l1' IHl1].
    + inversion H1.
    +
      inversion H1.
      inversion H2.
      simpl.
      rewrite -> IHl.
      reflexivity.
      rewrite -> H4.
      reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if eqb n 3 then true
  else if eqb n 5 then true
  else false.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq.
  unfold sillyfun1 in eq.
  destruct (eqb n 3) eqn:Heqe3.
  -
    apply eqb_true in Heqe3.
    rewrite -> Heqe3.
    reflexivity.
  -
    destruct (eqb n 5) eqn:Heqe5.
    +
      apply eqb_true in Heqe5.
      rewrite -> Heqe5.
      reflexivity.
    + inversion eq.
Qed.

(** Exercise: 2 stars (destruct_eqn_practice)  *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  - destruct (f true) eqn:H1.
    + rewrite -> H1.  apply H1.
    + destruct (f false) eqn:H2.
      * apply H1.
      * apply H2.
  - destruct (f false) eqn:H3.
    + destruct (f true) eqn:H4.
      * apply H4.
      * apply H3.
    +
      rewrite -> H3.
      apply H3.
Qed.

(** * Review *)

(** We've now seen many of Coq's most fundamental tactics.  We'll
    introduce a few more in the coming chapters, and later on we'll
    see some more powerful _automation_ tactics that make Coq help us
    with low-level details.  But basically we've got what we need to
    get work done.

    Here are the ones we've seen:

      - [intros]: move hypotheses/variables from goal to context

      - [reflexivity]: finish the proof (when the goal looks like [e =
        e])

      - [apply]: prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]: apply a hypothesis, lemma, or constructor to
        a hypothesis in the context (forward reasoning)

      - [apply... with...]: explicitly specify values for variables
        that cannot be determined by pattern matching

      - [simpl]: simplify computations in the goal

      - [simpl in H]: ... or a hypothesis

      - [rewrite]: use an equality hypothesis (or lemma) to rewrite
        the goal

      - [rewrite ... in H]: ... or a hypothesis

      - [symmetry]: changes a goal of the form [t=u] into [u=t]

      - [symmetry in H]: changes a hypothesis of the form [t=u] into
        [u=t]

      - [unfold]: replace a defined constant by its right-hand side in
        the goal

      - [unfold... in H]: ... or a hypothesis

      - [destruct... as...]: case analysis on values of inductively
        defined types

      - [destruct... eqn:...]: specify the name of an equation to be
        added to the context, recording the result of the case
        analysis

      - [induction... as...]: induction on values of inductively
        defined types

      - [inversion]: reason by injectivity and distinctness of
        constructors

      - [assert (H: e)] (or [assert (e) as H]): introduce a "local
        lemma" [e] and call it [H]

      - [generalize dependent x]: move the variable [x] (and anything
        else that depends on it) from the context back to an explicit
        hypothesis in the goal formula *)

(** Exercise: 3 stars (eqb_sym)  *)
Theorem eqb_sym : forall (n m : nat),
  eqb n m = eqb m n.
Proof.
  intros n.
  induction n as [|n' IHn]. 
  -
    intros [].
    + reflexivity.
    + reflexivity.
  -
    intros [].
    + reflexivity.
    +
      simpl.
      apply IHn.
Qed.

(** Exercise: 3 stars, optional (beq_nat_trans)  *)
Theorem eqb_trans : forall n m p,
  eqb n m = true ->
  eqb m p = true ->
  eqb n p = true.
Proof.
  intros n m p H1 H2.
  apply eq_trans with (eqb n m).
  apply f_equal.
  apply eqb_true in H2.
  symmetry.
  apply H2.
  apply H1.
Qed.

(** Exercise: 3 stars, advanced (split_combine)  *)

Check @list (nat*nat).

Definition split_combine_statement : Prop :=
  forall (X Y : Type) (l1 : list X) (l2 : list Y),
    length l1 = length l2 ->
    split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l1.
  induction l1 as [|n l1' IHl].
  - intros l2 H.
    destruct l2 as [|m l2'].
    + reflexivity.
    + inversion H.
  -
    intros l2 H.
    destruct l2 as [|m l2'].
    +  inversion H.
    +
      inversion H.
      apply IHl in H1.
      simpl.
      rewrite H1.
      reflexivity.
Qed.

(** Exercise: 3 stars, advanced (filter_exercise)  *)
Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l.
  generalize dependent x.
  induction l as [|n l' IHl].
  -
    intros x lf H.
    simpl in H.
    inversion H.
  -
    intros x lf H. simpl in H.
    destruct (test n) eqn:Htst1.
    +
      inversion H.
      rewrite H1 in Htst1.
      apply Htst1.
    +
      apply IHl in H.
      apply H.
Qed.

Fixpoint forallb {X : Type} (f : X -> bool) (l : list X) :=
  match l with
  | nil => true
  | h :: t => andb (f h) (forallb f t)
  end.

Fixpoint existsb {X : Type} (f : X -> bool) (l : list X) :=
  match l with
  | nil => false
  | h :: t => orb (f h) (existsb f t)
  end.

Definition existsb' {X : Type} (f : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (f x)) l).

Example forallb1 : forallb oddb [1; 3; 5; 7; 9] = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example forallb2 : forallb negb [false; false] = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example forallb3 : forallb evenb [0; 2; 4; 5] = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example forallb4 : forallb (eqb 5) [] = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example existsb1 : existsb (eqb 5) [0; 2; 3; 6] = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example existsb2 : existsb (andb true) [true; true; false] = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example existsb3 : existsb oddb [1; 0; 0; 0; 0; 3] = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example existsb4 : existsb evenb [] = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example existsb'1 : existsb' (eqb 5) [0; 2; 3; 6] = false.
Proof.
  reflexivity.
Qed.

Example existsb'2 : existsb' (andb true) [true; true; false] = true.
Proof.
  reflexivity.
Qed.

Example existsb'3 : existsb' oddb [1; 0; 0; 0; 0; 3] = true.
Proof.
  reflexivity.
Qed.

Example existsb'4 : existsb' evenb [] = false.
Proof.
  reflexivity.
Qed.

(** Theorem existsb_existsb' : forall (X : Type) (f : X -> bool) (l : list X),
  existsb f l = existsb' f l.
Proof.
  intros X f l.
  induction l as [|n l' IHl].
  - reflexivity.
  -
    destruct (f n) eqn:Hfn1.
    +
      unfold existsb'.
      simpl.
      rewrite -> Hfn1.
      reflexivity.
    +
      assert (H : existsb' f (n :: l') = f n \/ existsb' f l').
      {
        rewrite -> Hfn1.
        unfold existsb'.
        simpl. rewrite -> Hfn1.
        reflexivity.
      }
      rewrite -> H.
      rewrite <- IHl.
      reflexivity.
Qed.
*)
