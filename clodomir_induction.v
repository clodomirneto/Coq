(* Capítulo 2 - Proof by Induction    (Induction) *)

From LF Require Export clodomir_basics.

(* Exemplos induction *)

Theorem plus_x_O : forall x:nat, 
  x = x + 0.
Proof.
  intros x.
  induction x as [| x' IHx].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite <- IHx.
    reflexivity.
Qed.

Theorem minus_diag : forall x,
  x - x = 0.
Proof.
  intros x.
  induction x as [| x' IHx].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite -> IHx.
    reflexivity.
Qed.

(* Exercise: 2 stars, standard, recommended (basic_induction) *)

Theorem mult_0_r : forall x:nat,
  x * 0 = 0.
Proof.
  intros x.
  induction x as [|x' IHx].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite -> IHx.
    reflexivity.
Qed.

Theorem plus_x_Sy : forall x y : nat,
  S (x + y) = x + (S y).
Proof.
  intros x y.
  induction x as [|x' IHx].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite -> IHx.
    reflexivity.
Qed.

Theorem plus_comm : forall x y : nat,
  x + y = y + x.
Proof.
  intros x y.
  induction x as [|x' IHx].
  -
    simpl.
    rewrite <- plus_x_O.
    reflexivity.
  -
    simpl.
    rewrite -> IHx.
    rewrite -> plus_x_Sy.
    reflexivity.
Qed.

Theorem plus_assoc : forall x y z : nat,
  x + (y + z) = (x + y) + z.
Proof.
  intros x y z.
  induction x as [|x' IHx].
  - reflexivity.
  -
    simpl.
    rewrite -> IHx.
    reflexivity.
Qed.

(* Exercise: 2 stars, standard (double_plus) *)

Fixpoint double (x:nat) :=
  match x with
  | O => O
  | S x' => S (S (double x'))
  end.

Lemma double_plus : forall x, double x = x + x .
Proof.
  intros x.
  induction x as [|x' IHx].
  -
    simpl.
    reflexivity.
  -
   simpl.
   rewrite -> IHx.
   rewrite <- plus_x_Sy.
   reflexivity.
Qed.

(* Exercise: 2 stars, standard, optional (evenb_S) *)

Theorem evenb_S : forall x : nat,
  evenb (S x) = negb (evenb x).
Proof.
  intros x.
  induction x as [|x' IHx].
  -
    simpl.
    reflexivity.
  -
    rewrite -> IHx.
    rewrite -> negb_involutive.
    reflexivity.
Qed.

(* Exemplo assert *)

Theorem mult_0_plus' : forall x y : nat,
  (0 + x) * y = x * y.
Proof.
  intros x y.
  assert (H: 0 + x = x). 
  {
    simpl.
    reflexivity.
  }
  rewrite <- H.
  simpl.
  reflexivity.
Qed.

Theorem plus_rearrange : forall x y z t : nat,
  (x + y) + (z + t) = (y + x) + (z + t).
Proof.
  intros x y z t.
  assert (H: x + y = y + x).
  {
    rewrite -> plus_comm.
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
  Qed.

Theorem plus_assoc' : forall x y z : nat,
  x + (y + z) = (x + y) + z.
Proof.
  intros x y z.
  induction x as [| x' IHx].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite -> IHx.
    reflexivity.
Qed.

Theorem plus_assoc'' : forall x y z : nat,
  x + (y + z) = (x + y) + z.
Proof.
  intros x y z.
  induction x as [| x' IHx].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite -> IHx.
    reflexivity.
Qed.

(* Exercise: 2 stars, advanced, recommended (plus_comm_informal)  *)

(** Translate your solution for [plus_comm] into an informal proof:

    Theorem: Addition is commutative.

    _Theorem_: For any [n] and [m],
        n + m = m + n

Proof : By induction on [n].

- First, suppose [n = 0].  We must show:
        0 + m = m + 0, it follows from the definition of [+].

- Next, suppose [n = S n'], with
        n' + m = m + n', then
        S n' + m = m + S n' -- apply [+] and plus_n_Sm
        S (n' + m) = S (m + n') -- apply hypotesis
        S (m + n') = S (m + n'). 
Qed.

*)