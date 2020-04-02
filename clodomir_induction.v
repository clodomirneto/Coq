(** Capítulo 2 - Proof by Induction    (Induction) *)

From LF Require Export clodomir_basics.

(** Exemplos induction *)

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

(** Exercise: 2 stars, standard, recommended (basic_induction) *)

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

(** Exercise: 2 stars, standard (double_plus) *)

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

(** Exercise: 2 stars, standard, optional (evenb_S) *)

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

(** Exemplo assert *)

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

(** Exercise: 2 stars, advanced, recommended (plus_comm_informal)  *)

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

Theorem plus_swap : forall x y z : nat,
  x + (y + z) = y + (x + z).
Proof.
  intros x y z.
  rewrite -> plus_assoc.
  assert (H: x + y = y + x).
  {
    rewrite -> plus_comm.
    reflexivity.
  }
  rewrite -> H. 
  rewrite -> plus_assoc.
  reflexivity.
Qed.

Theorem mult_x_0 : forall x : nat,
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

Theorem mult_x_Sy: forall x y : nat,
  x * S y = x + x * y.
Proof.
  intros x y.
  induction x as [|x' IHx].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite -> IHx.
    rewrite plus_swap.
    reflexivity.
Qed.

Theorem mult_comm : forall x y : nat,
  x * y = y * x.
Proof.
  intros x y.
  induction x as [|x' IHx].
  -
    rewrite -> mult_x_0.
    simpl.
    reflexivity.
  -
    simpl.
    rewrite -> mult_x_Sy.
    rewrite -> IHx.
    reflexivity.
Qed.

Check leb.

Theorem leb_refl : forall x:nat,
  true = leb x x.
Proof.
  intros x.
  induction x as [|x' IHx].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite <- IHx.
    reflexivity.
Qed.

Theorem zero_neqb_S : forall x : nat,
  eqb 0 (S x) = false.
Proof.
  intros x.
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_leb_compat_l : forall x y z : nat,
  leb x y = true -> leb (z + x) (z + y) = true.
Proof.
  intros x y z H.
  induction z as [|z' IHz].
  -
    simpl.
    rewrite -> H.
    reflexivity.
  -
    simpl.
    rewrite -> IHz.
    reflexivity.
Qed.

Theorem S_neqb_0 : forall x : nat,
  eqb (S x) 0 = false.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem mult_1_l : forall x : nat, 
  1 * x = x.
Proof.
  intros x.
  simpl.
  rewrite <- plus_x_O.
  reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  intros [][].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem mult_plus_distr_r : forall x y z : nat,
  (x + y) * z = (x * z) + (y * z).
Proof.
  intros x y z.
  induction x as [|x' IHx].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite -> IHx.
    rewrite -> plus_assoc.
    reflexivity.
Qed.

Theorem mult_assoc : forall x y z : nat,
  x * (y * z) = (x * y) * z.
Proof.
  intros x y z.
  induction x as [|x' IHx].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite -> IHx.
    rewrite -> mult_plus_distr_r.
    reflexivity.
Qed.

Theorem eqb_refl : forall x : nat,
  true = eqb x x.
Proof.
  intros x.
  induction x as [|x' IHx].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite <- IHx.
    reflexivity.
Qed.

Theorem plus_swap' : forall x y z : nat,
  x + (y + z) = y + (x + z).
Proof.
  intros x y z.
  rewrite -> plus_assoc.
  replace (x + y) with (y + x).
  -
    rewrite -> plus_assoc.
    reflexivity.
  -
    rewrite -> plus_comm.
    reflexivity.
Qed.

Module binnats.

  Inductive bin : Set :=
  | O : bin
  | D : bin -> bin
  | P : bin -> bin.

  Fixpoint bininc (b:bin) : bin :=
    match b with
      | O => P O
      | D b' => P b'
      | P b' => D (bininc b')
    end.

  Fixpoint bin2nat (b:bin) : nat :=
    match b with
      | O => 0
      | D b' => double (bin2nat b')
      | P b' => S (double (bin2nat b'))
    end.

  Theorem bin2nat_bininc_comm : forall b:bin,
    bin2nat (bininc b) = S (bin2nat b).
    Proof.
      intros b.
      induction b.
      reflexivity.
      reflexivity.
      simpl.
      rewrite IHb.
      reflexivity.
    Qed.

    Fixpoint nat2bin (n:nat) : bin :=
      match n with
        | 0 => O
        | S n' => bininc (nat2bin n')
      end.

    Theorem nat2bin2nat_id : forall n:nat,
      bin2nat (nat2bin n) = n.
      intros n.
      induction n.
      reflexivity.
      simpl.
      rewrite bin2nat_bininc_comm.
      rewrite IHn.
      reflexivity.
    Qed.

    Eval simpl in (nat2bin (bin2nat O)).
    Eval simpl in (nat2bin (bin2nat (D (D (D O))))).

    Fixpoint normalize (b:bin) : bin :=
      match b with
        | O => O
        | D b' => match normalize b' with
                    | O => O
                    | nb => D nb
                  end
        | P b' => P (normalize b')
      end.

Definition imp_id_proof := fun (p:Prop) => (fun (d:p) => d).

Check imp_id_proof (3=3).
Check imp_id_proof (3=3) (refl_equal 3).

Theorem imp_id : forall P:Prop, P -> P.
  intro p.
  intro d.
  exact d.
Qed.

Print imp_id.

(** Eval simpl in bininc (normalize (D (P (D O)))) = (normalize (P (P (D O)))). *)

Definition bindouble (b:bin) : bin :=
  match b with
    | O => O
    | D n' => D (D n')
    | P n' => D (P n')
  end.

Lemma bininc_twice : forall b:bin,
  bininc (bininc (bindouble b)) = bindouble (bininc b).
  Proof.
    destruct b.
    reflexivity.
    reflexivity.
    reflexivity.
  Qed.

Lemma double_bindouble : forall n:nat,
  nat2bin (double n) = (bindouble (nat2bin n)).
  Proof.
    intro n.
    induction n.
    reflexivity.
    simpl.
    rewrite IHn.
    rewrite bininc_twice.
    reflexivity.
  Qed.

Lemma bininc_bindouble: forall b:bin,
  bininc (bindouble b) = P b.
  intro b.
  destruct b.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

Theorem bin2nat2bin_n_eq_norm_n : forall b:bin,
  nat2bin (bin2nat b) = normalize b.
  Proof.
    intro b.
    induction b.
    reflexivity.
    simpl.
    rewrite double_bindouble.
    rewrite IHb.
    unfold bindouble.
    reflexivity.
    simpl.
    rewrite double_bindouble.
    rewrite IHb.
    rewrite bininc_bindouble.
    reflexivity.
  Qed.

End binnats.