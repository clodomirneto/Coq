(** Capítulo 1 - Functional Programming in Coq (Basics) *)

(** Booleano *)

Inductive bool : Type :=
  | true : bool
  | false: bool.

(** Negação *)

Definition negb (x: bool) : bool :=
  match x with
    | true => false
    | false => true
  end.

Notation "~ x" := (negb x).

(** Tabela Verdade - Negação *)

Compute (negb true).

Example test_negb1 : (negb true) = false.
Proof. 
  simpl.
  reflexivity.
Qed.

Compute (negb false).

Example test_negb2 : (negb false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

(** Conjunção *)

Definition andb (x y: bool) : bool :=
  match (x, y) with
    | (true, true) => true
    | _ => false
  end.

Notation "x /\ y" := (andb x y).

(** Tabela Verdade - Conjunção *)

Compute (andb true true).

Example test_andb1 : (andb true true) = true.
Proof.
  reflexivity.
Qed.

Compute (andb true false).

Example test_andb2 : (andb true false) = false.
Proof.
  reflexivity.
Qed.

Compute (andb false true).

Example test_andb3 : (andb false true) = false.
Proof.
  reflexivity.
Qed.

Compute (andb false false).

Example test_andb4 : (andb false false) = false.
Proof.
  reflexivity.
Qed.

(** Disjunção *)

Definition orb (x y: bool) : bool :=
  match (x, y) with
    | (false, false) => false
    | _ => true
  end.

Notation "x \/ y" := (orb x y).

(** Tabela Verdade - Disjunção *)

Compute (orb true true).

Example test_orb1 : (orb true true) = true.
Proof.
  reflexivity.
Qed.

Compute (orb true false).

Example test_orb2 : (orb true false) = true.
Proof.
  reflexivity.
Qed.

Compute (orb false true).

Example test_orb3 : (orb false true) = true.
Proof.
  reflexivity.
Qed.

Compute (orb false false).

Example test_orb4 : (orb false false) = false.
Proof.
  reflexivity.
Qed.

(** Implicação *)

Definition implb (x y: bool) : bool :=
  match (x, y) with
    | (true, false) => false
    | _ => true
  end.

Notation "x -> y" := (implb x y).

(** Tabela Verdade - Implicação *)

Compute (implb true true).

Example test_implb1 : (implb true true) = true.
Proof.
  reflexivity.
Qed.

Compute (implb true false).

Example test_implb2 : (implb true false) = false.
Proof.
  reflexivity.
Qed.

Compute (implb false true).

Example test_implb3 : (implb false true) = true.
Proof.
  reflexivity.
Qed.

Compute (implb false false).

Example test_implb4 : (implb false false) = true.
Proof.
  reflexivity.
Qed.

(** Bi-implicação *)

Definition biimplb (x y: bool) : bool :=
  match (x, y) with
    | (true, true) => true
    | (false, false) => true
    | _ => false
  end.

Notation "x <-> y" := (biimplb x y).

(** Tabela Verdade - Bi-implicação *)

Compute (biimplb true true).

Example test_biimplb1 : (biimplb true true) = true.
Proof.
  reflexivity.
Qed.

Compute (biimplb true false).

Example test_biimplb2 : (biimplb true false) = false.
Proof.
  reflexivity.
Qed.

Compute (biimplb false true).

Example test_biimplb3 : (biimplb false true) = false.
Proof.
  reflexivity.
Qed.

Compute (biimplb false false).

Example test_biimplb4 : (biimplb false false) = true.
Proof.
  reflexivity.
Qed.

(** Exercise: 1 star, standard (nandb) *)

Definition nandb (x y: bool) : bool :=
  match (x, y) with
    | (true, true) => false
    | _ => true
  end.

Compute (nandb true false).

Example test_nandb1: (nandb true false) = true.
Proof.
  reflexivity.
Qed.

Compute (nandb false false).

Example test_nandb2: (nandb false false) = true.
Proof.
  reflexivity.
Qed.

Compute (nandb false true).

Example test_nandb3: (nandb false true) = true.
Proof.
  reflexivity.
Qed.

Compute (nandb true true).

Example test_nandb4: (nandb true true) = false.
Proof.
  reflexivity.
Qed.

(** Exercise: 1 star, standard (andb3) *)

Definition andb3 (x y z: bool) : bool :=
  match (x, y, z) with
    | (true, true, true) => true
    | _ => false
  end.

Compute (andb3 true true true).

Example test_andb31: (andb3 true true true) = true.
Proof.
  reflexivity.
Qed.

Compute (andb3 false true true).

Example test_andb32: (andb3 false true true) = false.
Proof.
  reflexivity.
Qed.

Compute (andb3 true false true).

Example test_andb33: (andb3 true false true) = false.
Proof.
  reflexivity.
Qed.

Compute (andb3 true true false).

Example test_andb34: (andb3 true true false) = false.
Proof.
  reflexivity.
Qed.

(** Naturais *)

Definition minustwo (x : nat) : nat :=
  match x with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

(** Par *)

Fixpoint evenb (x: nat) : bool :=
  match x with
    | O => true
    | S O => false
    | S (S x') => evenb x'
  end.

Compute (evenb 2).

Example test_evenb1 : (evenb 2) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Compute (evenb 3).

Example test_evenb2 : (evenb 3) = false.
Proof.
  simpl.
  reflexivity.
Qed.

(** Ímpar *)

Fixpoint oddb (x: nat) : bool :=
  match x with
    | O => false
    | S O => true
    | S (S x') => oddb x'
  end.

Compute (oddb 3).

Example test_oddb1 : (oddb 3) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Compute (oddb 2).

Example test_oddb2 : (oddb 2) = false.
Proof.
  simpl.
  reflexivity.
Qed.

(** Adição *)

Fixpoint plus (x y : nat) : nat :=
  match x with
    | O => y
    | S x' => S (plus x' y)
  end.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.

Compute (plus 2 3).

Example test_plus1 : (plus 2 3) = 5.
Proof.
  simpl.
  reflexivity.
Qed.

(** Subtração *)

Fixpoint minus (x y:nat) : nat :=
  match x, y with
    | O, _ => O
    | S _ , O => x
    | S x', S y' => minus x' y'
  end.

Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.

Compute (minus 5 2).

Example test_minus1 : (minus 5 2) = 3.
Proof.
  simpl.
  reflexivity.
Qed.

(** Multiplicação *)

Fixpoint mult (x y : nat) : nat :=
  match x with
    | O => O
    | S x' => plus y (mult x' y)
  end.

Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Compute (mult 3 4).

Example test_mult1: (mult 3 4) = 12.
Proof.
  simpl.
  reflexivity.
Qed.

(** Potenciação *)

Fixpoint exp (b p : nat) : nat :=
  match p with
    | O => S O
    | S p' => mult b (exp b p')
  end.

Notation "x ^ y" := (exp x y).

Compute (exp 3 2).

Example test_exp1 : (exp 3 2) = 9.
Proof.
  simpl.
  reflexivity.
Qed.

(** Exercise: 1 star, standard (factorial) *)

Fixpoint factorial (x: nat) : nat :=
  match x with
    | O => 1
    | S x' => x * (factorial x')
  end.

Compute (factorial 3).

Example test_factorial1: (factorial 3) = 6.
Proof.
  simpl.
  reflexivity.
Qed.

Compute (factorial 5).

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof.
  simpl.
  reflexivity.
Qed.

(** Função 'igual que' *)

Fixpoint eqb (x y : nat) : bool :=
  match x with
    | O => match y with
      | O => true
      | S y' => false
    end
    | S x' => match y with
      | O => false
      | S y' => eqb x' y'
    end
  end.

Notation "x = y" := (eqb x y) (at level 70) : nat_scope.

Compute (eqb 3 3).

Example test_eqb1 : (eqb 3 3) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Compute (eqb 2 3).

Example test_eqb2 : (eqb 2 3) = false.
Proof.
  simpl.
  reflexivity.
Qed.

(** Função 'menor ou igual que' *)

Fixpoint leb (x y : nat) : bool :=
  match x with
    | O => true
    | S x' => match y with
      | O => false
      | S y' => leb x' y'
      end
  end.

Notation "x <= y" := (leb x y) (at level 70) : nat_scope.

Compute (leb 2 2).

Example test_leb1 : (leb 2 2) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Compute (leb 2 4).

Example test_leb2 : (leb 2 4) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Compute (leb 4 2).

Example test_leb3 : (leb 4 2) = false.
Proof.
  simpl.
  reflexivity.
Qed.

(** Exercise: 1 star, standard (ltb) -  Função 'menor que' *)

Definition ltb (x y : nat) : bool :=
  (andb (leb x y) (negb (eqb x y))).

Notation "x < y" := (ltb x y) (at level 70) : nat_scope.

Compute (ltb 2 2).

Example test_ltb1: (ltb 2 2) = false.
Proof.
  reflexivity.
Qed.

Compute (ltb 2 4).

Example test_ltb2: (ltb 2 4) = true.
Proof.
  reflexivity.
Qed.

Compute (ltb 4 2).

Example test_ltb3: (ltb 4 2) = false.
Proof.
  reflexivity.
Qed.

(** Exemplo rewrite *)

Theorem plus_id_example : forall x y:nat,
  x = y ->
  x + x = y + y.
Proof.
  intros x y H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_id_example' : forall x y:nat,
  x = y ->
  x + x = y + y.
Proof.
  intros x y H.
  rewrite <- H.
  reflexivity.
Qed.

(** Exercise: 1 star, standard (plus_id_exercise) *)

Theorem plus_id_exercise : 
  forall x y z : nat,
  x = y ->
  y = z ->
  x + y = y + z.
Proof.
  intros x y z H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

(** Exercise: 2 stars, standard (mult_S_1) *)

Theorem mult_S_1 : 
  forall x y : nat,
  y = S x ->
  y * (1 + x) = y * y.
Proof.
  intros x y H.
  simpl.
  rewrite <- H.
  reflexivity.
Qed.

(** Dupla Negação *)

Theorem negb_involutive : 
  forall x : bool,
  negb (negb x) = x.
Proof.
  intros x.
  destruct x.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive' : 
  forall x : bool,
  negb (negb x) = x.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive'' : 
  forall x : bool,
  negb (negb x) = x.
Proof.
  intros [].
  { reflexivity. }
  { reflexivity. }
Qed.

(** Comutação *)

Theorem andb_commutative : 
  forall x y, 
  andb x y = andb y x.
Proof.
  intros x y.
  destruct x.
  - destruct y.
    + reflexivity.
    + reflexivity.
  - destruct y.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : 
  forall x y,
  andb x y = andb y x.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative'' : 
  forall x y,
  andb x y = andb y x.
Proof.
  intros x y.
  destruct x.
  {
    destruct y.
    { reflexivity. }
    { reflexivity. }
  }
  {
    destruct y.
    { reflexivity. }
    { reflexivity. }
  }
Qed.

(** Exercise: 2 stars, standard (andb_true_elim2) *)

Theorem andb_true_elim2 : 
  forall x y : bool,
  andb x y = true ->
  y = true.
Proof.
  intros [] [].
  - reflexivity.
  - intro H.
    rewrite <- H.
    reflexivity.
  - reflexivity.
  - intro H.
    rewrite <- H.
    reflexivity.
Qed.

Theorem andb_true_elim2' : 
  forall x y : bool,
  andb x y = true ->
  y = true.
Proof.
  intros x y H.
  destruct x.
  {
    destruct y.
    { reflexivity. }
    { rewrite <- H.
      reflexivity.
    }
  }
  {
    destruct y.
    { reflexivity. }
    {
      rewrite <- H.
      reflexivity.
    }
  }
Qed.

(** Exercise: 1 star (zero_nbeq_plus_1)  *)

Theorem zero_nbeq_plus_1 : 
  forall x : nat,
  (0 = x + 1) = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

Theorem zero_nbeq_plus_1' : 
  forall x : nat,
  (0 = x + 1) = false.
Proof.
  intros x.
  destruct x.
  { reflexivity. }
  { reflexivity. }
Qed.

(** Exercise: 2 stars (boolean_functions)  *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

(** Exercise: 1 star, standard (negation_fn_applied_twice) *)

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  rewrite -> negb_involutive.
  reflexivity.
  Qed.

(** Exercise: 2 stars (andb_eq_orb) *)

Theorem andb_eq_orb :
  forall (x y : bool),
  (andb x y = orb x y) ->
  x = y.
Proof.
  intros x y H.
  destruct x.
  - destruct y.
    + reflexivity.
    +
      compute in H.
      rewrite -> H.
      reflexivity.
  - destruct y.
    +
      compute in H.
      rewrite -> H. 
      reflexivity.
    + reflexivity.
Qed.

(** Exercise: 3 stars, standard (binary) *)

Inductive bin : Type :=
  | Z : bin
  | A : bin -> bin
  | B : bin -> bin.

Fixpoint incr (x : bin) : bin :=
  match x with
  | Z => B Z
  | A x' => B x'
  | B x' => A (incr x')
  end.

Fixpoint bin_to_nat (x : bin) : nat :=
  match x with
  | Z => O
  | A x' => mult 2 (bin_to_nat x')
  | B x' => S (mult 2 (bin_to_nat x'))
  end.

Example inc_three_four: (bin_to_nat (incr (B (B Z)))) = 4.
Proof.
  reflexivity.
Qed.

Example inc_nine_ten: (bin_to_nat (incr (B (A (A (B Z)))))) = 10.
Proof.
  reflexivity.
Qed.

Example zero_is_zero: (bin_to_nat Z) = 0.
Proof.
  reflexivity.
Qed.

Example five_is_five: (bin_to_nat (B (A (B Z)))) = 5.
Proof.
  reflexivity.
Qed.

Fixpoint incN (n:nat) (m:bin)  :=
  match n with
  | 0 => m
  | S n' => incN n' (incr m)
  end.

Compute (incN 15 Z).

Example SanityCheck: bin_to_nat (incN 15 Z) = 15.
Proof.
  reflexivity.
Qed.
