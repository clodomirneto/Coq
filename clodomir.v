(* Booleano *)

Inductive bool : Type :=
  | true
  | false.

Check bool.

(* Negação *)

Definition negb (x: bool) : bool :=
  match x with
  | true => false
  | false => true
  end.

Example test_negb1 : (negb true) = false.
Proof.
reflexivity.
Qed.

Example test_negb2 : (negb false) = true.
Proof.
reflexivity.
Qed.

(* Conjunção *)

Definition andb (x y: bool) : bool :=
  match (x, y) with
  | (true, true) => true
  | _ => false
  end.

Notation "x && y" := (andb x y).

Example test_andb1 : (andb true true) = true.
Proof.
reflexivity.
Qed.

Example test_andb2 : (andb true false) = false.
Proof.
reflexivity.
Qed.

Example test_andb3 : (andb false true) = false.
Proof.
reflexivity.
Qed.

Example test_andb4 : (andb false false) = false.
Proof.
reflexivity.
Qed.

(* Disjunção *)

Definition orb (x y: bool) : bool :=
  match (x, y) with
  | (false, false) => false
  | _ => true
  end.

Notation "x || y" := (orb x y).

Example test_orb1 : (orb true true) = true.
Proof.
reflexivity.
Qed.

Example test_orb2 : (orb true false) = true.
Proof.
reflexivity.
Qed.

Example test_orb3 : (orb false true) = true.
Proof.
reflexivity.
Qed.

Example test_orb4 : (orb false false) = false.
Proof.
reflexivity.
Qed.

(* Implicação *)

Definition implb (x y: bool) : bool :=
  match (x, y) with
  | (true, false) => false
  | _ => true
  end.

Example test_implb1 : (implb true true) = true.
Proof.
reflexivity.
Qed.

Example test_implb2 : (implb true false) = false.
Proof.
reflexivity.
Qed.

Example test_implb3 : (implb false true) = true.
Proof.
reflexivity.
Qed.

Example test_implb4 : (implb false false) = true.
Proof.
reflexivity.
Qed.

(* Bi-implicação *)

Definition biimplb (x y: bool) : bool :=
  match (x, y) with
  | (true, true) => true
  | (false, false) => true
  | _ => false
  end.

Example test_biimplb1 : (biimplb true true) = true.
Proof.
reflexivity.
Qed.

Example test_biimplb2 : (biimplb true false) = false.
Proof.
reflexivity.
Qed.

Example test_biimplb3 : (biimplb false true) = false.
Proof.
reflexivity.
Qed.

Example test_biimplb4 : (biimplb false false) = true.
Proof.
reflexivity.
Qed.

(* Exercise: 1 star, standard (nandb) *)

Definition nandb (x y: bool) : bool :=
  match (x, y) with
  | (true, true) => false
  | _ => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof.
reflexivity.
Qed.

Example test_nandb2: (nandb false false) = true.
Proof.
reflexivity.
Qed.

Example test_nandb3: (nandb false true) = true.
Proof.
reflexivity.
Qed.

Example test_nandb4: (nandb true true) = false.
Proof.
reflexivity.
Qed.

(* Exercise: 1 star, standard (andb3) *)

Definition andb3 (x y z: bool) : bool :=
  match (x, y, z) with
  | (true, true, true) => true
  | _ => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof.
reflexivity.
Qed.

Example test_andb32: (andb3 false true true) = false.
Proof.
reflexivity.
Qed.

Example test_andb33: (andb3 true false true) = false.
Proof.
reflexivity.
Qed.

Example test_andb34: (andb3 true true false) = false.
Proof.
reflexivity.
Qed.

(* Número *)

Inductive nat : Type :=
  | O
  | S (x : nat).

Check nat.

(* Par *)

Fixpoint evenb (x: nat) : bool :=
  match x with
  | O => true
  | S O => false
  | S (S x') => evenb x'
  end.

Example test_evenb1 : evenb 3 = true.
Proof.
reflexivity.
Qed.

Example test_evenb2 : (evenb 13) = false.
Proof.
reflexivity.
Qed.

Example test_evenb3 : (evenb 24) = false.
Proof.
reflexivity.
Qed.

(* Ímpar *)

Fixpoint oddb (x: nat) : bool :=
  match x with
  | O => false
  | S O => true
  | S (S x') => oddb x'
  end.

Example test_oddb1 : (oddb 4) = true.
Proof.
reflexivity.
Qed.

Example test_oddb2 : (oddb 13) = false.
Proof.
reflexivity.
Qed.

Example test_oddb3 : (oddb 24) = false.
Proof.
reflexivity.
Qed.

(* Exercise: 1 star, standard (factorial) *)

Fixpoint factorial (n: nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof.
reflexivity.
Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof.
reflexivity.
Qed.
