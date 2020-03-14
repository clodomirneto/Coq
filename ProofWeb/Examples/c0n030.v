Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: ((B \/ (A \/ C)) \/ A).

Theorem c0n030 : (C \/ (A \/ B)).
Proof.
dis_e ((B \/ (A \/ C)) \/ A) H1 H2.
exact P1.
dis_e (B \/ (A \/ C)) H3 H4.
exact H1.
dis_i2.
dis_i2.
exact H3.
dis_e (A \/ C) H5 H6.
exact H4.
dis_i2.
dis_i1.
exact H5.
dis_i1.
exact H6.
dis_i2.
dis_i1.
exact H2.
Qed.