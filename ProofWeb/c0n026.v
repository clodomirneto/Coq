Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A \/ B).

Theorem c0n026 : (B \/ A).
Proof.
dis_e (A \/ B) H1 H2.
exact P1.
dis_i2.
exact H1.
dis_i1.
exact H2.
Qed.