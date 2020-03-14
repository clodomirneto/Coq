Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A <-> B).

Theorem c0n101 : (B <->  A).
Proof.
iff_i H1 H2.
iff_e2 B.
exact P1.
exact H1.
iff_e1 A.
exact P1.
exact H2.
Qed.