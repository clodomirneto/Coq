Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A <-> B).
Hypothesis P2: (B <-> C).

Theorem c0n102 : (A <-> C).
Proof.
iff_i H1 H2.
iff_e1 B.
exact P2.
iff_e1 A.
exact P1.
exact H1.
iff_e2 B.
exact P1.
iff_e2 C.
exact P2.
exact H2.
Qed.