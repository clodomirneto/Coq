Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: A.
Hypothesis P2: B.

Theorem c0n103 : (A <-> B).
Proof.
iff_i H1 H2.
exact P2.
exact P1.
Qed.