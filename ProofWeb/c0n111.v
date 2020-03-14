Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: ~(A <->  B).
Hypothesis P2: A.

Theorem c0n111 : ~B.
Proof.
neg_i H1.
neg_e (A <-> B).
exact P1.
iff_i H2 H3.
exact H1.
exact P2.
Qed.