Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: ~A.
Hypothesis P2: B.

Theorem c0n106 : ~(A <-> B).
Proof.
neg_i H1.
neg_e A.
exact P1.
iff_e2 B.
exact H1.
exact P2.
Qed.