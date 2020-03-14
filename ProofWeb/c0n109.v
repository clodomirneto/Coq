Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (~A <-> B).
Hypothesis P2: A.

Theorem c0n109 : ~B.
Proof.
neg_i H1.
neg_e A.
iff_e2 B.
exact P1.
exact H1.
exact P2.
Qed.