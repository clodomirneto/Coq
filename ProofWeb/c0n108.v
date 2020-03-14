Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A <-> B).
Hypothesis P2: ~B.

Theorem c0n108 : ~A.
Proof.
neg_i H1.
neg_e B.
exact P2.
iff_e1 A.
exact P1.
exact H1.
Qed.