Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: A.
Hypothesis P2: ~B.

Theorem c0n105 : ~(A <-> B).
Proof.
neg_i H1.
neg_e B.
exact P2.
iff_e1 A.
exact H1.
exact P1.
Qed.