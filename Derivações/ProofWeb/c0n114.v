Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: ~(A <-> B).
Hypothesis P2: ~B.

Theorem c0n114 : A.
Proof.
PBC H1.
neg_e B.
exact P2.
PBC H2.
neg_e (A <-> B).
exact P1.
iff_i H3 H4.
PBC H5.
neg_e A.
exact H1.
exact H3.
PBC H6.
neg_e B.
exact H2.
exact H4.
Qed.