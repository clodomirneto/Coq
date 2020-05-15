Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: ~A.
Hypothesis P2: ~B.

Theorem c0n104 : (A <-> B).
Proof.
iff_i H1 H2.
PBC H3.
neg_e A.
exact P1.
exact H1.
PBC H4.
neg_e B.
exact P2.
exact H2.
Qed.