Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: ~(A \/ ~B).

Theorem c0n082 : B.
Proof.
PBC H1.
neg_e (A \/ ~B).
exact P1.
dis_i2.
exact H1.
Qed.