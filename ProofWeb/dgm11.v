Require Import ProofWeb.

Parameter A B: Prop.

Hypothesis P1: ~A.

Theorem dgm11: A -> B.

Proof.
imp_i H1.
PBC H2.
neg_e (A).
exact P1.
exact H1.
Qed.
