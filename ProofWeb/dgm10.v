Require Import ProofWeb.

Parameter A B: Prop.

Hypothesis P1: ~(A \/ B).

Theorem dgm10: ~A.

Proof.
neg_i H1.
neg_e (A \/ B).
exact P1.
dis_i1.
exact H1.
Qed.
