Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: ~(A -> B).

Theorem c0n088 : A.
Proof.
PBC H1.
neg_e (A -> B).
exact P1.
imp_i H2.
PBC H3.
neg_e A.
exact H1.
exact H2.
Qed.