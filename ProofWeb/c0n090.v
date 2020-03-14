Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: ~(A -> ~B).

Theorem c0n090 : B.
Proof.
PBC H1.
neg_e (A -> ~B).
exact P1.
imp_i H2.
exact H1.
Qed.