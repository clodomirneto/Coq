Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: B.

Theorem c0n078 : ~(A /\ ~B).
Proof.
neg_i H1.
neg_e B.
con_e2 A.
exact H1.
exact P1.
Qed.