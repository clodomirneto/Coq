Require Import ProofWeb.

Parameter A B: Prop.

Hypothesis P1: ~(A /\ B).

Hypothesis P2: A.

Theorem dgm09: ~B.

Proof.
neg_i H1.
neg_e (A /\ B).
exact P1.
con_i.
exact P2.
exact H1.
Qed.
