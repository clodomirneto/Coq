Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: ~(A /\ B /\ C).
Hypothesis P2: B.

Theorem c0n068 : ~(A /\ C).
Proof.
neg_i H1.
neg_e (A /\ B /\ C).
exact P1.
con_i.
con_e1 C.
exact H1.
con_i.
exact P2.
con_e2 A.
exact H1.
Qed.