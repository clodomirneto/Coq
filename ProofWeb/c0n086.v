Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A -> ~B).

Theorem c0n086 : ~(A /\ B).
Proof.
neg_i H1.
neg_e B.
imp_e A.
exact P1.
con_e1 B.
exact H1.
con_e2 A.
exact H1.
Qed.