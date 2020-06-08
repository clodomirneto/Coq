Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A -> B).

Theorem c0n085 : ~(A /\ ~B).
Proof.
neg_i H1.
neg_e B.
con_e2 A.
exact H1.
imp_e A.
exact P1.
con_e1 (~B).
exact H1.
Qed.