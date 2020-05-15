Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A -> B).
Hypothesis P2: (A -> ~B).

Theorem c0n053 : ~A.
Proof.
neg_i H1.
neg_e B.
imp_e A.
exact P2.
exact H1.
imp_e A.
exact P1.
exact H1.
Qed.