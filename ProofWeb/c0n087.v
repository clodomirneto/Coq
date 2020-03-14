Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: A.
Hypothesis P2: ~B.

Theorem c0n087 : ~(A -> B).
Proof.
neg_i H1.
neg_e B.
exact P2.
imp_e A.
exact H1.
exact P1.
Qed.