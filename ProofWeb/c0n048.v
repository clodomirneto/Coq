Require Import ProofWeb.

Parameter A : Prop.

Hypothesis P1: A.

Theorem c0n048 : ~~A.
Proof.
neg_i H1.
neg_e A.
exact H1.
exact P1.
Qed.