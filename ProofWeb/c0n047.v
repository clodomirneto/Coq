Require Import ProofWeb.

Parameter A : Prop.

Hypothesis P1: (A -> False ).

Theorem c0n047 : ~A.
Proof.
neg_i H1.
imp_e A.
exact P1.
exact H1.
Qed.