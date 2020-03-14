Require Import ProofWeb.

Parameter A : Prop.

Hypothesis P1: ~A.

Theorem c0n046 : (A -> False ).
Proof.
imp_i H1.
neg_e A.
exact P1.
exact H1.
Qed.