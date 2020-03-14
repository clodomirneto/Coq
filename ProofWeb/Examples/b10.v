Require Import ProofWeb.

Parameter C D : Prop.

Hypothesis P1 : (C -> D) -> C.

Theorem b10 : (C -> D) -> D.

Proof.
imp_i H1.
imp_e (C).
exact H1.
imp_e (C -> D).
exact P1.
exact H1.
Qed.
