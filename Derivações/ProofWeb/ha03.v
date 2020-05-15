Require Import ProofWeb.

Parameter P Q: Prop.

Hypothesis P1: P /\ Q.

Theorem a03: P -> Q.

Proof.
imp_i H1.
con_e2 P.
exact P1.
Qed.