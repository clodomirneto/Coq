Require Import ProofWeb.

Parameter P Q: Prop.

Hypothesis P1: ~P.

Theorem a02: P -> Q.

Proof.
imp_i H1.
PBC H2.
neg_e P.
exact P1.
exact H1.
Qed.