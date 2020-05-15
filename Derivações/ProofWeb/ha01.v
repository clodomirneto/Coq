Require Import ProofWeb.

Parameter P: Prop.

Hypothesis P1: ~P -> P.

Theorem a01: P.

Proof.
PBC H1.
neg_e P.
exact H1.
imp_e (~P).
exact P1.
exact H1.
Qed.