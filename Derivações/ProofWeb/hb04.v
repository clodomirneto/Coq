Require Import ProofWeb.

Parameter P : Prop.

Hypothesis P1 : P.

Theorem b04 : P /\ P.

Proof.
con_i.
exact P1.
exact P1.
Qed.
