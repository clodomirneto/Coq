Require Import ProofWeb.

Variable P: D -> Prop.

Hypothesis P1 : exi x,P(x).

Theorem c1n034 : exi y,P(y).
Proof.
exi_e (exi x, P(x)) a H1.
exact P1.
exi_i a.
exact H1.
Qed.