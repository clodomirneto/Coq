Require Import ProofWeb.

Variable P: D -> Prop.

Hypothesis P1 : exi x,exi x,P(x).

Theorem c1n035 : exi x,P(x).
Proof.
exi_e (exi x, exi x, P(x)) a H1.
exact P1.
exact H1.
Qed.