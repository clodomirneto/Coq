Require Import ProofWeb.

Variable P : D -> Prop.

Hypothesis P1 : exi x,P(x).

Theorem c1n040 : exi x,exi y,(P(x) /\ P(y)).
Proof.
exi_e (exi x, P(x)) a H1.
exact P1.
exi_i a.
exi_i a.
con_i.
exact H1.
exact H1.
Qed.