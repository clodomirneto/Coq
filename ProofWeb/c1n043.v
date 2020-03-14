Require Import ProofWeb.

Variable P : D -> Prop.

Hypothesis P1 : exi x,exi y,(P(x) /\ P(y)).

Theorem c1n043 : exi x,P(x).
Proof.
exi_e (exi x, exi y, (P(x) /\ P(y))) a H1.
exact P1.
exi_i a.
exi_e (exi y, (P(a) /\ P(y))) b H2.
exact H1.
con_e1 (P(b)).
exact H2.
Qed.