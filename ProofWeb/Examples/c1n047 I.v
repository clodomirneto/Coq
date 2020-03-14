Require Import ProofWeb.

Variable P : D -> Prop.

Hypothesis P1 : exi x,exi y,(P(x) \/ P(y)).
 
Theorem c1n044 : exi x,P(x).
Proof.
exi_e (exi x, exi y, (P(x) \/ P(y))) a H1.
exact P1.
exi_e (exi y, (P(a) \/ P(y))) b H2.
exact H1.
dis_e (P(a) \/ P(b)) H3 H4.
exact H2.
exi_i a.
exact H3.
exi_i b.
exact H4.
Qed.