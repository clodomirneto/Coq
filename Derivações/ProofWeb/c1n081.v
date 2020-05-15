Require Import ProofWeb.

Variable P : D -> Prop.
Variable Q : D*D -> Prop.

Hypothesis P1 : exi x,exi y,(P(x) /\ Q(x,y)).

Theorem c1n081 : exi x,(P(x) /\ exi y,Q(x,y)).
Proof.
exi_e (exi x, exi y, (P(x) /\ Q(x,y))) a H1.
exact P1.
exi_i a.
exi_e (exi y, (P(a) /\ Q(a,y))) b H2.
exact H1.
con_i.
con_e1 (Q(a, b)).
exact H2.
exi_i b.
con_e2 (P(a)).
exact H2.
Qed.