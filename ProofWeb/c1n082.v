Require Import ProofWeb.

Variable P : D -> Prop.
Variable Q : D*D -> Prop.

Hypothesis P1 : exi x,(P(x) /\ exi y,Q(x,y)).

Theorem c1n082 : exi x,exi y,(P(x) /\ Q(x,y)).
Proof.
exi_e (exi x, (P(x) /\ exi y, (Q(x,y)))) a H1.
exact P1.
exi_i a.
exi_e (exi y, Q(a, y)) b H2.
con_e2 (P(a)).
exact H1.
exi_i b.
con_i.
con_e1 (exi y, (Q(a, y))).
exact H1.
exact H2.
Qed.