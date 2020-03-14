Require Import ProofWeb.

Variable P : D -> Prop.
Variable Q : D*D -> Prop.

Hypothesis P1 : exi y,all x,(P(x) -> Q(x,y)).

Theorem c1n083 : all x,(P(x) -> exi y,Q(x,y)).
Proof.
all_i a.
imp_i H1.
exi_e (exi y, all x, (P(x) -> Q(x,y))) b H2.
exact P1.
exi_i b.
imp_e (P(a)).
all_e (all x, (P(x) -> Q(x, b))).
exact H2.
exact H1.
Qed.