Require Import ProofWeb.

Variable P : D -> Prop.

Hypothesis P1 : all x,all y,(P(y)->P(x)) .

Theorem c1n048 : all x,(exi y,P(y)->P(x)).
Proof.
all_i a.
all_i b.
imp_e (P(a)).
all_e (all y, (P(y) -> P(a))).
all_e (all x, all y, (P(y) -> P(x))).
exact P1.
exi_e (exi y, (P(y))) c H1.
exact b.
imp_e (P(c)).
all_e (all y, (P(y) -> P(a))).
all_e (all x, all y, (P(y) -> P(x))).
exact P1.
exact H1.
Qed.