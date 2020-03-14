Require Import ProofWeb.

Variables P : D -> Prop.

Hypothesis P1 : exi x,all y,(P(y)->P(x)).

Theorem c1n046 : exi x,(exi y,P(y)->P(x)).
Proof.
exi_e (exi x, all y, (P(y) -> P(x))) a H1.
exact P1.
exi_i a.
all_i b.
exi_e (exi y, P(y)) c H2.
exact b.
imp_e (P(c)).
all_e (all y, (P(y) -> P(a))).
exact H1.
exact H2.
Qed.