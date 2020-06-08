Require Import ProofWeb.

Variables R S: D -> Prop.

Hypothesis P1 : all x,(R(x)->S(x)).

Theorem c1n023 : exi y,R(y)->exi z,S(z).
Proof.
imp_i H1.
exi_e (exi y, R(y)) a H2.
exact H1.
exi_i a.
imp_e (R(a)).
all_e (all x, (R(x) -> S(x))).
exact P1.
exact H2.
Qed.