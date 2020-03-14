Require Import ProofWeb.

Variables R S: D -> Prop.

Hypothesis P1 : all x,(R(x) <-> S(x)). 

Theorem c1n028 : exi y,R(y) <-> exi z,S(z).
Proof.
iff_i H1 H2.
exi_e (exi y, R(y)) a H3.
exact H1.
exi_i a.
iff_e1 (R(a)).
all_e (all x, (R(x) <-> S(x))).
exact P1.
exact H3.
exi_e (exi z, S(z)) a H4.
exact H2.
exi_i a.
iff_e2 (S(a)).
all_e (all x, (R(x) <-> S(x))).
exact P1.
exact H4.
Qed.