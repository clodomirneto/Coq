Require Import ProofWeb.

Variables R S: D -> Prop.

Hypothesis P1 : all x,R(x) \/ all y,S(y). 

Theorem c1n021 : all z,(R(z) \/ S(z)).
Proof.
all_i a.
dis_e (all x, R(x) \/ all y, S(y)) H1 H2.
exact P1.
dis_i1.
all_e (all x, R(x)).
exact H1.
dis_i2.
all_e (all y, S(y)).
exact H2.
Qed.