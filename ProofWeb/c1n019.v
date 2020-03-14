Require Import ProofWeb.

Variables R S: D -> Prop.

Hypothesis P1 : all x,R(x) /\ all y,S(y). 

Theorem c1n019 : all z,(R(z) /\ S(z)).
Proof.
all_i a.
con_i.
all_e (all x, R(x)).
con_e1 (all y, S(y)).
exact P1.
all_e (all y, S(y)).
con_e2 (all x, R(x)).
exact P1.
Qed.