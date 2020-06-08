Require Import ProofWeb.

Variable R : D*D -> Prop.

Hypothesis P1 : all x,all y,R(x,y).

Theorem c1n051 : all y,all x,R(x,y).
Proof.
all_i a.
all_i b.
all_e (all y, R(b,y)).
all_e (all x, all y, (R(x,y))).
exact P1.
Qed.