Require Import ProofWeb.

Variable R : D*D -> Prop.

Hypothesis P1 : all x,all y,R(x,y).

Theorem c1n049 : all z,R(z,z).
Proof.
all_i a.
all_e (all y, R(a, y)).
all_e (all x, all y, R(x, y)).
exact P1.
Qed.