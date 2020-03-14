Require Import ProofWeb.

Variables R S: D -> Prop.

Hypothesis P1 : all x,(R(x)->S(x)). 

Theorem c1n015 : all y,R(y)->all z,S(z).
Proof.
imp_i H1.
all_i a.
imp_e (R(a)).
all_e (all x, (R(x) -> S(x))).
exact P1.
all_e (all y, R(y)).
exact H1.
Qed.