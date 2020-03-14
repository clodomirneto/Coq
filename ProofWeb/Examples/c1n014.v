Require Import ProofWeb.

Variables R S: D -> Prop.
Variable i : D.

Hypothesis P1 : R(i). 
Hypothesis P2 : all x,(R(x)->S(x)).

Theorem c1n014 : S(i).
Proof.
imp_e (R(i)).
all_e (all x, (R(x) -> S(x))).
exact P2.
exact P1.
Qed.