Require Import ProofWeb.

Variable P: Prop.
Variable R: D -> Prop.
Variable i: D.

Hypothesis P1 : all x,(R(x)->P).

Theorem c1n003 : (all x,R(x))->P.
Proof.
imp_i H1.
imp_e (R(i)).
all_e (all x, (R(x) -> P)).
exact P1.
all_e (all x, R(x)).
exact H1.
Qed.