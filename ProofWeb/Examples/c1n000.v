Require Import ProofWeb.

Variable P: Prop.
Variable R: D -> Prop.

Hypothesis P1 : (all x,R(x)) /\ P.

Theorem c1n000 : all x,(R(x) /\ P).
Proof.
all_i a.
con_i.
all_e (all x, R(x)).
con_e1 P.
exact P1.
con_e2 (all x, R(x)).
exact P1.
Qed.