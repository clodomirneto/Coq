Require Import ProofWeb.

Variable P: Prop.
Variable R: D -> Prop.

Hypothesis P1 : (all x,R(x)) \/ P.

Theorem c1n011 : all x,(R(x) \/ P).
Proof.
dis_e ((all x, R(x)) \/ P) H1 H2.
exact P1.
all_i a.
dis_i1.
all_e (all x, R(x)).
exact H1.
all_i a.
dis_i2.
exact H2.
Qed.