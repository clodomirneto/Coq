Require Import ProofWeb.

Variables P Q: Prop.
Variable R: D -> Prop.

Hypothesis P1 : all x,R(x). 

Theorem c1n022 : all y,(P \/ R(y) \/ Q).
Proof.
all_i a.
dis_i2.
dis_i1.
all_e (all x, R(x)).
exact P1.
Qed.