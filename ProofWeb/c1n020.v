Require Import ProofWeb.

Variables R S: D -> Prop.

Hypothesis P1 : all x,(R(x) /\ S(x)). 

Theorem c1n020 : all y,R(y) /\ all z,S(z).
Proof.
con_i.
all_i a.
con_e1 (S(a)).
all_e (all x, (R(x) /\ S(x))).
exact P1.
all_i a.
con_e2 (R(a)).
all_e (all x, (R(x) /\ S(x))).
exact P1.
Qed.