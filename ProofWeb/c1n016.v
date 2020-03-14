Require Import ProofWeb.

Variables R S T: D -> Prop.

Hypothesis P1 : all x,(R(x)->S(x)). 
Hypothesis P2 : all y,(S(y)->T(y)). 

Theorem c1n016 : all z,(R(z)->T(z)).
Proof.
all_i a.
imp_i H1.
imp_e (S(a)).
all_e (all y, (S(y) -> T(y))).
exact P2.
imp_e (R(a)).
all_e (all x, (R(x) -> S(x))).
exact P1.
exact H1.
Qed.