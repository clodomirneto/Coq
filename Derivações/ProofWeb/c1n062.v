Require Import ProofWeb.

Variables P Q R : D -> Prop.

Hypothesis P1 : all x,(R(x) -> Q(x)).
Hypothesis P2 : all x,(P(x) -> R(x)). 

Theorem c1n062 : all x,(P(x) -> Q(x)).
Proof.
all_i a.
imp_i H1.
imp_e (R(a)).
all_e (all x, (R(x) -> Q(x))).
exact P1.
imp_e (P(a)).
all_e (all x, (P(x) -> R(x))).
exact P2.
exact H1.
Qed.