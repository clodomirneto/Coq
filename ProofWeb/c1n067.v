Require Import ProofWeb.

Variables P Q R : D -> Prop.

Hypothesis P1 : all x,(Q(x) -> R(x)).
Hypothesis P2 : all x,(P(x) -> ~R(x)). 

Theorem c1n067 : all x,(P(x) -> ~Q(x)).
Proof.
all_i a.
imp_i H1.
neg_i H2.
neg_e (R(a)).
imp_e (P(a)).
all_e (all x, (P(x) -> ~R(x))).
exact P2.
exact H1.
imp_e (Q(a)).
all_e (all x, (Q(x) -> R(x))).
exact P1.
exact H2.
Qed.