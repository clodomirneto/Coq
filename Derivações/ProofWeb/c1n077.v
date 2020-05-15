Require Import ProofWeb.

Variables P Q R : D -> Prop.

Hypothesis P1 : all x,(Q(x) -> R(x)).
Hypothesis P2 : all x,(R(x) -> ~P(x)).

Theorem c1n077 : all x,(P(x) -> ~Q(x)).
Proof.
all_i a.
imp_i H1.
neg_i H2.
neg_e (P(a)).
imp_e (R(a)).
all_e (all x, (R(x) -> ~P(x))).
exact P2.
imp_e (Q(a)).
all_e (all x, (Q(x) -> R(x))).
exact P1.
exact H2.
exact H1.
Qed.