Require Import ProofWeb.

Variables P Q R : D -> Prop.

Hypothesis P1 : all x,(Q(x) -> ~R(x)).
Hypothesis P2 : exi x,(R(x) /\ P(x)).

Theorem c1n080 : exi x,(P(x) /\ ~Q(x)).
Proof.
exi_e (exi x, (R(x) /\ P(x))) a H1.
exact P2.
exi_i a.
con_i.
con_e2 (R(a)).
exact H1.
neg_i H2.
neg_e (R(a)).
imp_e (Q(a)).
all_e (all x, (Q(x) -> ~R(x))).
exact P1.
exact H2.
con_e1 (P(a)).
exact H1.
Qed.