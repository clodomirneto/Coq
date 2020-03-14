Require Import ProofWeb.

Variables P Q R : D -> Prop.

Hypothesis P1 : all x,(R(x) -> ~Q(x)).
Hypothesis P2 : all x,(R(x) -> P(x)) .
Hypothesis P3 : exi x,R(x).

Theorem c1n073 : exi x,(P(x) /\ ~Q(x)).
Proof.
exi_e (exi x, R(x)) a H1.
exact P3.
exi_i a.
con_i.
imp_e (R(a)).
all_e (all x, (R(x) -> P(x))).
exact P2.
exact H1.
imp_e (R(a)).
all_e (all x, (R(x) -> ~Q(x))).
exact P1.
exact H1.
Qed.