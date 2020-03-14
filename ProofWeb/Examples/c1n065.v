Require Import ProofWeb.

Variables P Q R : D -> Prop.

Hypothesis P1 : all x,(R(x) -> ~Q(x)).
Hypothesis P2 : exi x,(P(x) /\ R(x)). 

Theorem c1n065 : exi x,(P(x) /\ ~Q(x)).
Proof.
exi_e (exi x, (P(x) /\ R(x))) a H1.
exact P2.
exi_i a.
con_i.
con_e1 (R(a)).
exact H1.
imp_e (R(a)).
all_e (all x, (R(x) -> ~Q(x))).
exact P1.
con_e2 (P(a)).
exact H1.
Qed.