Require Import ProofWeb.

Variables P Q R : D -> Prop.

Hypothesis P1 : exi x,(Q(x) /\ R(x)).
Hypothesis P2 : all x,(R(x) -> P(x)).

Theorem c1n078 : exi x,(P(x) /\ Q(x)).
Proof.
exi_e (exi x, (Q(x) /\ R(x))) a H1.
exact P1.
exi_i a.
con_i.
imp_e (R(a)).
all_e (all x, (R(x) -> P(x))).
exact P2.
con_e2 (Q(a)).
exact H1.
con_e1 (R(a)).
exact H1.
Qed.