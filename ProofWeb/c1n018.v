Require Import ProofWeb.

Variables P Q: D -> Prop.

Hypothesis P1 : exi x,(P(x) /\ Q(x)). 

Theorem c1n018 : exi y,(Q(y) /\ P(y)).
Proof.
exi_e (exi x, (P(x) /\ Q(x))) i H1.
exact P1.
exi_i i.
con_i.
con_e2 (P(i)).
exact H1.
con_e1 (Q(i)).
exact H1.
Qed.