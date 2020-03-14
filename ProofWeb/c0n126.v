Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A /\ B).

Theorem c0n126 : ((A \/ B) <-> (A <-> B)).
Proof.
iff_i H1 H2.
iff_i H3 H4.
con_e2 A.
exact P1.
con_e1 B.
exact P1.
dis_i1.
con_e1 B.
exact P1.
Qed.