Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A <-> B).

Theorem c0n141 : ((A /\ C) <-> (B /\ C)).
Proof.
iff_i H1 H2.
con_i.
iff_e1 A.
exact P1.
con_e1 C.
exact H1.
con_e2 A.
exact H1.
con_i.
iff_e2 B.
exact P1.
con_e1 C.
exact H2.
con_e2 B.
exact H2.
Qed.