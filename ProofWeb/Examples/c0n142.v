Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A <-> B).

Theorem c0n142 : ((A \/ C) <-> (B \/ C)).
Proof.
iff_i H1 H2.
dis_e (A \/ C) H3 H4.
exact H1.
dis_i1.
iff_e1 A.
exact P1.
exact H3.
dis_i2.
exact H4.
dis_e (B \/ C) H5 H6.
exact H2.
dis_i1.
iff_e2 B.
exact P1.
exact H5.
dis_i2.
exact H6.
Qed.