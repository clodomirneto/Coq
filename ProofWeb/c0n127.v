Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A \/ B).

Theorem c0n127 : ((A /\ B) <-> (A <-> B)).
Proof.
dis_e (A \/ B) H1 H2.
exact P1.
iff_i H3 H4.
iff_i H5 H6.
con_e2 A.
exact H3.
con_e1 B.
exact H3.
con_i.
exact H1.
iff_e1 A.
exact H4.
exact H1.
iff_i H7 H8.
iff_i H9 H10.
exact H2.
con_e1 B.
exact H7.
con_i.
iff_e2 B.
exact H8.
exact H2.
exact H2.
Qed.