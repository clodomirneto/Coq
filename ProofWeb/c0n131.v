Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n131 : ((A <-> B) <-> ((A \/ B) -> (A /\ B))).
Proof.
iff_i H1 H2.
imp_i H3.
con_i.
dis_e (A \/ B) H4 H5.
exact H3.
exact H4.
iff_e2 B.
exact H1.
exact H5.
dis_e (A \/ B) H6 H7.
exact H3.
iff_e1 A.
exact H1.
exact H6.
exact H7.
iff_i H8 H9.
con_e2 A.
imp_e (A \/ B).
exact H2.
dis_i1.
exact H8.
con_e1 B.
imp_e (A \/ B).
exact H2.
dis_i2.
exact H9.
Qed.