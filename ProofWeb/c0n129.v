Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n129 : ((A -> B) <-> (B <-> (A \/ B))).
Proof.
iff_i H1 H2.
iff_i H3 H4.
dis_i2.
exact H3.
dis_e (A \/ B) H5 H6.
exact H4.
imp_e A.
exact H1.
exact H5.
exact H6.
imp_i H7.
iff_e2 (A \/ B).
exact H2.
dis_i1.
exact H7.
Qed.