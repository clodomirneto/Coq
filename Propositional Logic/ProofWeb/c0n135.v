Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n135 : ((A \/ B) <-> (B <-> (A -> B))).
Proof.
iff_i H1 H2.
iff_i H3 H4.
dis_e (A \/ B) H5 H6.
exact H1.
imp_i H7.
exact H3.
imp_i H8.
exact H3.
dis_e (A \/ B) H9 H10.
exact H1.
imp_e A.
exact H4.
exact H9.
exact H10.
PBC H11.
neg_e (A \/ B).
exact H11.
dis_i2.
PBC H12.
neg_e (A -> B).
neg_i H13.
neg_e (B).
exact H12.
iff_e2 (A -> B).
exact H2.
exact H13.
imp_i H14.
PBC H15.
neg_e (B).
exact H15.
PBC H16.
neg_e (A \/ B).
exact H11.
dis_i1.
exact H14.
Qed.