Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n134 : ((A \/ B) <-> (A <-> (B -> A))).
Proof.
iff_i H1 H2.
dis_e (A \/ B) H3 H4.
exact H1.
iff_i H5 H6.
imp_i H7.
exact H3.
exact H3.
iff_i H9 H10.
imp_i H11.
exact H9.
imp_e (B).
exact H10.
exact H4.
PBC H12.
neg_e (A \/ B).
exact H12.
dis_i1.
PBC H13.
neg_e (B -> A).
neg_i H14.
neg_e (A).
exact H13.
iff_e2 (B -> A).
exact H2.
exact H14.
imp_i H15.
PBC H16.
neg_e (A).
exact H16.
PBC H17.
neg_e (A \/ B).
exact H12.
dis_i2.
exact H15.
Qed.