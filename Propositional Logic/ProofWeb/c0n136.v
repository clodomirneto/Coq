Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n136 : ((A \/ B) <-> ((A <-> B) -> A)).
Proof.
iff_i H1 H2.
imp_i H3.
dis_e (A \/ B) H4 H5.
exact H1.
exact H4.
iff_e2 B.
exact H3.
exact H5.
PBC H6.
neg_e (A \/ B).
exact H6.
dis_i1.
PBC H7.
neg_e (A).
exact H7.
imp_e (A <-> B).
exact H2.
iff_i H8 H9.
PBC H10.
neg_e (A).
exact H7.
exact H8.
PBC H11.
neg_e (A \/ B).
exact H6.
dis_i2.
exact H9.
Qed.