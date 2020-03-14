Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n117 : ~(A <-> B) <->  (~A <-> B).
Proof.
iff_i H1 H2.
iff_i H3 H4.
PBC H5.
neg_e (A <-> B).
exact H1.
iff_i H6 H7.
PBC H8.
neg_e (A).
exact H3.
exact H6.
PBC H9.
neg_e B.
exact H5.
exact H7.
neg_i H10.
neg_e (A <-> B).
exact H1.
iff_i H11 H12.
exact H4.
exact H10.
neg_i H13.
neg_e A.
neg_i H14.
neg_e A.
iff_e2 B.
exact H2.
iff_e1 A.
exact H13.
exact H14.
exact H14.
iff_e2 B.
exact H13.
iff_e1 (~A).
exact H2.
neg_i H15.
neg_e A.
iff_e2 B.
exact H2.
iff_e1 A.
exact H13.
exact H15.
exact H15.
Qed.