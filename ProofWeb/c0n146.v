Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n146 : (((A <-> B) <-> B) <-> A).
Proof.
iff_i H1 H2.
PBC H3.
neg_e B.
neg_i H4.
neg_e ((A <-> B) <-> B).
neg_i H5.
neg_e A.
exact H3.
iff_e2 B.
iff_e2 B.
exact H1.
exact H4.
exact H4.
exact H1.
iff_e1 (A <-> B).
exact H1.
iff_i H6 H7.
PBC H8.
neg_e A.
exact H3.
exact H6.
PBC H9.
neg_e B.
neg_i H10.
neg_e ((A <-> B) <-> B).
neg_i H11.
neg_e A.
exact H9.
iff_e2 B.
iff_e2 B.
exact H1.
exact H7.
exact H7.
exact H1.
exact H7.
iff_i H12 H13.
iff_e1 A.
exact H12.
exact H2.
iff_i H14 H15.
exact H13.
exact H2.
Qed.