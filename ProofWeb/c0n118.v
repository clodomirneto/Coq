Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n118 : ~(A <-> B) <-> (A <-> ~B).
Proof.
iff_i H1 H2.
iff_i H3 H4.
neg_i H5.
neg_e (A <-> B).
exact H1.
iff_i H6 H7.
exact H5.
exact H3.
PBC H8.
neg_e (A <-> B).
exact H1.
iff_i H9 H10.
PBC H11.
neg_e A.
exact H8.
exact H9.
PBC H12.
neg_e B.
exact H4.
exact H10.
neg_i H13.
neg_e B.
neg_i H14.
neg_e A.
neg_i H15.
neg_e (A <-> ~B).
neg_i H16.
neg_e B.
iff_e1 A.
exact H2.
exact H15.
exact H14.
exact H2.
iff_e2 B.
exact H13.
exact H14.
PBC H17.
neg_e A.
neg_i H18.
neg_e B.
exact H17.
iff_e1 A.
exact H13.
exact H18.
PBC H19.
neg_e A.
exact H19.
iff_e2 (~B).
exact H2.
exact H17.
Qed.