Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n116 : ~(A <-> B) <->  ~(B <-> A).
Proof.
iff_i H1 H2.
neg_i H3.
neg_e (A <-> B).
exact H1.
iff_i H4 H5.
iff_e2 A.
exact H3.
exact H4.
iff_e1 B.
exact H3.
exact H5.
neg_i H6.
neg_e (B <-> A).
exact H2.
iff_i H7 H8.
iff_e2 B.
exact H6.
exact H7.
iff_e1 A.
exact H6.
exact H8.
Qed.