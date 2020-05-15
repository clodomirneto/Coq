Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A <-> (B <-> C)).

Theorem c0n149 : ((A <-> B) <-> C).
Proof.
iff_i H1 H2.
PBC H3.
neg_e B.
neg_i H4.
neg_e A.
neg_i H5.
neg_e B.
neg_i H6.
neg_e C.
exact H3.
iff_e1 B.
iff_e1 A.
exact P1.
exact H5.
exact H6.
exact H4.
iff_e2 B.
exact H1.
exact H4.
PBC H7.
neg_e B.
exact H7.
iff_e1 A.
exact H1.
PBC H8.
neg_e A.
exact H8.
iff_e2 (B <-> C).
exact P1.
iff_i H9 H10.
PBC H11.
neg_e B.
exact H7.
exact H9.
PBC H12.
neg_e C.
exact H3.
exact H10.
iff_i H13 H14.
iff_e2 C.
iff_e1 A.
exact P1.
exact H13.
exact H2.
iff_e2 (B <-> C).
exact P1.
iff_i H15 H16.
exact H2.
exact H14.
Qed.