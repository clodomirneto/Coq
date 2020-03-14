Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A <-> (B <-> C)).

Theorem c0n147 : ((C <-> A) <-> B).
Proof.
iff_i H1 H2.
PBC H3.
neg_e B.
exact H3.
iff_e2 C.
iff_e1 A.
exact P1.
iff_e1 C.
exact H1.
PBC H4.
neg_e C.
exact H4.
iff_e2 A.
exact H1.
PBC H5.
neg_e A.
exact H5.
iff_e2 (B <-> C).
exact P1.
iff_i H6 H7.
PBC H8.
neg_e B.
exact H3.
exact H6.
PBC H9.
neg_e C.
exact H4.
exact H7.
PBC H10.
neg_e C.
exact H10.
iff_e2 A.
exact H1.
PBC H11.
neg_e A.
exact H11.
iff_e2 (B <-> C).
exact P1.
iff_i H12 H13.
PBC H14.
neg_e B.
exact H3.
exact H12.
PBC H15.
neg_e C.
exact H10.
exact H13.
iff_i H16 H17.
iff_e2 (B <-> C).
exact P1.
iff_i H18 H19.
exact H16.
exact H2.
iff_e1 B.
iff_e1 A.
exact P1.
exact H17.
exact H2.
Qed.