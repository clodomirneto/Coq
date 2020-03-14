Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A <-> (B <-> C)).

Theorem c0n148 : (B <-> (C <-> A)).
Proof.
iff_i H1 H2.
iff_i H3 H4.
iff_e2 (B <-> C).
exact P1.
iff_i H5 H6.
exact H3.
exact H1.
iff_e1 B.
iff_e1 A.
exact P1.
exact H4.
exact H1.
PBC H7.
neg_e B.
exact H7.
iff_e2 C.
iff_e1 A.
exact P1.
iff_e1 C.
exact H2.
PBC H8.
neg_e C.
exact H8.
iff_e2 A.
exact H2.
PBC H9.
neg_e A.
exact H9.
iff_e2 (B <-> C).
exact P1.
iff_i H10 H11.
PBC H12.
neg_e B.
exact H7.
exact H10.
PBC H13.
neg_e C.
exact H8.
exact H11.
PBC H14.
neg_e C.
exact H14.
iff_e2 A.
exact H2.
PBC H15.
neg_e A.
exact H15.
iff_e2 (B <-> C).
exact P1.
iff_i H16 H17.
PBC H18.
neg_e B.
exact H7.
exact H16.
PBC H19.
neg_e C.
exact H14.
exact H17.
Qed.