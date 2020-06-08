Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n119 : (~A <-> B) <-> (A <-> ~B).
Proof.
iff_i H1 H2.
iff_i H3 H4.
neg_i H5.
neg_e A.
iff_e2 B.
exact H1.
exact H5.
exact H3.
PBC H6.
neg_e B.
exact H4.
iff_e1 (~A).
exact H1.
exact H6.
iff_i H7 H8.
PBC H9.
neg_e A.
exact H7.
iff_e2 (~B).
exact H2.
exact H9.
neg_i H10.
neg_e B.
iff_e1 A.
exact H2.
exact H10.
exact H8.
Qed.