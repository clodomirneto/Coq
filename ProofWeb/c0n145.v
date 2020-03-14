Require Import ProofWeb.

Parameter A : Prop.

Theorem c0n145 : ~(A <-> ~A).
Proof.
neg_i H1.
neg_e A.
iff_e1 A.
exact H1.
PBC H2.
neg_e A.
exact H2.
iff_e2 (~A).
exact H1.
exact H2.
PBC H3.
neg_e A.
iff_e1 A.
exact H1.
iff_e2 (~A).
exact H1.
exact H3.
iff_e2 (~A).
exact H1.
exact H3.
Qed.