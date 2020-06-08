Require Import ProofWeb.

Parameter A: Prop.

Theorem dgm14: A \/ ~A.

Proof.
PBC H1.
neg_e (A \/ ~A).
exact H1.
dis_i2.
neg_i H2.
neg_e A.
neg_i H3.
neg_e (A \/ ~A).
exact H1.
dis_i1.
exact H2.
exact H2.
Qed.
