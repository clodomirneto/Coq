Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n123 : ((A \/ B) <-> (B \/ A)).
Proof.
iff_i H1 H2.
dis_e (A \/ B) H3 H4.
exact H1.
dis_i2.
exact H3.
dis_i1.
exact H4.
dis_e (B \/ A) H5 H6.
exact H2.
dis_i2.
exact H5.
dis_i1.
exact H6.
Qed.