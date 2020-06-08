Require Import ProofWeb.

Parameter A : Prop.

Theorem c0n121 : (A <-> (A \/ False)).
Proof.
iff_i H1 H2.
dis_i1.
exact H1.
dis_e (A \/ False) H3 H4.
exact H2.
exact H3.
PBC H5.
exact H4.
Qed.