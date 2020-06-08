Require Import ProofWeb.

Parameter A : Prop.

Theorem c0n100 : (A <-> A).
Proof.
iff_i H1 H2.
exact H1.
exact H2.
Qed.