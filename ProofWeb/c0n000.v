Require Import ProofWeb.

Parameter A : Prop.

Theorem c0n000 : (A -> A).
Proof.
imp_i H.
exact H.
Qed.