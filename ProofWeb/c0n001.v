Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n001 : (A -> (B -> A)).
Proof.
imp_i H1.
imp_i H2.
exact H1.
Qed.