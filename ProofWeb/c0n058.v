Require Import ProofWeb.

Parameter A : Prop.

Theorem c0n058 : ((A -> ~A) -> ~A).
Proof.
imp_i H1.
neg_i H2.
neg_e A.
imp_e A.
exact H1.
exact H2.
exact H2.
Qed.