Require Import ProofWeb.

Parameter A : Prop.

Theorem c0n059 : ((~A -> A) -> A).
Proof.
imp_i H1.
PBC H2.
neg_e A.
exact H2.
imp_e (~A).
exact H1.
exact H2.
Qed.