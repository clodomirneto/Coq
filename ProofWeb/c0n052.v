Require Import ProofWeb.

Parameter A : Prop.

Theorem c0n052 : ~(A /\ ~A).
Proof.
neg_i H1.
neg_e A.
con_e2 A.
exact H1.
con_e1 (~A).
exact H1.
Qed.