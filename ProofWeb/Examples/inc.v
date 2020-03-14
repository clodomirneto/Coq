Require Import ProofWeb.

Parameter A B: Prop.

Hypothesis P1: A.
Hypothesis P2: ~A.

Theorem inc: B. 
Proof.
PBC H1.
neg_e A.
exact P2.
exact P1.
Qed.