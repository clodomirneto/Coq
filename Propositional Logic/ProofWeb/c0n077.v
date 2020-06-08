Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: A.

Theorem c0n077 : ~(~A /\ B).
Proof.
neg_i H1.
neg_e A.
con_e1 B.
exact H1.
exact P1.
Qed.