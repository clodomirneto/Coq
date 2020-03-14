Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A -> C).

Theorem c0n017 : ((A /\ B) -> C).
Proof.
imp_i H1.
imp_e A.
exact P1.
con_e1 B.
exact H1.
Qed.