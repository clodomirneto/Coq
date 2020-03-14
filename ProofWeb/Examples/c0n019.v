Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A -> (B -> C)).

Theorem c0n019 : ((A /\ B) -> C).
Proof.
imp_i H1.
imp_e B.
imp_e A.
exact P1.
con_e1 B.
exact H1.
con_e2 A.
exact H1.
Qed.