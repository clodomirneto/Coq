Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A /\ (B -> C)).

Theorem c0n022 : ((A -> B) -> C).
Proof.
imp_i H1.
imp_e B.
con_e2 A.
exact P1.
imp_e A.
exact H1.
con_e1 (B -> C).
exact P1.
Qed.