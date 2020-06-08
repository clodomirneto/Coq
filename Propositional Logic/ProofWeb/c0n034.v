Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A -> C).
Hypothesis P2: (B -> C).

Theorem c0n034 : ((A \/ B) -> C).
Proof.
imp_i H1.
dis_e (A \/ B) H2 H3.
exact H1.
imp_e A.
exact P1.
exact H2.
imp_e B.
exact P2.
exact H3.
Qed.