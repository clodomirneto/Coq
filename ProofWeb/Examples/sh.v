Require Import ProofWeb.

Parameter A B C: Prop.

Hypothesis P1: A -> B.
Hypothesis P2: B -> C.

Theorem sh: A -> C.
Proof.
imp_i H1.
imp_e B.
exact P2.
imp_e A.
exact P1.
exact H1.
Qed.