Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1 : A -> B.

Hypothesis P2 : A -> (B -> C).

Theorem b09 : A -> C.

Proof.
imp_i H1.
imp_e (B).
imp_e (A).
exact P2.
exact H1.
imp_e (A).
exact P1.
exact H1.
Qed.
