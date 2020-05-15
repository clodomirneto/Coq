Require Import ProofWeb.

Parameter A B C: Prop.

Hypothesis P1: A -> B.

Theorem dgm02: A -> (B \/ C).

Proof.
imp_i H1.
dis_i1.
imp_e (A).
exact P1.
exact H1.
Qed.
