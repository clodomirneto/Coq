Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: ((A \/ B) -> C).

Theorem c0n032 : (A -> C).
Proof.
imp_i H1.
imp_e (A \/ B).
exact P1.
dis_i1.
exact H1.
Qed.