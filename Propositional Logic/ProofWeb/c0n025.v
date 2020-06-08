Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A \/ A).

Theorem c0n025 : A.
Proof.
dis_e (A \/ A) H1 H2.
exact P1.
exact H1.
exact H2.
Qed.