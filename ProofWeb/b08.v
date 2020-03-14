Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1 : ~A.

Hypothesis P2 : B -> A.

Theorem b08 : ~B.

Proof.
neg_i H1.
neg_e (A).
exact P1.
imp_e (B).
exact P2.
exact H1.
Qed.
