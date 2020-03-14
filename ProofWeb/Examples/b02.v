Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1 : ~A -> (B -> C).

Hypothesis P2 : ~A.

Hypothesis P3 : B.

Theorem b02 : C.

Proof.
imp_e (B).
imp_e (~A).
exact P1.
exact P2.
exact P3.
Qed.
