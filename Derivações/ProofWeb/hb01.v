Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1 : C.

Hypothesis P2 : B -> A.

Hypothesis P3 : C -> B.

Theorem b01 : A.

Proof.
imp_e (B).
exact P2.
imp_e (C).
exact P3.
exact P1.
Qed.
