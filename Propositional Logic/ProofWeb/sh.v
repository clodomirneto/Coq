Require Import ProofWeb.

Variables A B C : Prop.

Hypothesis P1 : A -> B.
Hypothesis P2 : B -> C.

Theorem sh : A -> C.
Proof.
imp_i Ha.
imp_e (B).
exact P2.
imp_e (A).
exact P1.
exact Ha.
Qed.