Require Import ProofWeb.

Variables A B : Prop.

Hypothesis P1 : A -> B.
Hypothesis P2 : ~B.

Theorem mt : ~A.
Proof.
neg_i Ha.
neg_e (B).
exact P2.
imp_e (A).
exact P1.
exact Ha.
Qed.