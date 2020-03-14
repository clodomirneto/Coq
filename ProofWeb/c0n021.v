Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: ((A -> B) -> C).

Theorem c0n021 : ((A /\ B) -> C).
Proof.
imp_i H1.
imp_e (A -> B).
exact P1.
imp_i H2.
con_e2 A.
exact H1.
Qed.