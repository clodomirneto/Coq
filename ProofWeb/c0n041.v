Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A /\ B).

Theorem c0n041 : (A -> B).
Proof.
imp_i H1.
con_e2 A.
exact P1.
Qed.