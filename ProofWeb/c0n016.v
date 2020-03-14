Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A /\ (B /\ C)).

Theorem c0n016 : ((A /\ B) /\ C).
Proof.
con_i.
con_i.
con_e1 (B /\ C).
exact P1.
con_e1 C.
con_e2 A.
exact P1.
con_e2 B.
con_e2 A.
exact P1.
Qed.