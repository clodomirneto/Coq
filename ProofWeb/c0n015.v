Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A /\ B).

Theorem c0n015 : (B /\ A).
Proof.
con_i.
con_e2 A.
exact P1.
con_e1 B.
exact P1.
Qed.