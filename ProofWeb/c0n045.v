Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A /\ False ).

Theorem c0n045 : B.
Proof.
PBC H1.
con_e2 A.
exact P1.
Qed.