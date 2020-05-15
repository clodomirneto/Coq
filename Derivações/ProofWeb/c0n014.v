Require Import ProofWeb.

Parameter A : Prop.

Hypothesis P1: A.

Theorem c0n014 : (A /\ A).
Proof.
con_i.
exact P1.
exact P1.
Qed.