Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: A.

Theorem c0n042 : (A /\ (A \/ B)).
Proof.
con_i.
exact P1.
dis_i1.
exact P1.
Qed.