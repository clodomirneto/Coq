Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A \/ (A /\ B)).

Theorem c0n043 : A.
Proof.
dis_e (A \/ (A /\ B)) H1 H2.
exact P1.
exact H1.
con_e1 B.
exact H2.
Qed.