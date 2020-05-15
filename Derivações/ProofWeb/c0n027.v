Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A \/ (B \/ C)).

Theorem c0n027 : ((A \/ B) \/ C).
Proof.
dis_e (A \/ (B \/ C)) H1 H2.
exact P1.
dis_i1.
dis_i1.
ass H1.
dis_e (B \/ C) H3 H4.
exact H2.
dis_i1.
dis_i2.
exact H3.
dis_i2.
exact H4.
Qed.