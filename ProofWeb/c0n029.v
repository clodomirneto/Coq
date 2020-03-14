Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (C \/ (A \/ B)).

Theorem c0n029 : ((B \/ (A \/ C)) \/ A).
Proof.
dis_e (C \/ (A \/ B)) H1 H2.
exact P1.
dis_i1.
dis_i2.
dis_i2.
exact H1.
dis_e (A \/ B) H3 H4.
exact H2.
dis_i2.
exact H3.
dis_i1.
dis_i1.
exact H4.
Qed.