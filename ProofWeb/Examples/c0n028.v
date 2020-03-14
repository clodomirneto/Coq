Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: ((A \/ B) \/ C).

Theorem c0n028 : (A \/ (B \/ C)).
Proof.
dis_e ((A \/ B) \/ C) H1 H2.
exact P1.
dis_e (A \/ B) H3 H4.
exact H1.
dis_i1.
exact H3.
dis_i2.
dis_i1.
exact H4.
dis_i2.
dis_i2.
exact H2.
Qed.