Require Import ProofWeb.

Parameter P Q : Prop.

Hypothesis P1 : P \/ Q.

Theorem b06 : Q \/ P.

Proof.
dis_e (P \/ Q) H1 H2.
exact P1.
dis_i2.
exact H1.
dis_i1.
exact H2.
Qed.
