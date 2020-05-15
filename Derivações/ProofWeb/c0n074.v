Require Import ProofWeb.

Parameter A B C D E : Prop.

Hypothesis P1: A \/ E \/ B.
Hypothesis P2: C \/ ~E \/ D.

Theorem c0n074 : A \/ B \/ C \/ D.
Proof.
dis_e (A \/ E \/ B) H1 H2.
exact P1.
dis_i1.
exact H1.
dis_e (C \/ ~E \/ D) H3 H4.
exact P2.
dis_i2.
dis_i2.
dis_i1.
exact H3.
dis_e (E \/ B) H5 H6.
exact H2.
dis_e (~E \/ D) H7 H8.
exact H4.
PBC H9.
neg_e E.
exact H7.
exact H5.
dis_i2.
dis_i2.
dis_i2.
exact H8.
dis_i2.
dis_i1.
exact H6.
Qed.