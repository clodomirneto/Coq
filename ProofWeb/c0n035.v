Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A -> B).

Theorem c0n035 : ((C \/ A) -> (B \/ C)).
Proof.
imp_i H1.
dis_e (C \/ A) H2 H3.
exact H1.
dis_i2.
exact H2.
dis_i1.
imp_e A.
exact P1.
exact H3.
Qed.