Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A /\ (B \/ C)).

Theorem c0n036 : ((A /\ B) \/ (A /\ C)).
Proof.
dis_e (B \/ C) H1 H2.
con_e2 A.
exact P1.
dis_i1.
con_i.
con_e1 (B \/ C).
exact P1.
exact H1.
dis_i2.
con_i.
con_e1 (B \/ C).
exact P1.
exact H2.
Qed.