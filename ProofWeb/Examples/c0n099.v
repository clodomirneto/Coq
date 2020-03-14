Require Import ProofWeb.

Parameter A B C D E : Prop.

Hypothesis P1: ~(~A /\ B /\ ~C).
Hypothesis P2: B.

Theorem c0n099 : (A \/ C).
Proof.
PBC H1.
neg_e (~A /\ B /\ ~C).
exact P1.
con_i.
neg_i H2.
neg_e (A \/ C).
exact H1.
dis_i1.
exact H2.
con_i.
exact P2.
neg_i H3.
neg_e (A \/ C).
exact H1.
dis_i2.
exact H3.
Qed.