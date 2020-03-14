Require Import ProofWeb.

Parameter A B C D E : Prop.

Hypothesis P1: ~(A /\ E /\ B).
Hypothesis P2: ~(C /\ ~E /\ D).

Theorem c0n069 : ~(A /\ B /\ C /\ D).
Proof.
neg_i H1.
neg_e (A /\ E /\ B).
exact P1.
con_i.
con_e1 (B /\ C /\ D).
exact H1.
con_i.
PBC H2.
neg_e (C /\ ~E /\ D).
exact P2.
con_i.
con_e1 D.
con_e2 B.
con_e2 A.
exact H1.
con_i.
exact H2.
con_e2 C.
con_e2 B.
con_e2 A.
exact H1.
con_e1 (C /\ D).
con_e2 A.
exact H1.
Qed.