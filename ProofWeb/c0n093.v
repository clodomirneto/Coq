Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A \/ B).

Theorem c0n093 : ~(~A /\ ~B).
Proof.
neg_i H1.
neg_e (A \/ B).
neg_i H2.
neg_e A.
con_e1 (~B).
exact H1.
dis_e (A \/ B) H3 H4.
exact P1.
exact H3.
PBC H5.
neg_e B.
con_e2 (~A).
exact H1.
exact H4.
exact P1.
Qed.