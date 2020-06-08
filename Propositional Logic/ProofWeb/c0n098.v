Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: ~(A /\ B).

Theorem c0n098 : (~A \/ ~B).
Proof.
PBC H1.
neg_e (A /\ B).
exact P1.
con_i.
PBC H2.
neg_e (~A \/ ~B).
exact H1.
dis_i1.
exact H2.
PBC H3.
neg_e (~A \/ ~B).
exact H1.
dis_i2.
exact H3.
Qed.