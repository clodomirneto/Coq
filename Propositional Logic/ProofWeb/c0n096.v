Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: ~(~A \/ ~B).

Theorem c0n096 : (A /\ B).
Proof.
con_i.
PBC H1.
neg_e (~A \/ ~B).
exact P1.
dis_i1.
exact H1.
PBC H2.
neg_e (~A \/ ~B).
exact P1.
dis_i2.
exact H2.
Qed.