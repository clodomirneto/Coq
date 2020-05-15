Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: ~(~A /\ B).
Hypothesis P2: B.

Theorem c0n067 : A.
Proof.
PBC H1.
neg_e (~A /\ B).
exact P1.
con_i.
exact H1.
exact P2.
Qed.