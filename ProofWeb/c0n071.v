Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (~A \/ B).
Hypothesis P2: A.

Theorem c0n071 : B.
Proof.
PBC H1.
neg_e A.
dis_e (~A \/ B) H2 H3.
exact P1.
exact H2.
neg_i H4.
neg_e B.
exact H1.
exact H3.
exact P2.
Qed.