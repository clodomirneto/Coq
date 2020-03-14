Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A -> B).
Hypothesis P2: (~A -> B).

Theorem c0n057 : B.
Proof.
PBC H1.
neg_e B.
exact H1.
imp_e A.
exact P1.
PBC H2.
neg_e B.
exact H1.
imp_e (~A).
exact P2.
exact H2.
Qed.