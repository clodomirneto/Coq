Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A -> B).

Theorem c0n083 : (~A \/ B).
Proof.
PBC H1.
neg_e (~A \/ B).
exact H1.
dis_i1.
neg_i H2.
neg_e (~A \/ B).
exact H1.
dis_i2.
imp_e A.
exact P1.
exact H2.
Qed.