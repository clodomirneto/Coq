Require Import ProofWeb.

Parameter A B : Prop.

Theorem dgm16 : (A -> B) -> (~A \/ B).

Proof.
imp_i H1.
PBC H2.
neg_e (~A \/ B).
exact H2.
dis_i1.
neg_i H3.
neg_e (~A \/ B).
exact H2.
dis_i2.
imp_e (A).
exact H1.
exact H3.
Qed.
