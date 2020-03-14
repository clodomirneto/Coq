Require Import ProofWeb.

Parameter A B : Prop.

Theorem dgm18 : (~(A \/ B)) -> (~A /\ ~B).

Proof.
imp_i H1.
con_i.
neg_i H2.
neg_e (A \/ B).
exact H1.
dis_i1.
exact H2.
neg_i H3.
neg_e (A \/ B).
exact H1.
dis_i2.
exact H3.
Qed.
