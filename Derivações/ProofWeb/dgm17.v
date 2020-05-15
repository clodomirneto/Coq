Require Import ProofWeb.

Parameter A B : Prop.

Theorem dgm17 : (~(A /\ B)) -> (~A \/ ~B).

Proof.
imp_i H1.
PBC H2.
neg_e (~A \/ ~B).
exact H2.
PBC H3.
neg_e (A /\ B).
exact H1.
con_i.
PBC H4.
neg_e (~A \/ ~B).
exact H3.
dis_i1.
exact H4.
PBC H5.
neg_e (~A \/ ~B).
exact H3.
dis_i2.
exact H5.
Qed.
