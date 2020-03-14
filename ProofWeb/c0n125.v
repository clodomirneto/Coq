Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n125 : ((~A -> B) <-> (~B -> A)).
Proof.
iff_i H1 H2.
imp_i H3.
PBC H4.
neg_e B.
exact H3.
imp_e (~A).
exact H1.
exact H4.
imp_i H5.
PBC H6.
neg_e A.
exact H5.
imp_e (~B).
exact H2.
exact H6.
Qed.