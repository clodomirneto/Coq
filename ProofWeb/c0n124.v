Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n124 : ((A -> B) <-> (~B -> ~A)).
Proof.
iff_i H1 H2.
imp_i H3.
neg_i H4.
neg_e (B).
exact H3.
imp_e A.
exact H1.
exact H4.
imp_i H5.
PBC H6.
neg_e A.
imp_e (~B).
exact H2.
exact H6.
exact H5.
Qed.