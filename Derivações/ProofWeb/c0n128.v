Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n128 : ((A -> B) <-> (A <-> (A /\ B))).
Proof.
iff_i H1 H2.
iff_i H3 H4.
con_i.
exact H3.
imp_e A.
exact H1.
exact H3.
con_e1 B.
exact H4.
imp_i H5.
con_e2 A.
iff_e1 A.
exact H2.
exact H5.
Qed.