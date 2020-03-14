Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n132 : ((A /\ B) <-> (A <-> (A -> B))).
Proof.
iff_i H1 H2.
iff_i H3 H4.
imp_i H5.
con_e2 A.
exact H1.
con_e1 B.
exact H1.
con_i.
iff_e2 (A -> B).
exact H2.
imp_i H6.
imp_e A.
iff_e1 A.
exact H2.
exact H6.
exact H6.
imp_e A.
iff_e1 A.
exact H2.
iff_e2 (A -> B).
exact H2.
imp_i H7.
imp_e A.
iff_e1 A.
exact H2.
exact H7.
exact H7.
iff_e2 (A -> B).
exact H2.
imp_i H8.
imp_e A.
iff_e1 A.
exact H2.
exact H8.
exact H8.
Qed.