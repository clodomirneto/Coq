Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n130 : ((A <-> B) <-> ((A -> B) /\ (B -> A))).
Proof.
iff_i H1 H2.
con_i.
imp_i H3.
iff_e1 A.
exact H1.
exact H3.
imp_i H4.
iff_e2 B.
exact H1.
exact H4.
iff_i H5 H6.
imp_e A.
con_e1 (B -> A).
exact H2.
exact H5.
imp_e B.
con_e2 (A -> B).
exact H2.
exact H6.
Qed.