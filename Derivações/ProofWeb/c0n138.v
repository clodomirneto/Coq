Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n138 : ((A <-> B) <-> ((A /\ B) \/ (~A /\ ~B))).
Proof.
iff_i H1 H2.
PBC H3.
neg_e ((A /\ B) \/ (~A /\ ~B)).
exact H3.
dis_i2.
con_i.
neg_i H4.
neg_e ((A /\ B) \/ (~A /\ ~B)).
exact H3.
dis_i1.
con_i.
exact H4.
iff_e1 A.
exact H1.
exact H4.
neg_i H5.
neg_e ((A /\ B) \/ (~A /\ ~B)).
exact H3.
dis_i1.
con_i.
iff_e2 B.
exact H1.
exact H5.
exact H5.
iff_i H6 H7.
dis_e ((A /\ B) \/ (~A /\ ~B)) H8 H9.
exact H2.
con_e2 A.
exact H8.
PBC H10.
neg_e A.
con_e1 (~B).
exact H9.
exact H6.
dis_e ((A /\ B) \/ (~A /\ ~B)) H11 H12.
exact H2.
con_e1 B.
exact H11.
PBC H13.
neg_e B.
con_e2 (~A).
exact H12.
exact H7.
Qed.