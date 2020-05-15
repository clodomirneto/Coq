Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n139 : ((A <-> B) <-> ((~A \/ B) /\ (A \/ ~B))).
Proof.
iff_i H1 H2.
PBC H3.
neg_e ((~ A \/ B) /\ (A \/ ~ B)).
exact H3.
con_i.
dis_i1.
neg_i H4.
neg_e ((~ A \/ B) /\ (A \/ ~ B)).
exact H3.
con_i.
dis_i2.
iff_e1 A.
exact H1.
exact H4.
dis_i1.
exact H4.
dis_i2.
neg_i H5.
neg_e ((~ A \/ B) /\ (A \/ ~ B)).
exact H3.
con_i.
dis_i2.
exact H5.
dis_i1.
iff_e2 B.
exact H1.
exact H5.
iff_i H6 H7.
dis_e (~A \/ B) H8 H9.
con_e1 (A \/ ~B).
exact H2.
PBC H10.
neg_e A.
exact H8.
exact H6.
exact H9.
dis_e (A \/ ~B) H11 H12.
con_e2 (~A \/ B).
exact H2.
exact H11.
PBC H13.
neg_e B.
exact H12.
exact H7.
Qed.