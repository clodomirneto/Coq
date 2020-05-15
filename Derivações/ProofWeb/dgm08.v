Require Import ProofWeb.

Parameter A B C D E : Prop.

Hypothesis P1 : ~A -> B.

Hypothesis P2 : A -> ~E.

Hypothesis P3 : C -> (D \/ E).

Hypothesis P4 : D -> ~C.

Theorem dgm08 : C -> B.

Proof.
imp_i H1.
imp_e (~A).
exact P1.
neg_i H2.
neg_e (C).
imp_e (D).
exact P4.
dis_e (D \/ E) H3 H4.
imp_e (C).
exact P3.
exact H1.
exact H3.
PBC H5.
neg_e (E).
imp_e (A).
exact P2.
exact H2.
exact H4.
exact H1.
Qed.
