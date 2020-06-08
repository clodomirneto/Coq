Require Import ProofWeb.

Variables A B C D : Prop.

Hypothesis P1 : ~C \/ ~D.
Hypothesis P2 : A -> C.
Hypothesis P3 : B -> D.

Theorem dd : ~A \/ ~B.
Proof.
dis_e (~C \/ ~D) Hnc Hnd.
exact P1.
dis_i1.
neg_i Ha.
neg_e (C).
exact Hnc.
imp_e (A).
exact P2.
exact Ha.
dis_i2.
neg_i Hb.
neg_e (D).
exact Hnd.
imp_e (B).
exact P3.
exact Hb.
Qed.