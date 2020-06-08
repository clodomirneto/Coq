Require Import ProofWeb.

Variables A : Prop.

Theorem taut_or : A <-> A \/ A.
Proof.
iff_i Ha Haa.
dis_i1.
exact Ha.
dis_e (A \/ A) Ha Ha'.
exact Haa.
exact Ha.
exact Ha'.
Qed.