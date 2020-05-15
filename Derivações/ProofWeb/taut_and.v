Require Import ProofWeb.

Variables A : Prop.

Theorem taut_and : A <-> A /\ A.
Proof.
iff_i Ha Haa.
con_i.
exact Ha.
exact Ha.
con_e1 (A).
exact Haa.
Qed.