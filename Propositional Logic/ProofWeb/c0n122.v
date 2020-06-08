Require Import ProofWeb.

Parameter A B : Prop.

Theorem c0n122 : ((A /\ B) <-> (B /\ A)).
Proof.
iff_i H1 H2.
con_i.
con_e2 A.
exact H1.
con_e1 B.
exact H1.
con_i.
con_e2 B.
exact H2.
con_e1 A.
exact H2.
Qed.