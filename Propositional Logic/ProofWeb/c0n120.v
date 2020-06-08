Require Import ProofWeb.

Parameter A : Prop.

Theorem c0n120 : (A <-> (A /\ True)).
Proof.
iff_i H1 H2.
con_i.
exact H1.
tru_i.
con_e1 True.
exact H2.
Qed.