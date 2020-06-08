Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A <-> B).

Theorem c0n143 : ((A -> C) <-> (B -> C)).
Proof.
iff_i H1 H2.
imp_i H3.
imp_e A.
exact H1.
iff_e2 B.
exact P1.
exact H3.
imp_i H4.
imp_e B.
exact H2.
iff_e1 A.
exact P1.
exact H4.
Qed.