Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A <-> B).

Theorem c0n144 : ((C -> A) <-> (C -> B)).
Proof.
iff_i H1 H2.
imp_i H3.
iff_e1 A.
exact P1.
imp_e C.
exact H1.
exact H3.
imp_i H4.
iff_e2 B.
exact P1.
imp_e C.
exact H2.
exact H4.
Qed.