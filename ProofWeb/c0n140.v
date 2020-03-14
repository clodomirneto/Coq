Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A <-> B).

Theorem c0n140 : (~A <->  ~B).
Proof.
iff_i H1 H2.
neg_i H3.
neg_e A.
exact H1.
iff_e2 B.
exact P1.
exact H3.
neg_i H4.
neg_e B.
exact H2.
iff_e1 A.
exact P1.
exact H4.
Qed.