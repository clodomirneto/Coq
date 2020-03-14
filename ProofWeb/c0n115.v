Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A <-> B).
Hypothesis P2: (A <-> ~B).

Theorem c0n115 : False.
Proof.
PBC H1.
neg_e (A <-> B).
neg_i H2.
neg_e A.
neg_i H3.
neg_e B.
iff_e1 A.
exact P2.
exact H3.
iff_e1 A
exact P1.
exact H3.
iff_e2 B.
exact P1.
PBC H4.
neg_e A.
neg_i H5.
neg_e B.
exact H4.
iff_e1 A. 
exact P1.
exact H5.
iff_e2 (~B).
exact P2.
exact H4.
exact P1.
Qed.