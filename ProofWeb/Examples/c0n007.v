Require Import ProofWeb.

Parameter A B C D : Prop.

Hypothesis P1: (A -> (B -> (C -> D))).

Theorem c0n007 : (C -> (B -> (A -> D))).
Proof.
imp_i H1.
imp_i H2.
imp_i H3.
imp_e C.
imp_e B.
imp_e A.
exact P1.
exact H3.
exact H2.
exact H1.
Qed.