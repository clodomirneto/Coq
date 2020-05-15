Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: ((A -> B) -> C).

Theorem c0n008 : (A -> (B -> C)).
Proof.
imp_i H1.
imp_i H2.
imp_e (A -> B).
exact P1.
imp_i H3.
exact H2.
Qed.