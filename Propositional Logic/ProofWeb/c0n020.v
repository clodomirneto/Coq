Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: ((A /\ B) -> C).

Theorem c0n020 : (A -> (B -> C)).
Proof.
imp_i H1.
imp_i H2.
imp_e (A /\ B).
exact P1.
con_i.
exact H1.
exact H2.
Qed.