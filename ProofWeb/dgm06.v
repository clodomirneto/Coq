Require Import ProofWeb.

Parameter A B C: Prop.

Theorem dgm06: (A -> (B -> C)) -> (A -> B) -> (A -> C).

Proof.
imp_i H1.
imp_i H2.
imp_i H3.
imp_e (B).
imp_e (A).
exact H1.
exact H3.
imp_e (A).
exact H2.
exact H3.
Qed.
