Require Import ProofWeb.

Parameter A B: Prop.

Theorem dgm12: (A -> B) -> (~B -> ~A).

Proof.
imp_i H1.
imp_i H2.
neg_i H3.
neg_e (B).
exact H2.
imp_e (A).
exact H1.
exact H3.
Qed.
