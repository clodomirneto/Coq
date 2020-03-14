Require Import ProofWeb.

Variable P: Prop.
Variable R: D -> Prop.

Hypothesis P1 : P->all x,R(x).

Theorem c1n007 : all x,(P->R(x)).
Proof.
all_i a.
imp_i H1.
imp_e P.
imp_i H2.
all_e (all x, R(x)).
imp_e P.
exact P1.
exact H1.
exact H1.
Qed.