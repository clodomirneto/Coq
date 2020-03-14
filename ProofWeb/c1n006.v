Require Import ProofWeb.

Variable P: Prop.
Variable R: D -> Prop.

Hypothesis P1 : all x,(P->R(x)).

Theorem c1n006 : P->all x,R(x).
Proof.
imp_i H1.
all_i a.
imp_e P.
all_e (all x, (P -> R(x))).
exact P1.
exact H1.
Qed.