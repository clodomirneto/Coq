Require Import ProofWeb.

Variable P: Prop.
Variable R: D -> Prop.
Variable i: D.

Hypothesis P1 : P->all x,R(x).

Theorem c1n005 : exi x,(P->R(x)).
Proof.
exi_i i.
imp_i H1.
all_e (all x, R(x)).
imp_e P.
exact P1.
exact H1.
Qed.