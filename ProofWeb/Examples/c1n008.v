Require Import ProofWeb.

Variable P: Prop.
Variable R: D -> Prop.

Hypothesis P1 : exi x,(P->R(x)).

Theorem c1n008 : P->exi x,R(x).
Proof.
imp_i H1.
exi_e (exi x, (P -> R(x))) i H2.
exact P1.
exi_i i.
imp_e P.
exact H2.
exact H1.
Qed.