Require Import ProofWeb.

Variable P: Prop.
Variable R: D -> Prop.

Hypothesis P1 : exi x,(R(x) /\ P).

Theorem c1n002 : P.
Proof.
exi_e (exi x, (R(x) /\ P)) a H1.
exact P1.
con_e2 (R(a)).
exact H1.
Qed.