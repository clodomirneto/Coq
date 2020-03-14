Require Import ProofWeb.

Variable P: Prop.
Variable R: D -> Prop.

Hypothesis P1 : exi x,(R(x) /\ P).

Theorem c1n001 : exi x,R(x).
Proof.
exi_e (exi x, (R(x) /\ P)) a H1.
exact P1.
exi_i a.
con_e1 P.
exact H1.
Qed.