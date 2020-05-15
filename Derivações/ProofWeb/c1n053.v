Require Import ProofWeb.

Variable R : D*D -> Prop.

Hypothesis P1 : exi x,all y,R(x,y).

Theorem c1n053 : all y,exi x,R(x,y).
Proof.
exi_e (exi x, all y, R(x,y)) a H1.
exact P1.
all_i b.
exi_i a.
all_e (all y, R(a,y)).
exact H1.
Qed.