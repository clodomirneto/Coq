Require Import ProofWeb.

Variables R : D*D -> Prop.

Hypothesis P1 : exi x,exi y,R(x,y).

Theorem c1n052 : exi y,exi x,R(x,y).
Proof.
exi_e (exi x, exi y, R(x, y)) a H1.
exact P1.
exi_e (exi y, R(a,y)) b H2.
exact H1.
exi_i b.
exi_i a.
exact H2.
Qed.