Require Import ProofWeb.

Variable R: D*D -> Prop.
Variable i: D.

Theorem c1n032 : exi x,exi y,(R(x,y)->R(y,x)).
Proof.
exi_i i.
exi_i i.
imp_i H1.
exact H1.
Qed.