Require Import ProofWeb.

Variable P: Prop.
Variable R: D -> Prop.
Variable i: D.

Hypothesis P1 : (exi x,R(x))->P.

Theorem c1n004 : exi x,(R(x)->P).
Proof.
exi_i i.
imp_i H1.
imp_e (exi x, R(x)).
exact P1.
exi_i i.
exact H1.
Qed.