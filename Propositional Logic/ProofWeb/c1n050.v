Require Import ProofWeb.

Variable R : D*D -> Prop.

Hypothesis P1 : exi z,R(z,z).
 
Theorem c1n050 : exi x,exi y,R(x,y).
Proof.
exi_e (exi z, R(z, z)) a H1.
exact P1.
exi_i a.
exi_i a.
exact H1.
Qed.