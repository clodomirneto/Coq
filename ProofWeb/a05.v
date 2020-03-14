Require Import ProofWeb.

Parameter P : Prop.

Theorem a05 : ~(P <-> ~P).

Proof.
neg_i H1.
neg_e P.
neg_i H2.
neg_e P.
iff_e1 P.
exact H1.
exact H2.
exact H2.
PBC H3.
neg_e P.
exact H3.
iff_e2 (~P).
exact H1.
exact H3.
Qed.