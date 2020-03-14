Require Import ProofWeb.

Parameter P Q : Prop.

Theorem a06 : (P -> Q) -> (~Q -> ~P).

Proof.
imp_i H1.
imp_i H2.
neg_i H3.
neg_e Q.
exact H2.
imp_e P.
exact H1.
exact H3.
Qed.