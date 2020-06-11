Set Implicit Arguments.
Require Export Bool.
Require Export List.
Import ListNotations.

(* Módulo Base *)
Module Type mod_base.
Declare Scope My_scope.
Open Scope My_scope.
Parameter VarProp : Set.
Parameter VarSeq : forall x y: VarProp, {x = y} + {x <> y}.
End mod_base.

(* Módulo Corretude *)
Module Type mod_sound (B : mod_base).
Import B.

(* Definição de Fórmulas Proposicionais *)
Inductive FormProp : Set :=
| Var : VarProp -> FormProp
| Bot : FormProp
| Conj : FormProp -> FormProp -> FormProp
| Disj : FormProp -> FormProp -> FormProp
| Impl : FormProp -> FormProp -> FormProp.

(* Notações *)
Notation "# P" := (Var P) (at level 1) : My_scope.

Notation "A ∨ B" := (Disj A B) (at level 15, right associativity) : My_scope.

Notation "A ∧ B" := (Conj A B) (at level 15, right associativity) : My_scope.

Notation "A → B" := (Impl A B) (at level 16, right associativity) : My_scope.

Notation "⊥" := Bot (at level 0)  : My_scope.

Definition Neg A := A → ⊥.

Notation "¬ A" := (Neg A) (at level 5) : My_scope.

Definition Top := ¬ ⊥.

Notation "⊤" := Top (at level 0) : My_scope.

Definition BiImpl A B := (A → B) ∧ (B → A).

Notation "A ↔ B" := (BiImpl A B) (at level 17, right associativity) : My_scope.

(* Semântica *)
Fixpoint TrueQ v A : bool := match A with
 | # P => v P
 | ⊥ => false
 | B ∨ C => (TrueQ v B) || (TrueQ v C)
 | B ∧ C => (TrueQ v B) && (TrueQ v C)
 | B → C => (negb (TrueQ v B)) || (TrueQ v C)
end.

Definition Satisfies v Γ := forall A, In A Γ -> Is_true (TrueQ v A).

Definition Models Γ A := forall v, Satisfies v Γ -> Is_true (TrueQ v A).

Notation "Γ ⊨ A" := (Models Γ A) (at level 80).

Definition Valid A := [] ⊨ A.

Reserved Notation "Γ ⊢ A" (at level 80).

(* Dedução Natural *)
Inductive Nc : list FormProp -> FormProp -> Prop :=
| Nax : forall Γ A, In A Γ -> Γ ⊢ A
| ImpI : forall Γ A B, A :: Γ ⊢ B -> Γ ⊢ A → B
| ImpE : forall Γ A B, Γ ⊢ A → B -> Γ ⊢ A -> Γ ⊢ B
| BotC : forall Γ A, ¬ A :: Γ ⊢ ⊥ -> Γ ⊢ A
| AndI : forall Γ A B, Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ A ∧ B
| AndE1 : forall Γ A B, Γ ⊢ A ∧ B -> Γ ⊢ A
| AndE2 : forall Γ A B, Γ ⊢ A ∧ B -> Γ ⊢ B
| OrI1 : forall Γ A B, Γ ⊢ A -> Γ ⊢ A ∨ B
| OrI2 : forall Γ A B, Γ ⊢ B -> Γ ⊢ A ∨ B
| OrE : forall Γ A B C, Γ ⊢ A ∨ B -> A :: Γ ⊢ C -> B :: Γ ⊢ C -> Γ ⊢ C
where "Γ ⊢ A" := (Nc Γ A) : My_scope.

Definition Provable A := [] ⊢ A.

Definition Prop_Soundness := forall A, Provable A -> Valid A.

Definition Prop_Completeness := forall A, Valid A -> Provable A.

Ltac mp := eapply ImpE.

Ltac AddnilL := match goal with
| |- _ ?Γ _ => change Γ with ([] ++ Γ)
end.

Ltac in_solve := intros; repeat
(eassumption
||match goal with
| H : In _ (_::_) |- _ => destruct H; [subst; try discriminate|]
| H : In _ (_++_) |- _ => apply in_app_iff in H as []; subst
| |- In _ (_++_) => apply in_app_iff; (left; in_solve; fail)|| (right; in_solve; fail) 
  end
||(constructor; reflexivity)
||constructor 2).

Ltac is_ass := econstructor; in_solve.

Ltac case_bool v A := let HA := fresh "H" in (case_eq (TrueQ v A); intro HA; try rewrite HA in *; simpl in *; try trivial; try contradiction).

Local Ltac prove_satisfaction :=
intros ? K; destruct K; [subst; simpl;
match goal with
| [ H : TrueQ _ _ = _  |-  _ ] => rewrite H
end; exact I|auto].

Lemma FormPropSeq : forall (x y : FormProp), {x = y} + {x <> y}.
induction x; destruct y; try (right; discriminate); try (destruct (IHx1 y1); [destruct (IHx2 y2); [left;f_equal;assumption|]|]; right; injection; intros; contradiction).
destruct (VarSeq v v0).
left; f_equal; assumption.
right; injection; intro; contradiction.
left; reflexivity.
Qed.

Lemma Excluded_Middle : forall Γ A, Γ ⊢ A ∨ ¬ A.
Proof.
intros Γ A.
apply BotC.
mp.
is_ass.
apply OrI2.
apply ImpI.
mp.
is_ass.
apply OrI1.
is_ass.
Qed.

Lemma weakening2 : forall Γ A, Γ ⊢ A -> forall Δ, (forall B, In B Γ -> In B Δ) -> Δ ⊢ A.
induction 1; [constructor|constructor 2|econstructor 3|constructor 4|constructor 5|econstructor 6
|econstructor 7|constructor 8|constructor 9|econstructor 10]; try eauto; [apply IHNc..|apply IHNc2|try apply IHNc3]; intros; in_solve; eauto.
Qed.

Lemma weakening : forall Γ Δ A, Γ ⊢ A -> Γ ++ Δ ⊢ A.
intros; eapply weakening2; [eassumption|in_solve].
Qed.

Lemma deduction : forall Γ A B, Γ ⊢ A → B -> A :: Γ ⊢ B.
intros; eapply ImpE with A; [eapply weakening2; [eassumption|in_solve]|is_ass].
Qed.

Lemma prov_impl : forall A B, Provable (A → B)-> forall Γ, Γ ⊢ A -> Γ ⊢ B.
intros.
mp.
AddnilL; apply weakening.
apply H.
assumption.
Qed.

Ltac prov_impl_in IH := let H := fresh "K" in try (remember (prov_impl IH) as H eqn:HeqH; clear IH HeqH).

Theorem Soundness_general : forall A Γ, Γ ⊢ A -> Γ ⊨ A.
intros A Γ H0 v; induction H0; simpl; intros; auto; try simpl in IHNc; try simpl in IHNc1; try simpl in IHNc2; case_bool v A; try (case_bool v B; fail); try (apply IHNc||apply IHNc2; prove_satisfaction); case_bool v B; apply IHNc3; prove_satisfaction.
Qed.

Theorem Soundness : Prop_Soundness.
intros ? ? ? ?; eapply Soundness_general; eassumption.
Qed.

End mod_sound.