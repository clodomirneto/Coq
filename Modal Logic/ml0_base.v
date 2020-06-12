(* Preâmbulo *)
Set Implicit Arguments.
Require Export Bool.
Require Export List.
Import ListNotations.
(* Módulo Base *)
Module Type mod_base.
(* Meu escopo *)
Declare Scope My_scope.
Open Scope My_scope.
(* Conjunto das Variáveis Proposicionais *)
Parameter VProp : Set.
(* Igualdade é decidível em VarProp *)
Parameter VarSeq_dec : forall x y: VProp, {x = y} + {x <> y}.
(* Função usada em  ml1_soundness *)
Fixpoint map_fold_right (A B :Type) (f : B -> A) (g : A -> A -> A) a l := match l with
| nil => a
| b :: l2 => g (f b) (map_fold_right f g a l2)
end.
End mod_base.