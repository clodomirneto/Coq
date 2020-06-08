Set Implicit Arguments.
Require Export Bool.
Require Export List.
Import ListNotations.
Module Type base_mod.
Declare Scope My_scope.
Open Scope My_scope.

Parameter PropVars : Set.

Parameter Varseq_dec : forall x y: PropVars, {x = y} + {x <> y}.

Fixpoint map_fold_right (A B :Type) (f : B -> A) (g : A -> A -> A) a l := match l with
| nil => a
| b :: l2 => g (f b) (map_fold_right f g a l2)
end.

End base_mod.