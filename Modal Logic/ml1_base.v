Set Implicit Arguments.
Require Export Bool.
Require Export List.
Import ListNotations.
Module Type mod_base.
Declare Scope My_scope.
Open Scope My_scope.

Parameter VarProp : Set.

Parameter VarSeq : forall x y: VarProp, {x = y} + {x <> y}.

Fixpoint map_fold_right (A B :Type) (f : B -> A) (g : A -> A -> A) a l := match l with
| nil => a
| b :: l2 => g (f b) (map_fold_right f g a l2)
end.

End mod_base.