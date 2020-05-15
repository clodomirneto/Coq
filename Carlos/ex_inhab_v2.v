Section S1.
  Variable A B : Prop .

  (* What is the proof of A -> A? It is the identity function! *)

  Theorem Id1: A->A.
    intro.
    exact H.
  Qed.

  (* The identity function on Nat *)
  Definition IdNat:= fun (x:nat) => x.
  Check IdNat.
  Compute IdNat 3.
  Eval compute in IdNat 3.

  (* But we can also define the identity on every type (polymorphism)
   *)

  Definition ID := fun A:Type => (* dependent types! *)
                     fun x:A => x.
  Check ID.
  Check ID nat.
  Check ID nat 3.
  Compute ID nat 3.
  Check ID Prop True.
  Eval compute in ID Prop True.
  
  (* In a more compact way *)
  Definition ID' (A:Type) (x:A) := x.
  Check ID'.

  Eval compute in ID nat 3.
  Eval compute in ID (nat -> nat). (* identity on nat functions *)
  Eval compute in ID (nat -> nat) (fun x :nat => S x).
  Eval compute in ID (nat -> nat) (fun x :nat => S x) 4.
  
  (* We can write a "program" with type A ->A. *)
  Definition ProgId : A -> A:=
    fun x:A => x.

  Check ID A.
  (* Or using or polymorphic version of ID *)
  Definition ProgId' : A -> A:=
    ID A.
  

  (* Note that the theorem Id1 (proved using tactics) is indeed a
  "program" that inhabit the proposition A -> A *)
  Print Id1. 
  

  (* Consider the proposition/type (A -> B) -> A -> B *)
  Definition Prop1 :Prop := (A-> B) -> A -> B.

  (* We can show that Prop1 holds... by writing a program that
  inhabitant that proposition *)
  Theorem Prop1isTrue : Prop1.
    unfold Prop1.
    intros HAB HA.
    apply HAB.
    exact HA.
  Qed.

  (* Here the program *)
  Print Prop1isTrue.

  (* But there are many ways of proving that proposition. In other
  words, there are many programs with the same type. Here some
  examples. *)

  (* (A -> B) -> A -> B *)
  (* If HAB has type A->B, we return HB *)
  Definition P1P1 : Prop1 :=
    fun (HAB : A -> B) => HAB.

  Check ID (A -> B).
  (* The previous one looks like the identity... from A->B returns A -> B *)
  Definition P1P1' : Prop1 :=
    ID ( A -> B).
  

  (* Another one *)
  (* (A -> B) -> A -> B *)
  Definition P1P2 : Prop1 :=
    fun (HAB : A -> B) =>
      fun (HA : A) =>
        HAB HA.

  
  (* A more (unnecessarily) more complicated program *)
  Definition P1P3 : Prop1 :=
    fun (HAB : A -> B) =>
      fun (HA : A) =>
        ( ID B) (HAB HA). (* note that (fun x =>x) (HAB HA) returns precisely (HAB HA) *)

  (* We can also build such complicated program using tactics *)
  Theorem P1P3' : Prop1.
    intros HAB HA.
    (* An unnecessary step *)
    assert(HidB: B -> B).
    exact (ID B).
    exact (HidB (HAB HA)).
  Qed.
End S1.



Section Bools.
  (* The type for booleans *)
  Variable T : Type.
  Definition  BOOL : Type := T -> T -> T.

  (* True is a function of the type T -> T -> T *)
  Definition TRUE : BOOL :=
    fun (x:T) =>   
      fun (y:T) =>
        x.

  (* What is doing it? is a function that receives 2 values and
  returns the first one. Similarly, FALSE is a function that returns
  the second component *)

  Definition FALSE : BOOL  :=
    fun (x y: T) => y.

  (* It what sense those definitions are really true and false? Let's
  try to define some basic operations on those. *)

  Definition soma (x y:nat) :=  x+y.
  Definition soma3 := soma 3.
  Eval compute in soma3 5.
  
  Definition NOT : BOOL -> BOOL :=
    fun (A :BOOL) => (* the  operand of the negation *)
      fun (x y :T) => A (FALSE x y) (TRUE x y).

  Eval compute in (NOT TRUE).
  Eval compute in (NOT FALSE).

  (* Now conjunction *)
  Definition AND : BOOL -> BOOL -> BOOL :=
    fun (A B : BOOL) => (*  the operands *)
      fun (x y :T) => A (B x y) (FALSE x y).


  Eval compute in (AND TRUE TRUE).
  Eval compute in (AND TRUE FALSE).
  Eval compute in (AND FALSE TRUE).
  Eval compute in (AND FALSE FALSE).

  (* We can easily define an IF-THEN-ELSE based on that representation of booleans *)
  Definition IFTHENELSE  (X Y Z: BOOL) :BOOL :=
    fun (x y : T) =>X (Y x y) (Z x y).
  Eval compute in (IFTHENELSE TRUE FALSE TRUE).
  Eval compute in (IFTHENELSE FALSE FALSE TRUE).
End Bools.

(* But it is a bit strange that we need to add a type T above... that
type can be generalized (using dependent types). *)
Check FALSE.

(* So the type is a dependent type! *)
Definition BOOLG: Type := forall T:Type, T -> T -> T.
(* False is also dependent on T *)
Definition FALSEG : BOOLG :=
  fun (T:Type) =>
    fun (x y :T) =>
      y.

Definition TRUEG : BOOLG :=
  fun (T:Type) =>
    fun (x y :T) =>
      x.

Definition NOTG : BOOLG -> BOOLG :=
  fun (A : BOOLG) =>
    fun (T:Type) (x y :T) => (* x and y depend on the type T! *)
      (A T) (FALSEG T x y) (TRUEG T x y).

Eval compute in NOTG TRUEG.
Eval compute in NOTG TRUE.
   
Section Logic.

  (* Falsity IN L2 *)

  Definition Bot : Type :=  forall Pa :Type, Pa.
  
  (* Inhabitant of beta *)
  Theorem Beta_InHab: forall (B:Type) (H:Bot), B.
    intros B HB.
    unfold Bot in HB.
    apply HB with (Pa:=B).
    (* apply HB also works in this case *)
  Qed.

  (* So, if Bot appears in the hypothesis, it can prove any
  proposition *)
      

  Theorem Falsity: forall A B :Type, (A -> Bot) -> ( (A -> A) -> A) -> B.
    intros A B x f.
    unfold Bot in  x.
    (* inhabitant of A *)
    assert A.
    - apply f.
      intro.
      assumption.
    - apply x with (Pa := B).
      assumption.
  Qed.

  Definition Falsity' : forall A B :Type, (A -> Bot) -> ( (A -> A) -> A) -> B :=
    fun (A B:Type) (x: A -> Bot) (f: (A -> A) -> A) =>
      (x (f (fun (x:A) => x) ) ) B.
  
  
  (* DISJUNCTION IN L2 *)
  Definition OR (A B:Type): Type := forall C:Type, (A->C) -> (B->C) -> C.

  Theorem Or_intro: forall (A B: Type)  (x: A),   (OR A B).
    intros A B x.
    unfold OR.
    intro C.
    intro l.
    intro r.
    exact (l x).
  Qed.
  Print Or_intro.
  Definition Or_intro' : forall (A B: Type)  (x: A),   (OR A B):=
    fun (A B:Type) (x:A) =>
      fun (C:Type) =>
        fun(l:A->C) =>
          fun(r:B->C) =>
            l x.

  Theorem Or_elim : forall (A B D: Type)  (x:  OR A B) (f: A->D) (g: B->D), D.
    intros A B D x f g.
    assert ( (A->D)->(B->D)->D) by (exact (x D)).
    apply X.
    assumption.
    assumption.
  Qed.

  Theorem Or_elim' : forall (A B D: Type)  (x:  OR A B) (f: A->D) (g: B->D), D.
    intros A B D x f g.
    exact ( x D f g).
  Qed.

  (* Conjunction *)

  Definition CONJ (A B : Type):= forall C:Type, (A -> B -> C)-> C.
  Check CONJ.
  
  Theorem ConjElim1: forall (A B C:Type), CONJ A B -> A.
    intros.
    unfold CONJ in X.
    apply X. (* with C:= A*)
    intros.
    exact X0.
  Qed.

  Definition ConjElim2 : forall (A B C:Type) (HAB: CONJ A B),  B:=
    fun (A B C : Type) (HAB : CONJ A B) => HAB B (fun (HA : A) (HB : B) => HB).

  Theorem ConjIntro: forall (A B :Type), A -> B -> CONJ A B.
    intros A B HA HB.
    unfold CONJ.
    intros C.
    intros HC.
    exact( (HC HA) HB).
  Qed.
  

  (* How this is done in Coq? *)

  (* There is no inhabitant of FALSE *)

  Inductive MYFALSE := .
  Theorem F1: forall (X:Type), MYFALSE -> X.
    intros.
    (* H is an inhabitant of FALSE. But, by construction, this is impossible! *)
    inversion H.
  Qed.

  Print False. (* Note that the construction in Coq is the same *)

  (* A unique constructor that, given A and B build the conjunction of A and B *)
  Inductive MYAND (A B:Type):=
  | c_and : A -> B -> MYAND A B.

  Locate "/\".
  Print and.
  Print or.

  Theorem AndTest1: forall A B, MYAND A B -> A.
    intros HA HB HAB.
    (* there is only one way of building AND *)
    inversion HAB.
    exact X.
  Qed.

  Theorem AndTest2: forall A B, A -> B -> MYAND A B.
    intros A B HA HB.
    Check c_and.
    exact(c_and A B HA HB).
  Qed.
  
End Logic.

(*-----------------------------------*)
Inductive seq (CtLef : List) (F:Formula) : Prop:=
| init: forall F:Formula, In F CtL -> seq CtL F
| box : forall F LL, seq LL [F] -> seq (BOX LL) (box F)                                                     
                                       Fixpoint BOX (L:List):=
| [] => []
| F:: L' => (box F) :: BOX(L')
end.
                                       
(F1),....(F2) |-- (F)    
------------------------------
=B(F1),....B(F2) |-- B(F)
