Section Ejercicio1.
Variable A B C: Set.

Definition term1_1 : (A->A->A)->A->A := fun f x => f x x.
Check term1_1.

Lemma term1_1_tauto: (A->A->A)->A->A.
Proof.
tauto.
Qed. 

Lemma term1_1_exact: (A->A->A)->A->A.
Proof.
exact (fun f x => f x x).
Qed.

Definition term1_2 : (A->B)->(B->C)->A->B->C :=  fun f g x y => g (f x).
Check term1_2.

Lemma term1_2_tauto: (A->B)->(B->C)->A->B->C.
Proof.
tauto.
Qed. 

Lemma term1_2_exact: (A->B)->(B->C)->A->B->C.
Proof.
exact (fun f g x y => g (f x)).
Qed.

Definition term1_3 : (A->B)->(A->B->C)->A->C :=  fun f g x => g x (f x).
Check term1_3.

Lemma term1_3_tauto: (A->B)->(A->B->C)->A->C.
Proof.
tauto.
Qed. 

Lemma term1_3_exact: (A->B)->(A->B->C)->A->C.
Proof.
exact (fun f g x => g x (f x)).
Qed.

Definition term1_4 : (A->B)->((A->B)->C)->C :=  fun f g => g f.
Check term1_3.

Lemma term1_4_tauto: (A->B)->((A->B)->C)->C.
Proof.
tauto.
Qed. 

Lemma term1_4_exact: (A->B)->((A->B)->C)->C.
Proof.
exact (fun f g => g f).
Qed.

End Ejercicio1.


Section Ejercicio2.
Variable A B C: Set.

(* [x:A->B->C][y:A][z:B]((x y)z) *)
Definition term2_1: (A->B->C)->A->B->C := fun x y z => (x y) z.
Check term2_1.

(* [x:A->B][y:C->A][z:C](x (y z)) *)
Definition term2_2: (A->B)->(C->A)->C->B := fun x y z => x (y z).
Check term2_2.

(* [z:B] ([x:A->B->C][y:A](x y) z) *)
Definition term2_3: B->(A->B->C)->A->C := fun z => (fun x y => (x y) z).
Check term2_3.

(* ([x:A->A->B]x [y:A->A]y) *)
Definition term2_4: ((A->A)->B)->B := fun x => x (fun y => y).
Check term2_4.

End Ejercicio2.


Section Ejercicio3.
Variable A B C: Set.

Definition apply: (A->B)->A->B := fun f x => f x.
Check apply.

Definition applyGen: forall A B: Set, (A->B)->A->B := fun a b (f: a->b) (x:a) => f x.
Check applyGen.

Definition o: (A->B)->(B->C)->(A->C) := fun f g => fun x => g (f x).
Check o.

Definition oGen: forall A B C: Set, (A->B)->(B->C)->(A->C) := fun a b c (f: a->b) (g: b->c) => fun x: a => g (f x). 
Check oGen.

Definition twice: (A->A)->A->A := fun f x => f (f x).
Check twice.

Definition twiceGen: forall A: Set, (A->A)->A->A := fun a (f: a->a) (x: a) => f (f x).
Check twiceGen.

End Ejercicio3.


Section Ejercicio4.
Variable A: Set.

Definition id: A-> A := fun x:A => x.

Print oGen.

Theorem e4_1 : forall x:A, (oGen A A A id id) x = id x.
Proof.
intro x.
compute.
reflexivity.
Qed.

Theorem e4_2 : forall x:A, (oGen A A A id id) x = id x.
Proof.
intro x.
cbv delta beta.
reflexivity.
Qed.

Theorem e4_3 : forall x:A, (oGen A A A id id) x = id x.
Proof.
intro x.
cbv delta.
simpl. (* funciona porque oGen es constante transparente *)
reflexivity.
Qed.

End Ejercicio4.


Section Ejercicio5.

(* 5.1 *)
Definition opI (A : Set) (x : A) := x.

Definition opK ...

Definition opS ...

(* 5.2 *)
(* Para formalizar el siguiente lema, determine los tipos ?1 ... ?8 adecuados *)
Lemma e52 : forall A B : Set, opS ?1 ?2 ?3 (opK ?4 ?5) (opK ?6 ?7) = opI ?8.
Proof.

Qed.

End Ejercicio5.


Section Ejercicio6.
Definition N := forall X : Set, X -> (X -> X) -> X.
Definition Zero (X : Set) (o : X) (f : X -> X) := o.
Definition Uno  (X : Set) (o : X) (f : X -> X) := f (Zero X o f).

(* 6.1 *)
Definition Dos  ...

(* 6.2 *)
Definition Succ ...

Lemma succUno : Succ Uno = Dos.
Proof.

Qed.

(* 6.3 *)
Definition Plus (n m : N) : N
                := fun (X : Set) (o : X) (f : X -> X) => n X (m X o f) f.


Infix "++" := Plus (left associativity, at level 94).

Lemma suma1: (Uno ++ Zero) = Uno.
Proof.

Qed.

Lemma suma2: (Uno ++ Uno) = Dos.
Proof.

Qed.

(* 6.4 *)
Definition Prod (n m : N) : N
                := fun (X:Set) (o:X) (f:X->X) => m X o (fun y:X => n X y f).


Infix "**" := ...

(* 6.5 *)
Lemma prod1 : (Uno ** Zero) = Zero.
Proof.

Qed.

Lemma prod2: (Uno ** Dos) = Dos.
Proof.

Qed.

End Ejercicio6.


Section Ejercicio7.
(* 7.1 *)
Definition Bool := ...
Definition t    := ...
Definition f    := ...

(* 7.2 *)
Definition If ...

(* 7.3 *)
Definition Not ...

Lemma CorrecNot : (Not t) = f /\ (Not f) = t.
Proof.

Qed.

(* 7.4 *)
Definition And ...

Definition And' ...

(* 7.5 *)
Infix "&" := ...

Lemma CorrecAnd : (t & t) = t /\ (f & t) = f /\ (t & f) = f.
Proof.

Qed.

End Ejercicio7.



(* Ejercicio8 *)

Section ArrayNat.
Parameter ArrayNat : forall n:nat, Set.
Parameter empty    : ArrayNat 0.
Parameter add      : forall n:nat, nat -> ArrayNat n -> ArrayNat (n + 1).

(* 8.1 *)

(* 8.2 *)

(* 8.3 *)
Parameter Concat : ...

(* 8.4 *)
Parameter Zip : ...

(* 8.5 *)

(* 8.6 *)
Parameter ArrayGen : ...
Parameter emptyGen : ...
Parameter addGen   : ...
Parameter ZipGen   : ...

(* 8.7 *)
Parameter ArrayBool : ...

End ArrayNat.


Section Ejercicio9.
...
End Ejercicio9.


Section Ejercicio10.

Parameter Array : Set -> nat -> Set.
Parameter emptyA : forall X : Set, Array X 0.
Parameter addA : forall (X : Set) (n : nat), X -> Array X n -> Array X (S n).

Parameter Matrix : Set -> nat -> Set.
Parameter emptyM : ...
Parameter addM : ...

Definition M1 := ... (* matriz de una columna *)
Definition M2 := ... (* matriz de dos columnas *) 
Definition M3 := ... (* matriz de tres columnas *)

Check M3.

End Ejercicio10.


Section Ejercicio11.
...
End Ejercicio11.


Section Ejercicio12.
...
End Ejercicio12.


Section Ejercicio13.
Variable A B C: Set.

Lemma e13_1 : (A -> B -> C) -> B -> A -> C.
Proof.
  ...
Qed.

Lemma e13_2 : (A -> B) -> (B -> C) -> A -> C.
Proof.
  ...
Qed.

Lemma e13_3 : (A -> B -> C) -> (B -> A) -> B -> C.
Proof.
  ...
Qed.

End Ejercicio13.


Section Ejercicio14.
Variable A B C: Prop.

Lemma Ej314_1 : (A -> B -> C) -> A -> (A -> C) -> B -> C.
Proof.
  intros f a g b.
        ...
Qed.

Lemma Ej314_2 : A -> ~ ~ A.
Proof.
  unfold not.
  intros.
     ...
Qed.

Lemma Ej314_3 : (A -> B -> C) -> A -> B -> C.
Proof.
     ...
Qed.

Lemma Ej314_4 : (A -> B) -> ~ (A /\ ~ B).
Proof.
  unfold not.
  intros.
  elim H0; intros.
     ...
Qed.

End Ejercicio14.



Section Ejercicio15.

Variable U : Set.
Variable e : U.
Variable A B : U -> Prop.
Variable P : Prop.
Variable R : U -> U -> Prop.

Lemma Ej315_1 : (forall x : U, A x -> B x) -> (forall x : U, A x) ->
forall x : U, B x.
Proof.
  intros.
   ...
Qed.

Lemma Ej315_2 : forall x : U, A x -> ~ (forall x : U, ~ A x).
Proof.
  unfold not.
  intros.
  ...
Qed.

Lemma Ej315_3 : (forall x : U, P -> A x) -> P -> forall x : U, A x.
Proof.
    ...
Qed.

Lemma Ej315_4 : (forall x y : U, R x y) -> forall x : U, R x x.
Proof.
     ...
Qed.

Lemma Ej315_5 : (forall x y: U, R x y -> R y x) ->
                 forall z : U, R e z -> R z e.
Proof.
     ...
Qed.

End Ejercicio15.
