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

Definition opK (A: Set) (x: A) (y: A) := x.

Definition opS (A: Set) (f: A->A->A) (g: A->A) (x: A) := (f x) (g x).

(*
opI = def [x] x
opK = def [x][y] x
opS = def [f][g][x] ((f x) (g x))
*)

(* 5.2 
(* Para formalizar el siguiente lema, determine los tipos ?1 ... ?8 adecuados *)
Lemma e52 : forall A B : Set, opS ?1 ?2 ?3 (opK ?4 ?5) (opK ?6 ?7) = opI ?8.
Proof.

Qed.
*)

End Ejercicio5.


Section Ejercicio6.
Definition N := forall X : Set, X -> (X -> X) -> X.
Definition Zero (X : Set) (o : X) (f : X -> X) := o.
Definition Uno  (X : Set) (o : X) (f : X -> X) := f (Zero X o f).

(* 6.1 *)
Definition Dos (X: Set) (o: X) (f: X -> X) := f (Uno X o f).

(* 6.2 *)
Definition Succ (n: N) (X: Set) (o: X) (f: X -> X) := f (n X o f).

Lemma succUno : Succ Uno = Dos.
Proof.
compute.
reflexivity.
Qed.

(* 6.3 *)
Definition Plus (n m : N) : N := fun (X : Set) (o : X) (f : X -> X) => n X (m X o f) f.

Infix "_++_" := Plus (left associativity, at level 94).

Lemma suma1: (Uno _++_ Zero) = Uno.
Proof.
compute.
reflexivity.
Qed.

Lemma suma2: (Uno _++_ Uno) = Dos.
Proof.
compute.
reflexivity.
Qed.

(* 6.4 *)
Definition Prod (n m : N) : N := fun (X:Set) (o:X) (f:X->X) => m X o (fun y:X => n X y f).

Infix "**" := Prod (left associativity, at level 94).

(* 6.5 *)
Lemma prod1 : (Uno ** Zero) = Zero.
Proof.
compute.
reflexivity.
Qed.

Lemma prod2: (Uno ** Dos) = Dos.
Proof.
compute.
reflexivity.
Qed.

End Ejercicio6.


Section Ejercicio7.
(* 7.1 *)
Definition Bool := forall X: Set, X -> X -> X.
Definition t (X: Set) (t0: X) (f0: X) := t0.
Definition f (X: Set) (t0: X) (f0: X) := f0.

Check (t: Bool).
Check (f: Bool).

(* 7.2 *)
Definition If (b: Bool) (tb: Bool) (fb: Bool) (X: Set) (x y: X) := b X (tb X x y) (fb X x y).

(* 7.3 *)
Definition Not (b: Bool) (X: Set) (x y: X) := b X y x.

Lemma CorrectNot : (Not t) = f /\ (Not f) = t.
Proof.
split; compute; reflexivity.
Qed.

(* 7.4 *)
Definition And (a: Bool) (b: Bool) (X: Set) (x y: X) := a X (b X x y) (f X x y).

Definition And' (a: Bool) (b: Bool) (X: Set) (x y: X) := b X (a X x y) (f X x y).

(* 7.5 *)
Infix "&" := And (left associativity, at level 94).

Lemma CorrecAnd : (t & t) = t /\ (f & t) = f /\ (t & f) = f.
Proof.
split.
compute.
reflexivity.
split;compute;reflexivity.
Qed.

End Ejercicio7.



(* Ejercicio8 *)

Section ArrayNat.
Parameter ArrayNat : forall n:nat, Set.
Parameter empty    : ArrayNat 0.
Parameter add      : forall n:nat, nat -> ArrayNat n -> ArrayNat (n + 1).

(* 8.1 *)
Check ((add 0 (S 0) empty) : ArrayNat (S 0)).

(* 8.2 *)
(* Vector [0,0] *)
Check (add 1 0 (add 0 0 empty): ArrayNat 2).

(* Vector [0,1,0,1 *)
Check (add 3 0 (add 2 1 (add 1 0 (add 0 1 empty))): ArrayNat 4).

(* 8.3 *)
Parameter Concat : forall n1: nat, forall n2 :nat, ArrayNat n1 -> ArrayNat n2 -> ArrayNat (plus n1 n2). 

(* 8.4 *)
Parameter Zip : forall n: nat, ArrayNat n -> ArrayNat n -> (nat->nat->nat) -> ArrayNat n.

(* 8.5 *)
Check (ArrayNat: nat -> Set).

(* 8.6 *)
Parameter ArrayGen : Set -> nat -> Set.
Parameter emptyGen : forall X: Set, ArrayGen X 0.
Parameter addGen   : forall X: Set, forall n: nat, X -> ArrayGen X n -> ArrayGen X (n+1).
Parameter ZipGen   : forall X: Set, forall n: nat, ArrayGen X n -> ArrayGen X n -> (nat->nat->nat) -> ArrayGen X n.

(* 8.7 *)
Parameter ArrayBool : forall n: nat, ArrayGen bool n.

End ArrayNat.


Section Ejercicio9.
End Ejercicio9.


Section Ejercicio10.

Parameter Array : Set -> nat -> Set.
Parameter emptyA : forall X : Set, Array X 0.
Parameter addA : forall (X : Set) (n : nat), X -> Array X n -> Array X (S n).

Parameter Matrix : Set -> nat -> Set.
Parameter emptyM : forall (X : Set) (n : nat), Matrix (Array X n) 0.
Parameter addM : forall (X : Set) (m n : nat), Array X m -> Matrix (Array X m) n -> Matrix (Array X m) (S n).

Definition A1 := addA nat 2 1 (addA nat 1 0 (addA nat 0 0 (emptyA nat))). (*columna de longitud 3 con un 1 al inicio*)
Definition A2 := addA nat 2 2 (addA nat 1 2 (addA nat 0 0 (emptyA nat))).
Definition A3 := addA nat 2 3 (addA nat 1 3 (addA nat 0 3 (emptyA nat))).

Definition M1 := addM nat 3 0 A1 (emptyM nat 3).  (* matriz de una columna *)
Definition M2 := addM nat 3 1 A2 M1. (* matriz de dos columnas *) 
Definition M3 := addM nat 3 2 A3 M2. (* matriz de tres columnas *)

Check M3.

End Ejercicio10.

(*
Section Ejercicio11.
...
End Ejercicio11.


Section Ejercicio12.
...
End Ejercicio12.
*)

Section Ejercicio13.
Variable A B C: Set.

Lemma e13_1 : (A -> B -> C) -> B -> A -> C.
Proof.
exact (fun (f: A -> B -> C) (b: B) (a: A) => f a b).
Qed.

Lemma e13_2 : (A -> B) -> (B -> C) -> A -> C.
Proof.
exact (fun (f: A -> B) (g: B -> C) (a: A) => g (f a)).
Qed.

Lemma e13_3 : (A -> B -> C) -> (B -> A) -> B -> C.
Proof.
exact (fun (f: A -> B -> C) (g: B -> A) (b: B) => f (g b) b).
Qed.

End Ejercicio13.


Section Ejercicio14.
Variable A B C: Prop.

Lemma Ej314_1 : (A -> B -> C) -> A -> (A -> C) -> B -> C.
Proof.
  intros f a g b.
  exact (g a).
Qed.

Lemma Ej314_2 : A -> ~ ~ A.
Proof.
  unfold not.
  intros.
  exact (H0 H).
Qed.

Lemma Ej314_3 : (A -> B -> C) -> A -> B -> C.
Proof.
  exact (fun (f: A -> B -> C) => f).
Qed.

Lemma Ej314_4 : (A -> B) -> ~ (A /\ ~ B).
Proof.
  unfold not.
  intros.
  elim H0; intros.
  exact (H2 (H H1)).
Qed.

End Ejercicio14.



Section Ejercicio15.

Variable U : Set.
Variable e : U.
Variable A B : U -> Prop.
Variable P : Prop.
Variable R : U -> U -> Prop.

Lemma Ej315_1 : (forall x : U, A x -> B x) -> (forall x : U, A x) -> forall x : U, B x.
Proof.
  intros.
  exact (H x (H0 x)).
Qed.

Lemma Ej315_2 : forall x : U, A x -> ~ (forall x : U, ~ A x).
Proof.
  unfold not.
  intros.
  exact (H0 x H).
Qed.

Lemma Ej315_3 : (forall x : U, P -> A x) -> P -> forall x : U, A x.
Proof.
  exact (fun (H: (forall x : U, P -> A x)) (p: P) (x: U) => H x p).
Qed.

Lemma Ej315_4 : (forall x y : U, R x y) -> forall x : U, R x x.
Proof.
  exact (fun (H: (forall x y : U, R x y)) (x: U) => H x x).
Qed.

Lemma Ej315_5 : (forall x y: U, R x y -> R y x) -> forall z : U, R e z -> R z e.
Proof.
  exact (fun (H: (forall x y: U, R x y -> R y x)) (z: U) => H e z).
Qed.

End Ejercicio15.
