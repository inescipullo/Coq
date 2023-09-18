(* Entrega Práctico 3 - CFPTT *)
(* Alumnas: Cipullo, Inés - Sullivan, Katherine *)


(* Definición necesaria para el desarrollo del ejercicio 4 *)
Definition oGen: forall A B C: Set, (A->B)->(B->C)->(A->C) := fun a b c (f: a->b) (g: b->c) => fun x: a => g (f x). 
Check oGen.


(* Ejercicio 4 *)
Section Ejercicio4.
Variable A: Set.

Definition id: A-> A := fun x:A => x.

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


(* Ejercicio 5 *)
Section Ejercicio5.

(* 5.1 *)
Definition opI (A : Set) (x : A) := x.

Definition opK (A : Set) (B : Set) (x : A) (y : B) := x.

Definition opS (A : Set) (B: Set) (C : Set) (f : A -> B -> C) (g : A -> B) (x : A) := (f x) (g x).

(* 5.2 *)
(* Para formalizar el siguiente lema, determine los tipos ?1 ... ?8 adecuados*) 
Lemma e52 : forall A B : Set, opS A (B->A) A (opK A (B->A)) (opK A B) = opI A.
Proof.
cbv delta beta.
reflexivity.
Qed.

End Ejercicio5.


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
Parameter Concat : forall (n1 n2 : nat), ArrayNat n1 -> ArrayNat n2 -> ArrayNat (plus n1 n2). 

(* 8.4 *)
Parameter Zip : forall n: nat, ArrayNat n -> ArrayNat n -> (nat->nat->nat) -> ArrayNat n.

(* 8.5 *)
Check (ArrayNat: nat -> Set).

(* 8.6 *)
Parameter ArrayGen : Set -> nat -> Set.
Parameter emptyGen : forall X: Set, ArrayGen X 0.
Parameter addGen   : forall (X: Set) (n: nat), X -> ArrayGen X n -> ArrayGen X (n+1).
Parameter ZipGen   : forall (X: Set) (n: nat), ArrayGen X n -> ArrayGen X n -> (nat->nat->nat) -> ArrayGen X n.

(* 8.7 *)
Parameter ArrayBool : forall n: nat, ArrayGen bool n.

End ArrayNat.


(* Ejercicio 10 *)
Section Ejercicio10.

Parameter Array : Set -> nat -> Set.
Parameter emptyA : forall X : Set, Array X 0.
Parameter addA : forall (X : Set) (n : nat), X -> Array X n -> Array X (S n).

Parameter Matrix : Set -> nat -> Set.
Parameter emptyM : forall (X : Set), Matrix X 0.
Parameter addM : forall (X : Set) (n : nat), Array X (S n) -> Matrix X n -> Matrix X (S n).

Definition A1 := addA nat 0 1 (emptyA nat).
Definition A2 := addA nat 1 2 (addA nat 0 2 (emptyA nat)).
Definition A3 := addA nat 2 3 (addA nat 1 3 (addA nat 0 3 (emptyA nat))).

Definition M1 := addM nat 0 A1 (emptyM nat).  (* matriz de una columna *)
Definition M2 := addM nat 1 A2 M1. (* matriz de dos columnas *) 
Definition M3 := addM nat 2 A3 M2. (* matriz de tres columnas *)

Check M3.

End Ejercicio10.


(* Ejercicio 11 *)
Section Ejercicio11.

Parameter ABNat : forall n : nat, Set.

Parameter emptyAB : ABNat 0.

Parameter addAB : forall n : nat, ArrayNat (Nat.pow 2 n) -> ABNat n -> ABNat (S n). (* A un árbol de altura n le paso como array el nuevo nivel *)

Definition AB2 := addAB 1 (add 1 7 (add 0 7 empty)) (addAB 0 (add 0 3 empty) (emptyAB)).
Check AB2.

Parameter GenAB : Set -> nat -> Set.
Parameter GenEmptyAB : forall X : Set, GenAB X 0.
Parameter GenAddAB : forall (X:Set) (n:nat), Array X (Nat.pow 2 n) -> GenAB X n -> GenAB X (S n).

End Ejercicio11.


(* Ejercicio 12 *)
Section Ejercicio12.

Parameter  AVLNat : forall n : nat, Set.
Parameter emptyAVL : AVLNat 0.
(* No se piensa en agregar un elemento al árbol, sino en construir un árbol. Se pasa la raíz,
el árbol izq y el árbol der *)
Parameter addAVL1 : forall n:nat, nat -> AVLNat n -> AVLNat (plus n 1) -> AVLNat (S (S n)).
Parameter addAVL2 : forall n:nat, nat -> AVLNat n -> AVLNat n -> AVLNat (S n).
Parameter addAVL3 : forall n:nat, nat -> AVLNat n -> AVLNat (minus n 1) -> AVLNat (S n).

Definition LeftLeaf := addAVL2 0 3 emptyAVL emptyAVL.

Definition AVL2 := addAVL3 1 10 LeftLeaf emptyAVL.
Check AVL2.

Parameter GenAVL : forall n : nat, Set.
Parameter GenEmptyAVL : AVLNat 0.
Parameter GenAddAVL1 : forall (n:nat) (X:Set), X -> AVLNat n -> AVLNat (plus n 1) -> AVLNat (S (S n)).
Parameter GenAddAVL2 : forall (n:nat) (X:Set), X -> AVLNat n -> AVLNat n -> AVLNat (S n).
Parameter GenAddAVL3 : forall (n:nat) (X:Set), X -> AVLNat n -> AVLNat (minus n 1) -> AVLNat (S n).

End Ejercicio12.


(* Ejercicio 14 *)
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
  exact (fun (H : A -> B -> C) => H).
Qed.

Lemma Ej314_4 : (A -> B) -> ~ (A /\ ~ B).
Proof.
  unfold not.
  intros.
  elim H0; intros.
  exact (H2 (H H1)).
Qed.

End Ejercicio14.


(* Ejercicio 15 *)
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
  exact (fun (H1 : forall x : U, P -> A x) (H2 : P) (H3 : U) => H1 H3 H2).
Qed.

Lemma Ej315_4 : (forall x y : U, R x y) -> forall x : U, R x x.
Proof.
  exact (fun (H1 : forall x y : U, R x y) (H2 : U) => H1 H2 H2).
Qed.

Lemma Ej315_5 : (forall x y: U, R x y -> R y x) -> forall z : U, R e z -> R z e.
Proof.
  exact (fun (H1 : forall x y: U, R x y -> R y x) (z : U) => H1 e z).
Qed.

End Ejercicio15.

