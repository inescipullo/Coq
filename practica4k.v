Section Ej1.

(* list y bintree *)
Inductive list (A : Set) : Set :=
  nil : list A 
 | cons : A -> list A -> list A.

Inductive bintree (A : Set) : Set :=
  emptyTree : bintree A
 | addNode : A -> bintree A -> bintree A -> bintree A.

(* Array y Matrix *)
Inductive Array (A : Set) : nat -> Set :=
  emptyArray : Array A 0
 | addElem : forall n:nat, A -> Array A n -> Array A (S n).

(* leq (menor o igual) entre naturales *)
Inductive Leq : nat -> nat -> Prop :=
  leq0 : forall n:nat, Leq 0 n
 | leqS : forall (n m : nat), Leq n m -> Leq (S n) (S m).

(* eq_list de igualdad entre listas de cualquier tipo A a partir de la igualdad en
A *)
Inductive eq_list (A:Set) : list A -> list A -> Prop :=
  eqEmpty : eq_list A (nil A) (nil A)
 | eqCons : forall (h : A) (l1 l2 : list A), eq_list A l1 l2 -> eq_list A (cons A h l1) (cons A h l2).

(* sorted sobre listas que especifique que una lista esta ordenada
crecientemente según una relación de orden R *)
Inductive sorted (A:Set) (R: A -> A -> Prop) : list A -> Prop :=
  sortedNil : sorted A R (nil A)
 | sortedSing : forall (x:A), sorted A R (cons A x (nil A))
 | sortedGen : forall (x1 x2:A) (l : list A), R x1 x2 -> sorted A R (cons A x2 l) -> sorted A R (cons A x1 (cons A x2 l)). 

(* mirror entre árboles que especifique que un árbol es “espejo” del
otro (o sea, que tengan la misma estructura, pero con todos sus sub-árboles invertidos). *)
Inductive mirror (A:Set) : bintree A -> bintree A ->  Prop :=
  mirrorEmpty : mirror A (emptyTree A) (emptyTree A)
 | mirrorNode : forall (x:A) (tl tr:bintree A), mirror A tl tr -> mirror A (addNode A x tl tr) (addNode A x tr tl).

(* isomorfo entre árboles que especifique que un árbol es igual
estructuralmente a otro *)
Inductive isomorfo (A:Set) : bintree A -> bintree A -> Prop :=
  isoEmpty : isomorfo A (emptyTree A) (emptyTree A)
 | isoNode : forall (x1 x2:A) (tl1 tr1 tl2 tr2:bintree A), isomorfo A tl1 tl2 -> isomorfo A tr1 tr2  -> isomorfo A (addNode A x1 tl1 tr1) (addNode A x2 tl2 tr2).

(*  Gtree de los árboles generales (finitarios) cuyos nodos internos son de
un tipo y las hojas de otro (hay que definirlo mutuamente con las forestas) *)
Inductive Gtree (A B : Set) : Set :=
 node : A -> forest A B -> Gtree A B
with forest (A B:Set) : Set :=
| leaf : B -> forest A B
| addTree : Gtree A B -> forest A B -> forest A B.

End Ej1.

Section Ej2.

(* Implemente las funciones booleanas Or And Xor *)

Definition Or := 
  fun b1 b2: bool => match b1, b2 with
                      true, _ => true
                     | _, true => true
                     | false, false => false
  end.

Definition And :=
  fun b1 b2: bool => match b1, b2 with
                      true, true => true
                     | _, _ => false
  end.

Definition Not := 
  fun b:bool => match b with
                  true => false
                 | false => true
  end.

Definition Xor := 
  fun b1 b2: bool => match b1, b2 with
                      true, false => true
                     | false, true => true
                     | _, _ => false
  end.

(* is_nil decide si una lista es vacia *)

Definition is_nil (A:Set) :=
  fun (l: list A) => match l with
                    nil _ => true
                   | _ => false
  end.

End Ej2.

Section Ej3.

Fixpoint add (n m:nat) {struct n}: nat :=
  match n with
      0 => m
    | S k => S (add k m)
  end.

Fixpoint prod (n m:nat) {struct n}: nat :=
  match n with
    0 => 0
   | S 0 => m
   | S x => add m (prod x m)
  end.

Fixpoint pot (n m:nat) {struct m}: nat :=
  match m with
    0 => S 0
   | S k => prod n (pot n k)
  end.

Definition isZero :=
  fun n:nat => match n with
                  0 => true
                 | S x => false
  end.

Fixpoint leBool (n m:nat) {struct n}: bool :=
  match n, m with
    0, 0 => false
   | 0, S y => true
   | S x, 0 => false
   | S x, S y => leBool x y
  end. 

(*prod pot leBool*)


End Ej3.

Section Ej4.

Fixpoint length (A:Set) (l : list A) {struct l} : nat :=
  match l with
    nil _ => 0
   | cons _ x l1 => S (length A l1)
  end.

Check length.

Fixpoint append (A:Set) (l1 l2: list A) {struct l1} : list A :=
  match l1 with
    nil _ => l2
   | cons _ x tl1 => cons A x (append _ tl1 l2) 
  end.

Fixpoint reverse (A:Set) (l:list A) {struct l} : list A :=
  match l with
    nil _ => nil A
   | cons _ x tl => append A (reverse A tl) (cons A x (nil A))
  end.

  
(*
1. length: (forall A: Set, list A -> nat), que calcula la longitud de una lista.
2. append: (forall A: Set, list A -> list A -> list A), que concatena dos listas.
3. reverse: (forall A: Set, list A -> list A), que invierte una lista.
4. filter: (forall A: Set, (A -> bool) -> list A -> list A), que deja en una
lista los elementos que cumplen cierta propiedad.
5. map: (forall A B: Set, (A -> B) -> list A -> list B), que aplica una función
a todos los elementos de una lista.
6. exists_: (forall A: Set, (A -> bool) -> list A -> bool), que devuelve true
si y sólo si hay por lo menos un elemento en la lista que cumple cierta propiedad.
*)

End Ej4.

Section Ej8.

(*Asociatividad y conmutatividad del and y el or*)

Lemma ConmOr : forall (b1 b2:bool), Or b1 b2 = Or b2 b1.
Proof.
destruct b1; destruct b2.
- reflexivity.
- simpl. reflexivity.
- simpl. reflexivity.
- reflexivity.
Qed.

Lemma AsocOr : forall (b1 b2 b3: bool), Or (Or b1 b2) b3 = Or b1 (Or b2 b3).
Proof.
destruct b1; destruct b2; destruct b3; auto.
Qed.

Lemma ConmAnd : forall (b1 b2:bool), And b1 b2 = And b2 b1.
Proof.
destruct b1; destruct b2; auto.
Qed.

Lemma AsocAnd : forall (b1 b2 b3:bool), And (And b1 b2) b3 = And b1 (And b2 b3).
Proof.
destruct b1; destruct b2; destruct b3; auto.
Qed.

Lemma LAnd : forall a b : bool, And a b = true <-> a = true /\ b = true.
Proof.
intros. 
unfold iff.
split.
- destruct a; simpl; destruct b; intros; split;
  try repeat reflexivity || apply H.
- intros. destruct a; destruct b; simpl.
  * reflexivity.
  * elim H. intros. apply H1.
  * elim H. intros. apply H0.
  * elim H. intros. apply H1.
Qed.

Lemma LOr1 : forall a b : bool, Or a b = false <-> a = false /\ b = false.
Proof.
intros.
unfold iff.
split.
- destruct a; destruct b; auto.
    (*;simpl * intros. split. 
      apply H. 
      destruct b. apply H. reflexivity.
    * destruct b; intros; split.
      reflexivity. 
      apply H. 
      reflexivity. 
      reflexivity.  *)
- intros. destruct a; destruct b; simpl; elim H; auto. (*intros; try apply H0 || apply H1.*)
Qed.

Lemma LOr2 : forall a b : bool, Or a b = true <-> a = true \/ b = true.
Proof.
intros. unfold iff. split.
- destruct a; destruct b; auto.
- intros. destruct a.
  * simpl. reflexivity.
  * destruct b; simpl. 
      reflexivity.
      elim H; intros; apply H0.
Qed.

Lemma LXor : forall a b : bool, Xor a b = true <-> a <> b.
Proof.
intros. unfold iff. split.
- destruct a; destruct b; simpl; intros.
  absurd (false=true). discriminate. apply H.
  discriminate.
  discriminate.
  discriminate.
- intros.
  destruct a; destruct b; simpl; auto.
  * absurd (true <> true).
    unfold not. intros. apply H0. reflexivity.
    apply H.
  * absurd (false <> false).
    unfold not. intros. apply H0. reflexivity.
    apply H.
Qed.

Lemma LNot : forall b : bool, Not (Not b) = b.
Proof.
intros. destruct b; simpl; reflexivity.
Qed.
 
End Ej8.

Section Ej9.
End Ej9. 
 


