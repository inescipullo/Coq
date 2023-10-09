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
- destruct a.
  * simpl. destruct b. 
      intros. split; reflexivity.
      intros. split. reflexivity. apply H.
 * simpl. destruct b.
      intros 

End Ej8.
 


