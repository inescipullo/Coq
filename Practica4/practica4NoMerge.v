Section Ejercicio1.

Inductive list (A:Set) : Set :=
  nil : list A
| cons : A -> list A -> list A.

Inductive bintree (A:Set) : Set :=
  empty_bintree : bintree A
| add_bintree : A -> bintree A -> bintree A -> bintree A.

Inductive array (A:Set) : nat -> Set :=
  empty_array : array A 0
| add_array : forall n:nat, A -> array A n -> array A (n+1).

Inductive matrix (A:Set) : nat -> nat -> Set :=
  one_col : forall n:nat, array A n -> matrix A 1 n
| add_col : forall m n:nat, array A n -> matrix A m n -> matrix A (S m) n.

Inductive leq : nat -> nat -> Prop :=
  leq0 : forall n:nat, leq 0 n
| leqS : forall n m:nat, leq n m -> leq (S n) (S m).

Inductive leq' : nat -> nat -> Prop :=
  leq0' : forall n:nat, leq' n n
| leqS' : forall n m:nat, leq' n m -> leq' (S n) (S m).

Inductive eq_list (A:Set) : list A -> list A -> Prop :=
  eq_nil : eq_list A (nil A) (nil A)
| eq_cons : forall h l1 l2, (eq_list A l1 l2) -> (eq_list A (cons A h l1) (cons A h l2)).

Inductive sorted (A:Set) (R:A->A->Prop) : list A -> Prop :=
  sorted_0 : sorted A R (nil A)
| sorted_1 : forall h, sorted A R (cons A h (nil A))
| sorted_S : forall h1 h2 l, (R h1 h2) -> sorted A R (cons A h2 l) -> sorted A R (cons A h1 (cons A h2 l)).

Inductive mirror (A:Set) : bintree A -> bintree A -> Prop :=
  mirror_empty : mirror A (empty_bintree A) (empty_bintree A)
| mirror_add : forall a l1 r1 l2 r2, 
            mirror A l1 r2 -> mirror A r1 l2 -> mirror A (add_bintree A a l1 r1) (add_bintree A a l2 r2).

End Ejercicio1.


Section Ejercicio2.

Definition Or (b1: bool) (b2: bool) : bool :=
  match b1, b2 with
   | true, _ => true
   | false, true => true
   | false, false => false
  end.

Definition And (b1: bool) (b2: bool) : bool :=
  match b1, b2 with
   | true, true => true
   | true, false => false
   | false, _ => false
  end.

Definition Not (b: bool) : bool :=
  match b with
   | true => false
   | false => true
  end.

Definition Xor (b1: bool) (b2: bool) : bool :=
  match b1, b2 with
   | true, true => false
   | true, false => true
   | false, true => true
   | false, false => false
  end.

Definition is_nil (A: Set) (l: list A) : bool :=
  match l with
   | nil _ => true
   | cons _ _ _ => false
  end.

End Ejercicio2.


Section Ejercicio4.

Fixpoint length (A: Set) (l: list A) {struct l} : nat :=
  match l with
  | nil _ => 0
  | cons _ _ l' => 1 + length A l'
  end.

Fixpoint append (A: Set) (l1: list A) (l2: list A) {struct l1} : list A :=
  match l1 with
   | nil _ => l2
   | cons _ h l1' => cons A h (append A l1' l2)
  end.

Fixpoint reverse (A: Set) (l: list A) : list A :=
  match l with
   | nil _ => nil A
   | cons _ h l' => append A (reverse A l') (cons A h (nil A))
  end.

Fixpoint filter (A: Set) (f: A -> bool) (l: list A) {struct l} : list A :=
  match l with
   | nil _ => nil A
   | cons _ h l' => if f h then cons A h (filter A f l') else (filter A f l')
  end.

Fixpoint map (A B: Set) (f: A -> B) (l: list A) {struct l} : list B :=
  match l with
   | nil _ => nil B
   | cons _ h l' => cons B (f h) (map A B f l')
  end.

Fixpoint exists_ (A: Set) (f: A -> bool) (l: list A) : bool :=
  match l with
   | nil _ => false
   | cons _ h l' => if f h then true else (exists_ A f l')
  end.

End Ejercicio4.


Section Ejercicio5.

Fixpoint inverse (A: Set) (t: bintree A) : bintree A :=
  match t with
   | empty_bintree _ => empty_bintree A
   | add_bintree _ x l r => add_bintree A x (inverse A r) (inverse A l)
  end.

End Ejercicio5.


Section Ejercicio6.

Definition listN := list nat.

Fixpoint member (x: nat) (l: listN) : bool :=
  match l with
   | nil _ => false
   | cons _ h l' => if Nat.eqb x h then true else member x l'
  end.

Fixpoint delete (x: nat) (l: listN) : listN :=
  match l with
   | nil _ => nil nat
   | cons _ h l' => if Nat.eqb x h then delete x l' else cons nat h (delete x l')
  end.

Fixpoint sorted_insertion (n: nat) (l: listN) : listN :=
  match l with
   | nil _ => nil nat
   | cons _ h l' => if Nat.leb n h then cons nat n (cons nat h l') else cons nat h (sorted_insertion n l')
  end.

Fixpoint insertion_sort (l: listN) : listN :=
  match l with
   | nil _ => nil nat
   | cons _ h l' => sorted_insertion h (insertion_sort l')
  end.

Fixpoint memberGen (A: Set) (x: A) (l: list A) (f: A -> A -> bool) : bool :=
  match l with
   | nil _ => false
   | cons _ h l' => if f x h then true else memberGen A x l' f
  end.

Fixpoint deleteGen (A: Set) (x: A) (l: list A) (f: A -> A -> bool) : list A :=
  match l with
   | nil _ => nil A
   | cons _ h l' => if f x h then deleteGen A x l' f else cons A h (deleteGen A x l' f)
  end.

Fixpoint sorted_insertionGen (A: Set) (n: A) (l: list A) (f: A -> A -> bool) : list A :=
  match l with
   | nil _ => nil A
   | cons _ h l' => if f n h then cons A n (cons A h l') else cons A h (sorted_insertionGen A n l' f)
  end.

Fixpoint insertion_sortGen (A: Set) (l: list A) (f: A -> A -> bool) : list A :=
  match l with
   | nil _ => nil A
   | cons _ h l' => sorted_insertionGen A h (insertion_sortGen A l' f) f
  end.

End Ejercicio6.


Section Ejercicio7.

Inductive Exp (A: Set) : Set :=
  | const : A -> Exp A
  | plus : Exp A -> Exp A -> Exp A
  | mult : Exp A -> Exp A -> Exp A
  | minus : Exp A -> Exp A.

Fixpoint eval_nat (e : Exp nat) : nat :=
  match e with
   | const _ x => x
   | plus _ x y => eval_nat x + eval_nat y
   | mult _ x y => eval_nat x * eval_nat y
   | minus _ x => eval_nat x
  end.

Fixpoint eval_bool (e : Exp bool) : bool :=
  match e with
   | const _ x => x
   | plus _ x y => Or (eval_bool x) (eval_bool y)
   | mult _ x y => And (eval_bool x) (eval_bool y)
   | minus _ x => Not (eval_bool x)
  end.

End Ejercicio7.


Section Ejercicio8.

Lemma conm_and : forall b1 b2: bool, And b1 b2 = And b2 b1.
Proof.
intros b1 b2.
destruct b1;
destruct b2;
compute;
reflexivity.
Qed.

Lemma conm_or : forall b1 b2: bool, Or b1 b2 = Or b2 b1.
Proof.
intros b1 b2.
destruct b1;
destruct b2;
compute;
reflexivity.
Qed.


End Ejercicio8.

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

Section Ejercicio11.

Lemma L1 : forall (A : Set) (l : list A), append A l (nil A) = l.
Proof.
induction l.
- simpl. reflexivity.
- simpl. rewrite IHl. reflexivity.
Qed.

Lemma L2 : forall (A : Set) (l : list A) (a : A), ~(cons A a l) = nil A.
Proof.
intros.
discriminate.
Qed.

Lemma L3 : forall (A : Set) (l m : list A) (a : A), 
cons A a (append A l m) = append A (cons A a l) m.
Proof.
induction l.
- intros. simpl. reflexivity.
- intros. simpl. reflexivity.
Qed.

Lemma L4 : forall (A : Set) (l m : list A),
length A (append A l m) = add (length A l) (length A m).
Proof.
induction l.
- simpl. reflexivity.
- intros. simpl. rewrite IHl. reflexivity.
Qed.

Lemma add1_eq_S : forall (x:nat), add x 1 = S x.
Proof.
intro x.
induction x.
- simpl. reflexivity.
- simpl.
  rewrite IHx.
  reflexivity.
Qed.

Lemma L5 : forall (A : Set) (l : list A), length A (reverse A l) = length A l.
Proof.
induction l.
- simpl. reflexivity.
- simpl. elim IHl. 
  rewrite (L4 A (reverse A l) (cons A a (nil A))).
  simpl. apply (add1_eq_S (length A (reverse A l))).
Qed.

End Ejercicio11.

Section Ejercicio12.

Lemma L7 : forall (A B : Set) (l m : list A) (f : A -> B),
map A B f (append A l m) = append B (map A B f l) (map A B f m).
Proof.
intros.
induction l.
- simpl. reflexivity.
- simpl. rewrite IHl. reflexivity.
Qed.

Lemma L8 : forall (A : Set) (l m : list A) (P : A -> bool),
filter A P (append A l m) = append A (filter A P l) (filter A P m).
Proof.
intros.
induction l.
- simpl. reflexivity.
- rewrite <- L3.
  simpl.
  case (P a).
  * simpl. rewrite IHl. reflexivity.
  * rewrite IHl. reflexivity.
Qed.

Lemma L9 : forall (A : Set) (l : list A) (P : A -> bool),
filter A P (filter A P l) = filter A P l.
Proof.
intros.
induction l.
- simpl. reflexivity.
- simpl.
  destruct (P a) eqn:H1.
  * simpl. rewrite H1. rewrite IHl. reflexivity.
  * rewrite IHl. reflexivity.
Qed.

Lemma L10 : forall (A : Set) (l m n : list A),
append A l (append A m n) = append A (append A l m) n.
Proof.
intros.
induction l.
* simpl. reflexivity.
* simpl. rewrite IHl. reflexivity.
Qed.

End Ejercicio12.

Section Ejercicio13.

Fixpoint filterMap (A B : Set) (P : B -> bool) (f : A -> B)
(l : list A) {struct l} : list B :=
   match l with
   | nil _ => nil B
   | cons _ a l1 =>
                   match P (f a) with
                   | true => cons B (f a) (filterMap A B P f l1)
                   | false => filterMap A B P f l1
                   end
 end.

Lemma FusionFilterMap :
 forall (A B : Set) (P : B -> bool) (f : A -> B) (l : list A),
 filter B P (map A B f l) = filterMap A B P f l.
Proof.
intros.
induction l.
- simpl. reflexivity.
- simpl. rewrite IHl. reflexivity.
Qed.

End Ejercicio13.

Section Ejercicio17.

(*
Defina inductivamente una relación binaria posfijo entre listas tal que 

una lista l1 se relaciona con una lista l2 
si y sólo si 
l1 es un posfijo de l2
(notación: l1 « l2)

Más formalmente, l1 « l2 sii l2 = l3++l1, para alguna lista l3, donde
++ representa la concatenación de listas (append).
*)

(*
Defina la función ++ entre listas de elementos de un tipo genérico y pruebe la corrección
de la relación posfijo del ejercicio anterior demostrando que:
* para todas listas l1, l2 y l3: Si l2 = l3++l1 entonces l1 « l2.
* para todas listas l1, l2: Si l1 « l2 entonces existe una lista l3 
  tal que l2 = l3++l1.
** Pruebe que para todas listas l1, l2 y l3 se cumple que l2 « l1++l2.
*)

Inductive posfijo(A : Set): list A -> list A -> Prop :=
  pos_append : forall (l1 l2 l3:list A), l2 = append A l3 l1 -> posfijo A l1 l2.

Fixpoint masmas (A: Set) (l1 l2 : list A) {struct l1} : list A :=
  match l1 with 
    | nil _ => l2
    | cons _ a l => cons A a (masmas A l l2)
  end.

Lemma EqApp: forall (A:Set) (l1 l2: list A), append A l1 l2 = masmas A l1 l2.
Proof.
intros.
induction l1.
* simpl. reflexivity.
* simpl. rewrite IHl1. reflexivity.
Qed.

Lemma P1 : forall (A : Set) (l1 l2 l3 : list A), 
l2 = masmas A l3 l1 -> posfijo A l1 l2.
Proof.
intros.
rewrite <- (EqApp A l3 l1) in H.
apply (pos_append A l1 l2 l3).
exact H.
Qed.

Lemma P2 : forall (A : Set) (l1 l2 : list A),
posfijo A l1 l2 -> exists (l3: list A), l2 = masmas A l3 l1.
Proof.
intros.
induction H.
exists l3.
exact H.
Qed.

Lemma P3: forall (A : Set) (l1 l2 : list A), 
posfijo A l2 (masmas A l1 l2).
Proof.
intros.
apply (pos_append A l2 (masmas A l1 l2) l1).
rewrite <- EqApp.
reflexivity.
Qed.

(*
Defina una función último que dada una lista de elementos de un tipo genérico 
retorne la lista que contiene a su último elemento. 

Si la lista parámetro es vacía, la función último
retorna la lista vacía. 
*) 
Fixpoint ultimo (A : Set) (l : list A) {struct l} : list A :=
  match l with
    | nil _ => nil A
    | cons _ a l1 => match l1 with 
                      | nil _ => cons A a (nil A)
                      | cons _ b l2 => ultimo A l1
                     end
  end.

(*
Pruebe que la función último de una lista es un posfijo de dicha lista.
*)
Fixpoint headAll (A : Set) (l: list A) {struct l} : list A :=
  match l with 
    | nil _ => nil A
    | cons _ a l1 => match l1 with
                      | nil _ => nil A
                      | cons _ b l2 => cons A a (headAll A l1)
                     end
  end.

Lemma headAllUlt : forall (A : Set) (l : list A), 
l = append A (headAll A l) (ultimo A l).
Proof.
intros.
induction l.
- simpl. reflexivity.
- induction l.
    * simpl. reflexivity.
    * simpl. simpl in IHl.
      rewrite IHl. reflexivity.
Qed.

Lemma ult_pos: forall (A : Set) (l : list A), 
posfijo A (ultimo A l) l.
Proof.
intros.
apply (pos_append A (ultimo A l) l (headAll A l)).
exact (headAllUlt A l).
Qed.

End Ejercicio17. 









