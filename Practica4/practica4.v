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

Lemma asoc_and : forall b1 b2 b3: bool, And b1 (And b2 b3) = And (And b1 b2) b3.

Lemma asoc_or : forall b1 b2 b3: bool, Or b1 (Or b2 b3) = Or (Or b1 b2) b3.

Lemma LAnd : forall a b : bool, And a b = true <-> a = true /\ b = true.
Proof.
intros a b.
unfold iff; split; intro h. 
- destruct a; destruct b; simpl in h; split; try assumption; try reflexivity.
- elim h; intros a_val b_val.
  rewrite a_val; rewrite b_val.
  compute.
  reflexivity.
Qed.

Lemma

3. LOr1 : forall a b : bool, Or a b = false <-> a = false /\ b = false
4. LOr2 : forall a b : bool, Or a b = true <-> a = true \/ b = true
5. LXor : forall a b : bool, Xor a b = true <-> a <> b
6. LNot : forall b : bool, Not (Not b) = b 

End Ejercicio8.