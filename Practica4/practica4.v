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


Section Ejercicio3.

Fixpoint sum (n m:nat) {struct n}: nat :=
  match n with
     0 => m
   | S k => S (sum k m)
  end.

Fixpoint prod (n m:nat) {struct n}: nat :=
  match n with
    0 => 0
   | S 0 => m
   | S x => sum m (prod x m)
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


End Ejercicio3.


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


Section Ejercicio9.

Lemma SumO: forall n: nat, sum n 0 = n /\ sum 0 n = n.
Proof.
induction n.
- split; compute; reflexivity.
- split; elim IHn; intros hi1 hi2; simpl.
  * rewrite hi1.
    reflexivity.
  * reflexivity.
Qed.

Lemma SumS: forall n m: nat, sum n (S m) = sum (S n) m.
Proof.
induction n.
- intro x; simpl; reflexivity.
- intro x.
  simpl.
  rewrite (IHn x).
  simpl.
  reflexivity.
Qed.

Lemma SumAsoc: forall n m p : nat, sum n (sum m p) = sum (sum n m) p.
Proof.
intros x y z.
induction x.
- simpl; reflexivity.
- simpl. elim IHx; reflexivity.
Qed.

Lemma SumConm: forall n m: nat, sum n m = sum m n.
Proof.
intros x y.
induction x; induction y.
- reflexivity.
- simpl. elim IHy. simpl. reflexivity.
- simpl. rewrite IHx. simpl. reflexivity.
- simpl. rewrite IHx.
  rewrite (SumS y x).
  reflexivity.
Qed.

End Ejercicio9.


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
length A (append A l m) = sum (length A l) (length A m).
Proof.
induction l.
- simpl. reflexivity.
- intros. simpl. rewrite IHl. reflexivity.
Qed.

Lemma add1_eq_S : forall (x:nat), sum x 1 = S x.
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

Lemma L7 : forall (A B : Set) (l m : list A) (f : A -> B), map A B f (append A l m) = append B (map A B f l) (map A B f m).
Proof.
intros.
induction l; simpl.
- reflexivity.
- elim IHl.
  reflexivity.
Qed.

Lemma L8 : forall (A : Set) (l m : list A) (P : A -> bool), filter A P (append A l m) = append A (filter A P l) (filter A P m).
Proof.
intros.
induction l.
- simpl; reflexivity.
- admit.
Admitted.

Lemma L9 : forall (A : Set) (l : list A) (P : A -> bool), filter A P (filter A P l) = filter A P l.
Proof.
intros.
induction l.
- simpl; reflexivity.
- simpl.
  destruct (P a).
  * simpl.
    rewrite IHl.
    destruct (P a).
    admit.
    admit.
  * rewrite IHl.
    reflexivity.
Admitted.

Lemma L10 : forall (A : Set) (l m n : list A), append A l (append A m n) = append A (append A l m) n.
Proof.
intros.
induction l; simpl.
- reflexivity.
- rewrite IHl.
  reflexivity.
Qed.


End Ejercicio12.


Section Ejercicio20.

(* 1 *)
Inductive ACom (A : Set) : nat -> Set :=
  singleton_ACom : array A 1 -> ACom A 0
| add_ACom : forall n : nat, ACom A (n-1) -> array A (pot 2 n) -> ACom A n.

(* 2 *)
Definition leaves_ACom (n:nat) : nat := pot 2 n.

(*
Fixpoint leaves_ACom_ind (A:Set) (n:nat) (t:ACom A n) : nat :=
  match t with
   | singleton_ACom _ => 1
*)

(* 3 *)
Axiom potO : forall n : nat, pot (S n) 0 = 1.
Axiom potS : forall m: nat, pot 2 (S m) = sum (pot 2 m) (pot 2 m).

Lemma LeavesACom : forall (n : nat), leaves_ACom n = pot 2 n.
Proof.
induction n.
- apply potO.
- apply potS.
Qed.

End Ejercicio20.


Section Ejercicio21.

(* 1 *)
Inductive AB (A : Set) : nat -> Set :=
  empty_AB : AB A 0
| add_AB : forall n m : nat, A -> AB A n -> AB A m -> AB A ((max n m) + 1).

(* 2 *)
Fixpoint camino (A : Set) (n : nat) (t : AB A n) : list A :=
  match t with
   | empty_AB _ => nil A
   | add_AB _ nl nr x l r => if leBool nr nl then cons A x (camino A nl l) 
                                             else cons A x (camino A nr r)
  end.

(* 3 *)
(*
Fixpoint max_nat (n m : nat) : nat :=
  match n,m with
   | 0, 0 => 0
   | 0, S m1 => S m1
   | S n1, 0 => S n1
   | S n1, S m1 => S (max_nat n1 m1)
  end.

Lemma leBoolmax : forall n m :nat, if leBool m n then max_nat n m = n else max_nat n m = m.
Proof.
intros.
induction (max_nat n m) eqn:H1.
- rewrite <- H1.
  destruct (leBool m n) eqn:H2.


induction n, m.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. 
  destruct (leBool m n) eqn:H1.
  simpl in IHn.
- induction n, m.
reflexivity.
*)

Axiom caso0 : forall m : nat, if leBool m 0 then max m 0 = 0 else max m 0 = m.



Lemma LengthCamino : forall (A : Set) (n : nat) (t : AB A n), length A (camino A n t) = n.
Proof.
intros.
induction t.
- simpl; reflexivity.
- simpl.
  destruct (leBool m n) eqn:H1.
  * simpl.
    rewrite IHt1.
    induction n.
    + apply (caso0 m).



End Ejercicio21.


