(* Entrega Práctico 4 - CFPTT *)
(* Alumnas: Cipullo, Inés - Sullivan, Katherine *)

Section Ejercicio1.

Inductive list (A:Set) : Set :=
  nil : list A
| cons : A -> list A -> list A.

Inductive array (A:Set) : nat -> Set :=
  empty_array : array A 0
| add_array : forall n:nat, A -> array A n -> array A (n+1).

Inductive leq : nat -> nat -> Prop :=
  leq0 : forall n:nat, leq 0 n
| leqS : forall n m:nat, leq n m -> leq (S n) (S m).

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


Section Ejercicio20.

(* 1 *)
Inductive ACom (A : Set) : nat -> Set :=
  singleton_ACom : array A 1 -> ACom A 0
| add_ACom : forall n : nat, array A (pot 2 n) -> ACom A (n-1) -> ACom A n.

(* 2 *)
Definition leaves_ACom (n:nat) : nat := pot 2 n.

Fixpoint h (A:Set) (n:nat) (t:ACom A n) : nat :=
  match t with
   | singleton_ACom _ _ => 1
   | add_ACom _ m _ t1  => sum m (h A (m-1) t1)
  end.

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
| add_AB : forall n m : nat, A -> AB A n -> AB A m -> AB A (S (max n m)).

(* 2 *)
Fixpoint camino (A : Set) (n : nat) (t : AB A n) : list A :=
  match t with
   | empty_AB _ => nil A
   | add_AB _ nl nr x l r => if leBool nr nl then cons A x (camino A nl l) 
                                             else cons A x (camino A nr r)
  end.

(* 3 *)
Lemma maxLeBool1 : forall n m, leBool m n = true -> max n m = n.
Proof.
induction n. intros.
- simpl. destruct m.
  -- reflexivity.
  -- simpl in H. discriminate.
- destruct m. 
  -- intros. simpl. reflexivity.
  -- intros.
     simpl. rewrite IHn.
        --- reflexivity.
        --- simpl in H. exact H.
Qed.

Lemma maxLeBool2 : forall n m, leBool m n = false -> max n m = m.
Proof.
induction n. intros.
- destruct m.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
- destruct m.
  -- simpl. intros. discriminate.
  -- simpl. intros. rewrite IHn.
      --- reflexivity.
      --- exact H.
Qed.

Lemma LengthCamino : forall (A : Set) (n : nat) (t : AB A n), length A (camino A n t) = n.
Proof.
intros.
induction t.
* simpl. reflexivity.
* simpl. 
  destruct (leBool m n) eqn:H.
  ** rewrite maxLeBool1.
     *** simpl.
         rewrite IHt1.
         reflexivity.
     *** exact H.
  ** rewrite maxLeBool2.
     *** simpl.
         rewrite IHt2.
         reflexivity.
     *** exact H.
Qed.

End Ejercicio21.