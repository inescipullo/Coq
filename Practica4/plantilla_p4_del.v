
Section Ejercicio1.

Inductive list (A: Set): Set :=
  | nil: list A
  | cons: A -> list A -> list A.

Inductive binTree (A: Set): Set :=
  | empty_bt: binTree A
  | add_bt: A -> binTree A -> binTree A -> binTree A.
(* Información en los nodos internos *)

Inductive array (A:Set): nat -> Set :=
  | empty_a : array A 0
  | add_a : forall n:nat, A -> array A n -> array A (S n).

Inductive matrix (A:Set): nat -> nat -> Set :=
  | one_col : forall n:nat, array A n -> matrix A 1 n
  | extend_col : forall m n:nat, matrix A m n -> array A n -> matrix A (S m) n.

Inductive leq: nat -> nat -> Prop :=
  | leq0 : forall n:nat, leq 0 n
  | leqS : forall n m:nat, leq n m -> leq (S n) (S m).

Inductive leq_2: nat -> nat -> Prop :=
  | leq0_2 : forall n:nat, leq_2 n n
  | leqS_2 : forall n m:nat, leq n m -> leq_2 n (S m).

Inductive eq_list (A: Set): list A -> list A -> Prop :=
  | eq_list_nil: eq_list _ (nil _) (nil _)
  | eq_list_cons: forall (a: A) l l',
      eq_list _ l l' -> eq_list _ (cons _ a l) (cons _ a l').

(* Set implicit arguments *)
(* ( (A:=A)  para explicitar ) *)

Parameter R: forall (A: Set), A -> A -> Prop.
Inductive sorted (A: Set) R: list A -> Prop :=
  | sorted_nil: sorted A R (nil A)
  | sorted_one: forall (a:A), sorted A R (cons A a (nil A))
  | sorted_cons: forall (a b: A) l,
      R A a b -> sorted A R (cons A b l) ->
        sorted A R (cons A a (cons A b l)).

Inductive mirror (A: Set): binTree A -> binTree A -> Prop :=
  | mirror_nil: mirror A (empty_bt A) (empty_bt A)
  | mirror_bt: forall (a:A) l1 r1 l2 r2,
      mirror _ l1 r2 -> mirror _ r1 l2 ->
        mirror _ (add_bt _ a l1 r1) (add_bt _ a l2 r2).

Inductive isomorfo (A: Set): binTree A -> binTree A -> Prop :=
  | isomorfo_nil: isomorfo A (empty_bt A) (empty_bt A)
  | isomorfo_bt: forall (a b:A) l1 r1 l2 r2,
      isomorfo _ l1 l2 -> isomorfo _ r1 r2 ->
        isomorfo _ (add_bt _ a l1 r1) (add_bt _ b l2 r2).

Inductive gtree (A: Set): Set :=
  | node_gtree: A -> forest A -> gtree A
with
  forest (A: Set): Set :=
    | empty_f: forest A
    | add_f: gtree A -> forest A -> forest A.

End Ejercicio1.

Section Ejercicio2.

Definition bool_not(b: bool): bool :=
  match b with
      | true => false
      | false => true
  end.

Definition bool_xor(b1 b2: bool): bool :=
  match b1, b2 with
      | true, false => true
      | false, true => true
      | _, _ => false
  end.

Definition bool_or(b1 b2: bool): bool :=
  match b1, b2 with
      | true, _ => true
      | _, true => true
      | false, false => false
  end.

Definition bool_and(b1 b2: bool): bool :=
  match b1, b2 with
      | false, _ => false
      | _, false => false
      | _, _ => true
  end.

Definition is_nil (a: Set) (l: list a): bool :=
  match l with
      | nil _ => true
      | cons _ _ _ => false
  end.

End Ejercicio2.

Section Ejercicio3.

(* sum: nat -> nat -> nat. *)
Fixpoint suml (n m: nat) {struct n}: nat :=
  match n with
    | 0 => m
    | S n' => S (suml n' m)
  end.

(* {struct m} argumento sobre el que se hace induccion *)
Fixpoint sumr (n m: nat) {struct m}: nat :=
  match m with
    | 0 => n
    | S m' => S (sumr n m')
  end.

Fixpoint prod (n m: nat) {struct n}: nat :=
  match n with
    | 0 => 0
    | S n' => suml (prod n' m) m
  end.

Fixpoint pot (n m: nat) {struct m}: nat :=
  match m with
    | 0 => 1
    | S m' => prod (pot n m') n
  end.

Fixpoint le_bool (n m: nat) {struct n}: bool :=
  match n with
    | 0 => true
    | S n' => match m with
        | 0 => false
        | S m' => le_bool n' m'
        end
  end.

End Ejercicio3.

Section Ejercicio4.

Fixpoint llength (a: Set) (l: list a) {struct l}: nat :=
  match l with
    | nil _ => 0
    | cons _ _ l' => S (llength a l')
  end.
(* Print llength. *)

Fixpoint append (a: Set) (l1 l2: list a) {struct l1}: list a :=
  match l1 with
    | nil _ => l2
    | cons _ x l1' => cons _ x (append _ l1' l2)
  end.
(* Print append. *)

Fixpoint reverse (a: Set) (l: list a) {struct l}: list a :=
  match l with
    | nil _ => nil _
    | cons _ x l' => append _ (reverse _ l') (cons _ x (nil _))
  end.
(* Print reverse. *)

Fixpoint lfilter (a: Set) (p: a -> bool) (l: list a) {struct l}: list a :=
  match l with
    | nil _ => nil _
    | cons _ x l' =>
    match (p x) with
      | true => (cons _ x (lfilter _ p l'))
      | false => lfilter _ p l'
    end
  end.
(* Print lfilter. *)

Fixpoint lmap (a b: Set) (f: a -> b) (l: list a) {struct l}: list b :=
  match l with
    | nil _ => nil _
    | cons _ x l' => cons _ (f x) (lmap _ _ f l')
  end.
(* Print lmap. *)

Fixpoint exists_ (a: Set) (p: a -> bool) (l: list a) {struct l}: bool :=
  match l with
    | nil _ => false
    | cons _ x l' =>
  if (p x) then true
           else exists_ _ p l'
  end.
(* Print exists_. *)

Fixpoint exists_2 (a: Set) (p: a -> bool) (l: list a) {struct l}: bool :=
  match l with
    | nil _ => false
    | cons _ x l' => bool_or (p x) (exists_2 _ p l')
  end.

End Ejercicio4.

Section Ejercicio5.

Fixpoint inverse (a: Set) (t: binTree a) {struct t}: binTree a :=
  match t with
    | empty_bt _ => empty_bt _
    | add_bt _ x l r =>
        add_bt _ x (inverse _ r) (inverse _ l)
  end.
(* Print inverse. *)

Fixpoint int_tree_size (a: Set) (t: gtree a): nat :=
  match t with | (node_gtree _ _ f) => S (int_forest_size  _ f)
  end
with int_forest_size (a: Set) (f: forest a): nat :=
  match f with
    | empty_f _ => 0
    | add_f _ t x => plus (int_tree_size _ t) (int_forest_size _ x)
  end.

Fixpoint ext_tree_size (a: Set) (t: gtree a) : nat :=
  match t with | (node_gtree _ _ f) => ext_forest_size _ f
  end
with ext_forest_size (a: Set) (f: forest a): nat :=
  match f with
    | empty_f _ => 1
    | add_f _ t x => plus (ext_tree_size _ t) (ext_forest_size _ x)
  end.

Definition ext_le_int (a: Set) (t: gtree a): bool :=
  Nat.leb (ext_tree_size _ t) (int_tree_size _ t).

End Ejercicio5.

Section Ejercicio6.

Definition listN:= list nat.

Fixpoint member (l: listN) (n: nat) {struct l}: bool :=
  match l with
    | nil _ => false
    | cons _ x l' => if Nat.eqb x n
        then true
        else member l' n
  end.

Fixpoint delete (l: listN) (n: nat) {struct l}: list nat :=
  match l with
    | nil _ => nil _
    | cons _ x l' => if Nat.eqb x n
        then delete l' n
        else cons _ x (delete l' n)
  end.

Fixpoint insert_sort (l: listN) (n: nat) {struct l}: list nat :=
  match l with
    | nil _ => cons _ n (nil _)
    | cons _ x l' => if le_bool x n
        then cons _ x (insert_sort l' n)
        else cons _ n (insert_sort l' x)
  end.

Fixpoint insertion_sort (l: list nat) {struct l}: list nat :=
  match l with
    | nil _ => nil _
    | cons _ x l' => insert_sort (insertion_sort l') x
  end.

Fixpoint member_g (a: Set) (l: list a) (y: a) (eq: a -> a -> bool) {struct l}: bool :=
  match l with
    | nil _ => false
    | cons _ x l' => if eq x y
        then true
        else member_g _ l' y eq
  end.

Fixpoint delete_g (a: Set) (l: list a) (n: a) (eq: a -> a -> bool) {struct l}: list a :=
  match l with
    | nil _ => nil _
    | cons _ x l' => if eq x n
        then delete_g _ l' n eq
        else cons _ x (delete_g _ l' n eq)
  end.

Fixpoint insert_sort_g (a: Set) (l: list a) (n: a) (leq: a -> a -> bool) {struct l}: list a :=
  match l with
    | nil _ => cons _ n (nil _)
    | cons _ x l' => if leq x n
        then cons _ x (insert_sort_g _ l' n leq)
        else cons _ n (insert_sort_g _ l' x leq)
  end.

Fixpoint insertion_sort_g (a: Set) (l: list a) (leq: a -> a -> bool) {struct l}: list a :=
  match l with
    | nil _ => nil _
    | cons _ x l' => insert_sort_g _ (insertion_sort_g _ l' leq) x leq
  end.

End Ejercicio6.

Section Ejercicio7.

Inductive Exp (a: Set): Set :=
  | const: a -> Exp a
  | sum_exp: Exp a -> Exp a -> Exp a
  | prod_exp: Exp a -> Exp a -> Exp a
  | op_exp: Exp a -> Exp a.

(* intexp ::= - intexp
  | intexp + intexp
  | intexp * intexp *)

Fixpoint eval_nat (e: Exp nat): nat :=
  match e with
    | const _ a => a
    | sum_exp _ a b => (eval_nat a) + (eval_nat b)
    | prod_exp _ a b => (eval_nat a) * (eval_nat b)
    | op_exp _ a => eval_nat a
  end.

Fixpoint eval_bool (e: Exp bool): bool :=
  match e with
    | const _ a => a
    | sum_exp _ a b => bool_or (eval_bool a) (eval_bool b)
    | prod_exp _ a b => bool_and (eval_bool a) (eval_bool b)
    | op_exp _ a => bool_not (eval_bool a)
  end.

End Ejercicio7.

Section Ejercicio8.

Lemma and_assoc: forall a b: bool, bool_and a b = bool_and b a.
Proof.
intros x y.
case x; case y; compute; reflexivity.
Qed.

Lemma or_assoc: forall a b: bool, bool_or a b = bool_or b a.
Proof.
intros x y.
case x; case y; compute; reflexivity.
Qed.

Lemma LAnd: forall a b: bool, bool_and a b = true <-> a = true /\ b = true.
Proof.
intros x y.
unfold iff; split; intro h.
- destruct x; destruct y; simpl in h; split; try reflexivity; try discriminate.
- elim h; intros x_eq_true y_eq_true.
  rewrite x_eq_true; rewrite y_eq_true.
  compute; reflexivity.
Qed.

Lemma LOr1: forall a b: bool, bool_or a b = false <-> a = false /\ b = false.
Proof.
intros x y.
unfold iff; split; intro h.
- destruct x; destruct y; simpl in h; split; try reflexivity; try discriminate.
- elim h; intros x_eq_false y_eq_false.
  rewrite x_eq_false; rewrite y_eq_false.
  compute; reflexivity.
Qed.

Lemma LOr2: forall a b: bool, bool_or a b = true <-> a = true \/ b = true.
Proof.
intros x y.
unfold iff; split; intro h.
- destruct x; simpl in h.
  * left. reflexivity.
  * destruct y.
    + right. reflexivity.
    + left. assumption.
- elim h; intros; rewrite H; compute.
  * reflexivity.
  * case x; reflexivity.
Qed.

Lemma LXor: forall a b: bool, bool_xor a b = true <-> a <> b.
Proof.
intros x y.
unfold iff; split; intro h.
- destruct x; destruct y; discriminate.
- destruct x; destruct y; compute; try reflexivity; unfold not in h; elim h; reflexivity.
Qed.

Lemma LNot: forall b: bool, bool_not (bool_not b) = b.
Proof.
destruct b; compute; reflexivity.
Qed.

End Ejercicio8.

Section Ejercicio9.

Lemma SumO: forall n: nat, suml n 0 = n /\ suml 0 n = n.
Proof.
induction n.
- split; compute; reflexivity.
- split; elim IHn; intros hi1 hi2; simpl.
  * rewrite hi1.
    reflexivity.
  * reflexivity.
Qed.

Lemma SumS: forall n m: nat, suml n (S m) = suml (S n) m.
Proof.
induction n; intro x; simpl.
- reflexivity.
- rewrite (IHn x).
  simpl.
  reflexivity.
Qed.

Lemma SumAsoc: forall n m p : nat, suml n (suml m p) = suml (suml n m) p.
Proof.
intros x y z.
induction x.
- simpl; reflexivity.
- simpl. elim IHx; reflexivity.
Qed.

Lemma SumConm: forall n m: nat, suml n m = suml m n.
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

Section Ejercicio10.

Lemma ProdConm: forall n m : nat, prod n m = prod m n.
Proof.
induction n; induction m.
- reflexivity.
- simpl. elim IHm. simpl. reflexivity.
- simpl. rewrite IHn. simpl. reflexivity.
- simpl. rewrite <- IHm.
  rewrite (IHn (S m)).
  simpl. rewrite (IHn m).
  rewrite <- (SumAsoc (prod m n) m (S n)).
  rewrite <- (SumAsoc (prod m n) n (S m)).
  rewrite (SumConm n (S m)).
  rewrite (SumS m n).
  reflexivity.
Qed.

Lemma ProdDistr: forall n m p: nat, prod (suml n m) p = suml (prod n p) (prod m p).
Proof.
induction n; intros m p.
- simpl. reflexivity.
- simpl. rewrite IHn.
  rewrite <- (SumAsoc (prod n p) (prod m p) p).
  rewrite <- (SumAsoc (prod n p) p (prod m p)).
  rewrite (SumConm p (prod m p)).
  reflexivity.
Qed.

Lemma ProdAsoc: forall n m p: nat, prod n (prod m p) = prod (prod n m) p.
Proof.
induction n; intros m p.
- simpl. reflexivity.
- simpl. rewrite (IHn m p).
  rewrite <- ProdDistr.
  reflexivity.
Qed.

Lemma ProdDistl: forall n m p: nat, prod n (suml m p) = suml (prod n m) (prod n p).
Proof.
induction n; intros m p.
- simpl. reflexivity.
- simpl. rewrite IHn.
  rewrite <- (SumAsoc (prod n m) (prod n p) (suml m p)).
  rewrite (SumConm m p).
  rewrite (SumAsoc (prod n p) p m).
  rewrite (SumConm (suml (prod n p) p) m).
  rewrite (SumAsoc (prod n m) m (suml (prod n p) p)).
  reflexivity.
Qed.

End Ejercicio10.

Section Ejercicio11.

Lemma L1 : forall (A : Set) (l : list A), append A l (nil A) = l.
Proof.
induction l; simpl.
- reflexivity.
- rewrite IHl. reflexivity.
Qed.

Lemma L2 : forall (A : Set) (l : list A) (a : A), ~(cons A a l) = nil A.
Proof.
induction l; intros e; discriminate.
Qed.

Lemma L3 : forall (A : Set) (l m : list A) (a : A),
cons A a (append A l m) = append A (cons A a l) m.
Proof.
induction l; intros m e; simpl.
- reflexivity.
- rewrite IHl. reflexivity.
Qed.

Lemma L4 : forall (A : Set) (l m : list A),
llength A (append A l m) = suml (llength A l) (llength A m).
Proof.
induction l; intros m; simpl.
- reflexivity.
- rewrite IHl. reflexivity.
Qed.

Lemma L5 : forall (A : Set) (l : list A), llength A (reverse A l) = llength A l.
Proof.
induction l; simpl.
- reflexivity.
- rewrite L4.
  rewrite IHl.
  simpl.
  rewrite (SumConm (llength A l) 1).
  simpl.
  reflexivity.
Qed.

End Ejercicio11.

Section Ejercicio12.

Lemma L7 : forall (A B : Set) (l m : list A) (f : A -> B),
lmap A B f (append A l m) = append B (lmap A B f l) (lmap A B f m).
Proof.
induction l; intros m f; simpl.
- reflexivity.
- rewrite IHl. reflexivity.
Qed.

Lemma L8 : forall (A : Set) (l m : list A) (P : A -> bool),
lfilter A P (append A l m) = append A (lfilter A P l) (lfilter A P m).
Proof.
induction l; intros m p; simpl.
- reflexivity.
- rewrite IHl.
  case (p a).
  * simpl. reflexivity.
  * reflexivity.
Qed.

Lemma L9 : forall (A : Set) (l : list A) (P : A -> bool),
lfilter A P (lfilter A P l) = lfilter A P l.
Proof.
induction l; intros p; simpl.
- reflexivity.
- case_eq (p a); intro p_value. (* Alternativamente a case_eq: destruct (p a) eqn:p_value *)
  * simpl. rewrite p_value. rewrite IHl. reflexivity.
  * rewrite IHl. reflexivity.
Qed.

Lemma L10 : forall (A : Set) (l m n : list A),
append A l (append A m n) = append A (append A l m) n.
Proof.
induction l; intros m n; simpl.
- reflexivity.
- rewrite IHl. reflexivity.
Qed.

End Ejercicio12.

Section Ejercicio13.

Fixpoint filterMap (A B : Set) (P : B -> bool) (f : A -> B)
(l : list A) {struct l} : list B :=
  match l with
    | nil _ => nil B
    | cons _ a l' =>
    match P (f a) with
      | true => cons _ (f a) (filterMap _ _ P f l')
      | false => filterMap _ _ P f l'
  end
end.

Lemma FusionFilterMap :
forall (A B : Set) (P : B -> bool) (f : A -> B) (l : list A),
lfilter B P (lmap A B f l) = filterMap A B P f l.
Proof.
induction l; simpl.
- reflexivity.
- case_eq (P (f a)); intro p_f_value; rewrite IHl; reflexivity.
Qed.

End Ejercicio13.

Section Ejercicio14.

Lemma mirror_inverse: forall (A: Set) (t: binTree A), mirror A (inverse A t) t.
Proof.
induction t; simpl; constructor; [exact IHt2 | exact IHt1].
Qed.

(* Menos factorizada para que sea más legible: *)
(* Lemma mirror_inverse2: forall (A: Set) (t: binTree A), mirror A (inverse A t) t.
Proof.
induction t; simpl.
- constructor.
- constructor.
  * exact IHt2.
  * exact IHt1.
Qed. *)

End Ejercicio14.

Section Ejercicio15.

Lemma iso_id: forall (A: Set) (t: binTree A), isomorfo _ t t.
Proof.
induction t; simpl; constructor; [exact IHt1 | exact IHt2].
Qed.

Lemma iso_sim: forall (A: Set) (t u: binTree A), isomorfo _ t u -> isomorfo _ u t.
Proof.
intros A t u h.
induction h.
- exact (isomorfo_nil _).
- exact (isomorfo_bt _ b a l2 r2 l1 r1 IHh1 IHh2).
Qed.
(* Probar alternativamente con inducción sobre el árbol *)

Lemma iso_inv1: forall (A: Set) (t u: binTree A), isomorfo _ t u -> t = empty_bt _ -> u = empty_bt _.
Proof.
intros.
destruct H.
- reflexivity.
- discriminate.
Qed.

Lemma iso_inv2: forall (A: Set) (a: A) (t u l r: binTree A), isomorfo A t u -> t = (add_bt _ a l r) -> exists b l r, u = add_bt _ b l r.
Proof.
intros.
destruct H.
- discriminate.
- exists b, l2, r2.
  reflexivity.
Qed.

Lemma iso_trans: forall (A: Set) (t u v: binTree A), isomorfo _ t u -> isomorfo _ u v -> isomorfo _ t v.
Proof.
intros A t u v h g.
induction h; induction g.
- exact (isomorfo_nil A).
- exact (isomorfo_bt _ a b l1 r1 l2 r2 IHg1 IHg2).
- admit.
- admit. (* apply (isomorfo_bt _ a b0 l1 r1 l3 r3 IHh1 IHh2). *)
Admitted.

(* Inductive isomorfo (A: Set): binTree A -> binTree A -> Prop :=
  | isomorfo_nil: isomorfo A (empty_bt A) (empty_bt A)
  | isomorfo_bt: forall (a b:A) l1 r1 l2 r2,
      isomorfo _ l1 l2 -> isomorfo _ r1 r2 ->
        isomorfo _ (add_bt _ a l1 r1) (add_bt _ b l2 r2). *)

End Ejercicio15.

Section Ejercicio16.

Inductive Tree (A: Set): Set :=
  | leaf_bt: A -> Tree A
  | add_tree: Tree A -> Tree A -> Tree A.
(* Información en las hojas *)

Fixpoint tmap (a b: Set) (f: a -> b) (t: Tree a) {struct t}: Tree b :=
  match t with
    | leaf_bt _ e => leaf_bt _ (f e)
    | add_tree _ l r => add_tree _ (tmap _ _ f l) (tmap _ _ f r)
  end.
(* Print tmap. *)

Fixpoint tsize (a: Set) (t: Tree a) {struct t}: nat :=
  match t with
    | leaf_bt _ _ => 1
    | add_tree _ l r => suml (tsize _ l) (tsize _ r)
  end.

Lemma map_tsize: forall (a b: Set) (f: a -> b) (t: Tree a), tsize _ (tmap _ _ f t) = tsize _ t.
Proof.
induction t; simpl.
- reflexivity.
- rewrite IHt1. rewrite IHt2. reflexivity.
Qed.

Fixpoint tree_to_list (a: Set) (t: Tree a) {struct t}: list a :=
  match t with
    | leaf_bt _ e => cons _ e (nil _)
    | add_tree _ l r => append _ (tree_to_list _ l) (tree_to_list _ r)
  end.

Lemma tree_to_list_size: forall (a: Set) (t: Tree a), tsize _ t = llength _ (tree_to_list _ t).
Proof.
induction t; simpl.
- reflexivity.
- rewrite IHt1. rewrite IHt2.
  rewrite (L4 _ (tree_to_list a t1) (tree_to_list a t2)).
  reflexivity.
Qed.

End Ejercicio16.

Section Ejercicio17.

Inductive posfijo (A: Set): list A -> list A -> Prop :=
  | pos_id : forall l, posfijo _ l l
  | pos_propio : forall (l l': list A) (e: A), posfijo _ l l' -> posfijo _ l (cons _ e l').

Lemma PFL1: forall (A: Set) (l1 l2 l3: list A), l2 = append _ l3 l1 -> posfijo _ l1 l2.
Proof.
intros a l1 l2 l3 h.
rewrite h. clear h. (* Sin clear h esta prueba no termina *)
induction l3; simpl.
- exact (pos_id _ l1).
- constructor.
  apply IHl3.
Qed.
(* tengo que aplicar constructor en una hipotesis para no usar clear h *)

Lemma PFL2: forall (A: Set) (l1 l2: list A), posfijo _ l1 l2 -> exists (l3: list A), l2 = append _ l3 l1.
Proof.
intros a l1 l2 h.
induction h.
- exists (nil _).
  simpl.
  reflexivity.
- elim IHh; intros l'' h'.
  rewrite h'.
  exists (cons _ e l'').
  simpl.
  reflexivity.
Qed.

Lemma PFL3: forall (A: Set) (l1 l2: list A), posfijo _ l2 (append _ l1 l2).
Proof.
intros a l1 l2.
induction l1; simpl; constructor.
  - assumption.
Qed.

(* Version menos factorizada para ver la estructura de prueba. *)
(* Lemma PFL3_2: forall (A: Set) (l1 l2: list A), posfijo _ l2 (append _ l1 l2).
Proof.
intros a l1 l2.
induction l1; simpl.
  - constructor.
  - constructor.
    assumption.
Qed. *)

Fixpoint ultimo (a: Set) (l: list a) {struct l}: list a :=
  match l with
    | nil _ => nil _
    | cons _ x l' =>
      match l' with
        | nil _ => cons _ x (nil _)
        | cons _ _ _ => ultimo _ l'
      end
  end.

Lemma ultimo_cons: forall (A: Set) (l: list A) (x y: A), ultimo _ (cons _ x (cons _ y l)) = ultimo _ (cons _ y l).
(* la lista debe tener por lo menos 2 elementos para que valga el lema *)
Proof.
intros a l x y.
induction l; simpl.
- reflexivity.
- case l.
  * reflexivity.
  * intros z l'; reflexivity.
Qed.

Lemma ultimo_posfijo: forall (A: Set) (l: list A), posfijo _ (ultimo _ l) l.
Proof.
induction l. simpl.
- constructor.
- destruct l. (* no usar case aca *)
  * constructor.
  * constructor.
    rewrite (ultimo_cons _ l a a0).
    exact IHl.
Qed.

End Ejercicio17.

Section Ejercicio18.

Inductive ABTree (A B: Set): Set :=
  | leaf_abt: B -> ABTree A B
  | add_abtree: A -> ABTree A B -> ABTree A B -> ABTree A B.
(* Información en nodos internos y hojas *)

Fixpoint absize_ext (A B: Set) (t: ABTree A B) {struct t}: nat :=
  match t with
    | leaf_abt _ _ _ => 1
    | add_abtree _ _ _ l r => suml (absize_ext _ _ l) (absize_ext _ _ r)
  end.

Fixpoint absize_int (A B: Set) (t: ABTree A B) {struct t}: nat :=
  match t with
    | leaf_abt _ _ _ => 0
    | add_abtree _ _ _ l r => S (suml (absize_int _ _ l) (absize_int _ _ r))
  end.

(* Lemma sum_ext: forall (A B: Set) (a: A) (t t1 t2: ABTree A B), t = add_abtree _ _ a t1 t2 ->
  absize_ext _ _ (add_abtree _ _ a t1 t2) = absize_ext _ _ t1 + absize_ext _ _ t2.
Proof.
induction t1.
- intros.
  constructor.
- intros.
  tauto.
Qed.

Lemma sum_int: forall (A B: Set) (a: A) (t t1 t2: ABTree A B), t = add_abtree _ _ a t1 t2 ->
  absize_int _ _ (add_abtree _ _ a t1 t2) = S (absize_int _ _ t1 + absize_int _ _ t2).
Proof.
induction t1.
- intros.
  simpl.
  reflexivity.
- intros.
  tauto.
Qed. *)

Lemma S_aux: forall (n m: nat), S (suml n m) = suml (S n) m.
Proof.
tauto.
Qed.

Lemma S_aux2: forall (n m: nat), S (suml n m) = suml n (S m).
Proof.
intros x y.
rewrite (SumS x y).
tauto.
Qed.

Lemma rel_ext_int: forall (A B: Set) (t: ABTree A B), absize_ext _ _ t = S (absize_int _ _ t).
Proof.
induction t; simpl.
- reflexivity.
- rewrite IHt1.
  rewrite IHt2.
  rewrite (S_aux (absize_int A B t1) (absize_int A B t2)).
  rewrite (S_aux2 (S (absize_int A B t1)) (absize_int A B t2)).
  reflexivity.
Qed.

End Ejercicio18.

Section Ejercicio19.

Variable A : Set.

Inductive Tree_ : Set :=
  | nullT : Tree_
  | consT : A -> Tree_ -> Tree_ -> Tree_.

Inductive subarbol: Tree_ -> Tree_ -> Prop :=
  | sub_id : forall t, subarbol t t
  | sub_propio_izq : forall (t t1 t2: Tree_) (e: A),
      subarbol t t1 -> subarbol t (consT e t1 t2)
  | sub_propio_der : forall (t t1 t2: Tree_) (e: A),
      subarbol t t2 -> subarbol t (consT e t1 t2).

Lemma subarbol_refl: forall (t: Tree_), subarbol t t.
Proof.
induction t.
- exact (sub_id nullT).
- exact (sub_id (consT a t1 t2)).
Qed.

(* Lemma SAL1: forall (t t1 t2: Tree_) (e: A), subarbol (consT e t1 t2) t -> subarbol t1 t.
Proof.
intros t t1 t2 e h.
induction t.
- admit. (* subarbol (consT e t1 t2) nullT -> t1 = nullT *)
- admit.
Admitted. *)

Lemma null_subarbol: forall (t: Tree_), subarbol nullT t.
Proof.
induction t.
- exact (sub_id nullT).
- exact (sub_propio_izq nullT t1 t2 a IHt1).
Qed.

(* Lemma subarbol_izq: forall (t t1 t2: Tree_) (e: A), t = (consT e t1 t2) -> subarbol t1 t.
Proof.
intros t t1 t2 e h.
induction t1.
- exact (null_subarbol t).
- admit.
Admitted. *)

(* Lemma SAL1_2: forall (t t1 t2: Tree_) (e: A), subarbol (consT e t1 t2) t -> subarbol t1 t.
Proof.
intros t t1 t2 e h.
induction h. (* perdi todo *)
- exact (subarbol_izq t t1 t2 e). (* como pruebo que t = (consT e t1 t2) *)
- exact (sub_propio_izq t1 t0 t3 e0 IHh).
- exact (sub_propio_der t1 t0 t3 e0 IHh).
Admitted. *)

(* Lemma SAL2: forall (t t1 t2: Tree_) (e: A), subarbol (consT e t1 t2) t -> subarbol t2 t.
Proof.
Admitted. *)

(* Lemma subarbol_trans: forall (t u v: Tree_), subarbol t u -> subarbol u v -> subarbol t v.
Proof.
intros t u v h g.
induction h.
- assumption.
- apply IHh.
  exact (SAL1 v t1 t2 e g).
- apply IHh.
  exact (SAL2 v t1 t2 e g).
Qed. *)

Lemma subarbol_trans: forall (t u v: Tree_), subarbol t u -> subarbol u v -> subarbol t v.
Proof.
intros t u v h0 h1.
induction h1.
- assumption.
- apply sub_propio_izq.
  apply IHh1.
  assumption.
- apply sub_propio_der.
  apply IHh1.
  assumption.
Qed.

End Ejercicio19.

Section Ejercicio20.

Inductive ComTree (A: Set): nat -> Set :=
  | leaf_com: A -> ComTree A 0
  | add_com: forall (n: nat), A -> ComTree A n -> ComTree A n -> ComTree A (S n).

Fixpoint h (n: nat) (A: Set) (t: ComTree A n) {struct t}: nat :=
  match t with
    | leaf_com _ _ => 1
    | add_com _ _ _ l r => suml (h _ _ l) (h _ _ r)
  end.
(* Alternativamente definirla por recursion en n *)

(* n^0 = 1 forall n>0 *)
Axiom potO : forall n : nat, pot (S n) 0 = 1.

(* 2^{m+1} = 2^m + 2^m *)
Axiom potS : forall m: nat, pot 2 (S m) = suml (pot 2 m) (pot 2 m).

Lemma comtsize: forall (n:nat) (A:Set) (t: ComTree A n), h _ _ t = pot 2 n.
Proof.
induction t.
- (* rewrite (potO 1). *)
  simpl.
  reflexivity.
- rewrite (potS n).
  simpl.
  rewrite IHt1.
  rewrite IHt2.
  reflexivity.
Qed.

(* Lemma t_0: forall (A:Set) (t: ComTree A 0), exists (e: A), t = leaf_com _ e.
Proof.
Admitted. *)

End Ejercicio20.

Section Ejercicio21.

Inductive AB (A: Set): nat -> Set :=
  | nil_ab: AB A 0
  | add_ab: forall (n m: nat), A -> AB A n -> AB A m -> AB A (S (max n m)).

Fixpoint camino (n: nat) (A: Set) (t: AB A n) {struct t}: list A :=
  match t with
    | nil_ab _ => nil _
    | add_ab _ n m e l r =>
      match le_bool m n with
        | true => cons _ e (camino _ _ l)
        | false => cons _ e (camino _ _ r)
      end
  end.

Lemma max_r: forall (n m : nat), le_bool n m = true -> max m n = m.
Proof.
induction n; intros; destruct m; simpl.
- reflexivity.
- reflexivity.
- discriminate.
- rewrite IHn.
  * reflexivity.
  * simpl in H. assumption.
Qed.

Lemma max_l: forall (n m : nat), le_bool n m = false -> max m n = n.
induction n; intros; destruct m; simpl.
- reflexivity.
- discriminate.
- reflexivity.
- rewrite IHn.
  * reflexivity.
  * simpl in H. assumption.
Qed.

Lemma largo_camino: forall (n: nat) (A: Set) (t: AB A n), llength _ (camino n A t) = n.
Proof.
induction t; simpl.
- reflexivity.
- case_eq (le_bool m n); intro le_value ; simpl.
  * rewrite IHt1.
    rewrite (max_r m n).
    + reflexivity.
    + assumption.
  * rewrite IHt2.
    rewrite (max_l m n).
    + reflexivity.
    + assumption.
Qed.

End Ejercicio21.