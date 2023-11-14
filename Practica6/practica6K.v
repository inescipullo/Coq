Section Ejercicio1.

Lemma predspec : forall n : nat, {m : nat | n = 0 /\ m = 0 \/ n = S m}. 
Proof.
intros.
destruct n.
- exists 0. left. split; reflexivity.
- exists n. right. reflexivity.
Qed.

End Ejercicio1.

Require Import Coq.extraction.ExtrHaskellBasic.
Extraction Language Haskell.
Extraction "predecesor" predspec.
(*SE EXTRAE EN HOME*)

Section Ejercicio2.

Inductive bintree (A:Set) : Set :=
  empty_bintree : bintree A
| add_bintree : A -> bintree A -> bintree A -> bintree A.

Inductive mirror (A:Set) : bintree A -> bintree A -> Prop :=
  mirror_empty : mirror A (empty_bintree A) (empty_bintree A)
| mirror_add : forall a l1 r1 l2 r2, 
            mirror A l1 r2 -> mirror A r1 l2 -> mirror A (add_bintree A a l1 r1) (add_bintree A a l2 r2).

Lemma MirrorC: forall (A:Set) (t:bintree A),
{t':bintree A|(mirror A t t')}. 
Proof.
intros.
induction t.
- exists (empty_bintree A). apply mirror_empty.
- destruct IHt1 as [t1' H1].
  destruct IHt2 as [t2' H2].
  exists (add_bintree A a t2' t1'). (* Caso inductivo para un árbol no vacío *)
  apply mirror_add.
  + apply H1.
  + apply H2.
Qed.

Fixpoint inverse (A: Set) (t: bintree A) : bintree A :=
  match t with
   | empty_bintree _ => empty_bintree A
   | add_bintree _ x l r => add_bintree A x (inverse A r) (inverse A l)
  end.

Require Import FunInd.
Functional Scheme inverse_ind := Induction for inverse Sort Prop.
Lemma MirrorC2 : forall (A : Set) (t : bintree A), {t2 : bintree A | mirror A t t2}.
Proof.
intros A t.
exists (inverse A t). 
functional induction inverse A t.
Hint Constructors mirror. auto. auto.
Qed.

End Ejercicio2.

Extraction Language Haskell.
Extraction "mirror_function" MirrorC2.
(*SE EXTRAE EN HOME*)

Section Ejercicio3.

Definition Value := bool.

Inductive BoolExpr : Set :=
 | bbool : bool -> BoolExpr
 | band : BoolExpr -> BoolExpr -> BoolExpr
 | bnot : BoolExpr -> BoolExpr.
Inductive BEval : BoolExpr -> Value -> Prop :=
 | ebool : forall b : bool, BEval (bbool b) (b:Value)
 | eandl : forall e1 e2 : BoolExpr, BEval e1 false -> BEval (band e1 e2) false
 | eandr : forall e1 e2 : BoolExpr, BEval e2 false -> BEval (band e1 e2) false
 | eandrl : forall e1 e2 : BoolExpr,
 BEval e1 true -> BEval e2 true -> BEval (band e1 e2) true
 | enott : forall e : BoolExpr, BEval e true -> BEval (bnot e) false
 | enotf : forall e : BoolExpr, BEval e false -> BEval (bnot e) true. 



Fixpoint beval1 (e : BoolExpr) : Value :=
 match e with
 | bbool b => b
 | band e1 e2 =>
 match beval1 e1, beval1 e2 with
 | true, true => true
| _, _ => false
 end
| bnot e1 => if beval1 e1 then false else true
end.


Fixpoint beval2 (e : BoolExpr) : Value :=
match e with
 | bbool b => b
 | band e1 e2 => match beval2 e1 with
 | false => false
 | _ => beval2 e2
 end
 | bnot e1 => if beval2 e1 then false else true
 end.

Lemma evalcorrectness1 : forall e:BoolExpr, {b:Value |(BEval e b)}. 
Proof.
intros e.
exists (beval1 e).
induction e.
- simpl. constructor.
- simpl. destruct (beval1 e1); destruct (beval1 e2).
  -- apply eandrl; assumption.
  -- apply eandr; assumption.
  -- apply eandl; assumption.
  -- apply eandr; assumption.
- simpl. destruct (beval1 e).
  -- apply enott; assumption.
  -- apply enotf; assumption. 
Qed.

Require Import FunInd.
Functional Scheme beval2_ind := Induction for beval2 Sort Prop.
Lemma evalcorrectness2 : forall e:BoolExpr, {b:Value |(BEval e b)}. 
Proof.
intros.
Hint Constructors BEval.
exists (beval2 e).
functional induction (beval2 e).
- auto.
- destruct (beval2 e2).
  -- rewrite e3 in IHv. auto.
  -- rewrite e3 in IHv. auto.
- destruct (beval2 e1). 
  -- discriminate.
  -- constructor. exact IHv.
- destruct (beval2 e1). 
  -- auto.
  -- discriminate.
- destruct (beval2 e1).
  -- discriminate.
  -- auto.
Qed.

Lemma evalcorrectness2_2 : forall e:BoolExpr, {b:Value |(BEval e b)}. 
Proof.
intros e.
Hint Constructors BEval.
exists (beval2 e).
induction e.
- simpl. constructor.
- simpl. destruct (beval2 e1); destruct (beval2 e2).
  -- apply eandrl; assumption.
  -- apply eandr; assumption.
  -- apply eandl; assumption.
  -- apply eandr; assumption.
- simpl. destruct (beval2 e).
  -- apply enott; assumption.
  -- apply enotf; assumption. 
Qed.


(*No iria ups*)
Lemma evalproof: forall e:BoolExpr, {b:Value |(BEval e b)}. 
Proof.
intros.
induction e.
Hint Constructors BEval.
- exists b. auto.
- destruct IHe1 as [v1 H1], IHe2 as [v2 H2].
  destruct v1, v2.
  -- exists true. auto.
  -- exists false. auto.
  -- exists false. auto.
  -- exists false. auto.
- destruct IHe as [v H]. (* Caso bnot *)
  destruct v in H.
  -- exists false. auto. 
  -- exists true. auto.
Qed.

End Ejercicio3.

Extraction Language Haskell.
Extract Inductive bool => "Prelude:Bool" ["true" "false"].
Extraction "eval_correct" evalcorrectness1.

Section Ejercicio4.

Section list_perm.
Variable A:Set.
Inductive list : Set :=
 | nil : list
 | cons : A -> list -> list.

Fixpoint append (l1 l2 : list) {struct l1} : list :=
 match l1 with
 | nil => l2
 | cons a l => cons a (append l l2)
 end.

Inductive perm : list -> list ->Prop:=
|perm_refl: forall l, perm l l
|perm_cons: forall a l0 l1, perm l0 l1-> perm (cons a l0)(cons a l1)
|perm_app: forall a l, perm (cons a l) (append l (cons a nil))
|perm_trans: forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

Hint Constructors perm.

Fixpoint reverse (l: list) : list :=
match l with
| nil => nil
| cons a xs => append (reverse xs) (cons a nil)
end.

Lemma Ej6_4: forall l: list, {l2: list | perm l l2}.
Proof.
intros.
exists (reverse l).
induction l.
- simpl. constructor.
- simpl. 
  apply (perm_trans (cons a l) (cons a (reverse l)) (append (reverse l) (cons a nil))). 
  -- constructor. exact IHl.
  -- constructor. 
Qed.

Lemma Ej6_4_1: forall l: list, {l2: list | perm l l2}.
Proof.
intros.
destruct l.
- exists nil. constructor.
- exists (append l (cons a nil)).
  constructor.
Qed.

End list_perm. 

End Ejercicio4.

Section Ejercicio5.

Inductive Le1 : nat -> nat -> Prop :=
| Le1_n : forall n : nat, Le1 n n
| Le1_S : forall n m : nat, Le1 n m -> Le1 n (S m).

Inductive Le : nat -> nat -> Prop :=
| Le_0 : forall n: nat, Le 0 n
| Le_S : forall n m: nat, Le n m -> Le (S n) (S m).

Inductive Gt: nat -> nat -> Prop :=
| Gt_0 : forall n: nat, Gt (S n) 0
| Gt_S : forall n m: nat, Gt n m -> Gt (S n) (S m).

Inductive Gt1 : nat -> nat -> Prop :=
| Gt1_S : forall n m : nat, Gt1 n m -> Gt1 (S n) m
| Gt1_n : forall n : nat, Gt1 (S n) n.

(*leBool:nat->nat->bool.*)
Fixpoint leBool1 (n m : nat) : bool :=
  match n, m with
  | 0, _ => true
  | S _, 0 => false
  | S n', S m' => leBool1 n' m'
  end.

Fixpoint leBool2 (n m : nat) : bool :=
  match n with
  | 0 => true
  | S n1 => match m with
            | 0 => false
            | S m1 => leBool2 n1 m1
            end
  end.
(*
{(Le n m)} + {(Gt n m)} es una notación específica en Coq 
que indica que la proposición Le n m o la proposición 
Gt n m es decidible, es decir, se puede probar que una y solo una de ellas 
es verdadera para cualquier par dado de números naturales n y m. *)

(*
La notación {A} + {B} se llama "suma de coproducto" 
y se utiliza para indicar una disyunción exclusiva, es decir, 
A o B, pero no ambos.
*)

Require Import FunInd.
Functional Scheme leBool1_rec := Induction for leBool1 Sort Set.
Lemma Le_Gt_dec: forall n m:nat, {(Le n m)} + {(Gt n m)}.
Proof.
intros n m.
functional induction (leBool1 n m).
- left. constructor.
- right. constructor.
- destruct IHb.
  -- left. constructor. exact l.
  -- right. constructor. exact g.
Qed.

Require Import Lia.

Lemma le_gt_dec: forall n m:nat, {(le n m)}+{(gt n m)}.
Proof.
intros.
functional induction (leBool1 n m).
- left. lia.
- right. lia.
- destruct IHb.
  -- left. lia.
  -- right. lia.
Qed.

End Ejercicio5.


Section Ejercicio6.

Require Import Lia.
Require Import DecBool.
Require Import Compare_dec.
Require Import Plus.
Require Import Mult. 


Definition spec_res_nat_div_mod (a b:nat) (qr:nat*nat) :=
 match qr with
 (q,r) => (a = b*q + r) /\ r < b
 end.

Fixpoint ltBool (n m : nat) : bool :=
  match n, m with
  | 0, 0 => false
  | 0, S m' => true
  | S _, 0 => false
  | S n', S m' => ltBool n' m'
  end.

Definition nat_div_mod :
 forall a b:nat, not(b=0) -> {qr:nat*nat | spec_res_nat_div_mod a b qr}.
Proof.
intros.
induction a.
- exists (0,0). simpl. split.
  -- lia.
  -- lia.
- destruct IHa.
  destruct x as [q r].
  case_eq (lt_dec r (b-1)); intros.
  -- exists (q, r+1). simpl. split.
      --- simpl in s. lia.
      --- lia.
  -- exists (q+1, 0). simpl. split.
      --- simpl in s. lia.
      --- lia.
Qed.

(*
0 divmod b = (0,0)
(n+1) divmod b = let (q,r) = n divmod b in
                       if r < b-1
                       then (q,r+1)
                       else (q+1,0)
*)


End Ejercicio6.


Section Ejercicio7.

Inductive tree (A:Set) : Set :=
 | leaf : tree A
 | node : A -> tree A -> tree A -> tree A.

Inductive tree_sub (A:Set) (t:tree A) : tree A -> Prop :=
 | tree_sub1 : forall (t':tree A) (x:A), tree_sub A t (node A x t t')
 | tree_sub2 : forall (t':tree A) (x:A), tree_sub A t (node A x t' t).

(* Theorem well_founded_tree_sub : forall A:Set, well_founded (tree_sub A). 
Proof.
intros.
unfold well_founded.
intros a.
induction a.
- 
Qed.  *)

Theorem well_founded_tree_sub: forall A:Set, well_founded (tree_sub A).
Proof.
intros.
unfold well_founded. 
intros.
induction a.
- apply Acc_intro. (* idem constructor *)
  intros t Hi.
  simple inversion Hi.
  -- discriminate.
  -- discriminate. (*vale pq no hay subarboles de leaf*)
- constructor.
  intros t Hi.
  inversion Hi.
 -- exact IHa1.
 -- exact IHa2.
Qed.


End Ejercicio7.

Section Ejercicio8.

(*
Definition Value := bool.

Inductive BoolExpr : Set :=
 | bbool : bool -> BoolExpr
 | band : BoolExpr -> BoolExpr -> BoolExpr
 | bnot : BoolExpr -> BoolExpr.

Inductive BEval : BoolExpr -> Value -> Prop :=
 | ebool : forall b : bool, BEval (bbool b) (b:Value)
 | eandl : forall e1 e2 : BoolExpr, BEval e1 false -> BEval (band e1 e2) false
 | eandr : forall e1 e2 : BoolExpr, BEval e2 false -> BEval (band e1 e2) false
 | eandrl : forall e1 e2 : BoolExpr,
 BEval e1 true -> BEval e2 true -> BEval (band e1 e2) true
 | enott : forall e : BoolExpr, BEval e true -> BEval (bnot e) false
 | enotf : forall e : BoolExpr, BEval e false -> BEval (bnot e) true. 
*)

(*
Fixpoint ltBool (n m : nat) : bool :=
  match n, m with
  | 0, 0 => false
  | 0, S m' => true
  | S _, 0 => false
  | S n', S m' => ltBool n' m'
  end.
*)

Fixpoint size (e : BoolExpr) : nat :=
match e with
| bbool _ => S 0
| band e1 e2 => size e1 + size e2
| bnot e1 => S (size e1)
end.

Require Import Lia.

Lemma size_not_cero: forall (e : BoolExpr), ~ size e = 0.
Proof.
intros.
induction e; simpl; lia.
Qed.

Definition elt (e1 e2 : BoolExpr) := size e1 < size e2.

Require Import Coq.Wellfounded.Inverse_Image.
Require Import Wf_nat.

Print wf_inverse_image.
Print lt_wf.

Theorem well_founded_elt: well_founded (elt).
Proof.
unfold well_founded.
intros.
apply (wf_inverse_image BoolExpr nat lt size).
exact lt_wf.
Qed.
(* unfold well_founded.
intros.
induction a.
- constructor.
  intros.
  inversion H.
  -- absurd (size y = 0).
      --- apply (size_not_cero y).
      --- exact H1.
  -- absurd (S (size y) <= 0).
      --- induction y; simpl; lia.
      --- exact H1.
- constructor.
  intros.
  inversion H.
  --  *)

(*
https://www.cs.princeton.edu/courses/archive/fall07/cos595/stdlib/html/Coq.Wellfounded.Inverse_Image.html
*)

End Ejercicio8.

Section Ejercicio9.

Inductive sorted (A:Set) (R:A->A->Prop) : list A -> Prop :=
  sorted_0 : sorted A R (nil A)
| sorted_1 : forall h, sorted A R (cons A h (nil A))
| sorted_S : forall h1 h2 l, (R h1 h2) -> sorted A R (cons A h2 l) -> sorted A R (cons A h1 (cons A h2 l)).

Inductive perm1 (A:Set) : list A -> list A ->Prop:=
|perm1_refl: forall l, perm1 A l l
|perm1_cons: forall a l0 l1, perm1 A l0 l1-> perm1 A (cons _ a l0)(cons _ a l1)
|perm1_ccons: forall a b l, (perm1 A (cons _ a (cons _ b l)) (cons _ b (cons _ a l)))
|perm1_trans: forall l1 l2 l3, perm1 A l1 l2 -> perm1 A l2 l3 -> perm1 A l1 l3.

Lemma SORT: forall l:(list nat), {s:(list nat) |
 (sorted nat le s) /\ (perm1 nat l s)}.
Proof.
intros.
induction l.
- exists (nil nat).
  split.
  -- constructor.
  -- constructor.
- destruct IHl.
  destruct x.
  -- elim a0.
     intros.

  exists (cons nat a x).
  split.
  -- 
Qed.


End Ejercicio9.



 




