(* Entrega Práctico 6 - CFPTT *)
(* Alumnas: Cipullo, Inés - Sullivan, Katherine *)

Require Import Coq.extraction.ExtrHaskellBasic.
Require Import FunInd.
Extraction Language Haskell.

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


(* 3.1 *)
Lemma beval1C : forall e:BoolExpr, {b:Value |(BEval e b)}. 
Proof.
intro e.
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

Lemma beval2C : forall e:BoolExpr, {b:Value |(BEval e b)}. 
Proof.
intro e.
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

(*3.2*)

Functional Scheme beval1_ind := Induction for beval1 Sort Prop.

Functional Scheme beval2_ind := Induction for beval2 Sort Prop.

Hint Constructors BEval : core.


Lemma beval1C2: forall e:BoolExpr, {b:Value |(BEval e b)}. 
Proof.
intros.
exists (beval1 e).
functional induction (beval1 e).
- auto.
- rewrite e3 in IHv. rewrite e4 in IHv0. auto.
- rewrite e4 in IHv0. auto.
- rewrite e3 in IHv. auto.
- rewrite e2 in IHv. auto.
- rewrite e2 in IHv. auto.
Qed.


Lemma beval2C2: forall e:BoolExpr, {b:Value |(BEval e b)}. 
Proof.
intros.
exists (beval2 e).
functional induction (beval2 e).
- auto.
- rewrite e3 in IHv. destruct (beval2 e2); auto.
- rewrite e3 in IHv. auto.
- rewrite e2 in IHv. auto.
- rewrite e2 in IHv. auto.
Qed.

End Ejercicio3.

(* 3.3 *)

Extraction "beval1C_function" beval1C.
Extraction "beval2C_function" beval2C.
Extraction "beval1C2_function" beval1C2.
Extraction "beval2C2_function" beval2C2.

(* 3.4 *)
Extract Inductive bool => "Prelude:Bool" ["true" "false"].
Extraction "beval1C_function2" beval1C.
Extraction "beval2C_function2" beval2C.
Extraction "beval1C2_function2" beval1C2.
Extraction "beval2C2_function2" beval2C2.

Section Ejercicio5.

Inductive Le : nat -> nat -> Prop :=
| Le_0 : forall n: nat, Le 0 n
| Le_S : forall n m: nat, Le n m -> Le (S n) (S m).

Inductive Gt: nat -> nat -> Prop :=
| Gt_0 : forall n: nat, Gt (S n) 0
| Gt_S : forall n m: nat, Gt n m -> Gt (S n) (S m).

Hint Constructors Le Gt : core.

(*leBool:nat->nat->bool.*)
Fixpoint leBool (n m : nat) : bool :=
  match n, m with
  | 0, _ => true
  | S _, 0 => false
  | S n', S m' => leBool n' m'
  end.

Functional Scheme leBool_rec := Induction for leBool Sort Set.
Lemma Le_Gt_dec: forall n m:nat, {(Le n m)} + {(Gt n m)}.
Proof.
intros n m.
functional induction (leBool n m).
- left. auto.
- right. auto.
- destruct IHb.
  -- left. auto.
  -- right. auto.
Qed.

Require Import Lia.

Lemma le_gt_dec: forall n m:nat, {(le n m)}+{(gt n m)}.
Proof.
intros.
functional induction (leBool n m).
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

(*
0 divmod b = (0,0)
(n+1) divmod b = let (q,r) = n divmod b in
                       if r < b-1
                       then (q,r+1)
                       else (q+1,0)
*)

Definition nat_div_mod :
 forall a b:nat, not(b=0) -> {qr:nat*nat | spec_res_nat_div_mod a b qr}.
Proof.
intros.
induction a.
- exists (0,0). simpl. split; lia.
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

End Ejercicio6.

Section Ejercicio7.

Inductive tree (A:Set) : Set :=
 | leaf : tree A
 | node : A -> tree A -> tree A -> tree A.

Inductive tree_sub (A:Set) (t:tree A) : tree A -> Prop :=
 | tree_sub1 : forall (t':tree A) (x:A), tree_sub A t (node A x t t')
 | tree_sub2 : forall (t':tree A) (x:A), tree_sub A t (node A x t' t).

Theorem well_founded_tree_sub: forall A:Set, well_founded (tree_sub A).
Proof.
intro A.
unfold well_founded. 
intros.
induction a; apply Acc_intro; intros.
- inversion H.
- inversion H; auto.
Qed.

End Ejercicio7.

Section Ejercicio8.

(* 8.1 *)

Fixpoint size (e : BoolExpr) : nat :=
match e with
| bbool _ => S 0
| band e1 e2 => size e1 + size e2
| bnot e1 => S (size e1)
end.

Definition elt (e1 e2 : BoolExpr) := size e1 < size e2. 

(* 8.2 *)

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

End Ejercicio8.

