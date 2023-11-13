Section Ejercicio1.

(* 1.1 *)
Lemma predspec : forall n : nat, {m : nat | n = 0 /\ m = 0 \/ n = S m}.
intros.
destruct n.
- exists 0. left. split; reflexivity.
- exists n. right. reflexivity.
Qed.

End Ejercicio1.

Print predspec.

(* 1.2 *)
(*
Require Import Coq.extraction.ExtrHaskellBasic.

Extraction Language Haskell.
Extraction "predecesor" predspec.
*)

Section Ejercicio2.

Inductive bintree (A:Set) : Set :=
  empty_bintree : bintree A
| add_bintree : A -> bintree A -> bintree A -> bintree A.

Inductive mirror (A:Set) : bintree A -> bintree A -> Prop :=
  mirror_empty : mirror A (empty_bintree A) (empty_bintree A)
| mirror_add : forall a l1 r1 l2 r2, 
            mirror A l1 r2 -> mirror A r1 l2 -> mirror A (add_bintree A a l1 r1) (add_bintree A a l2 r2).

Fixpoint inverse (A: Set) (t: bintree A) : bintree A :=
  match t with
   | empty_bintree _ => empty_bintree A
   | add_bintree _ x l r => add_bintree A x (inverse A r) (inverse A l)
  end.

(* 2.1 *)
Lemma MirrorC: forall (A:Set) (t:bintree A), {t':bintree A|(mirror A t t')}.
Proof.
intros.
induction t.
- exists (empty_bintree A).
  apply mirror_empty.
- elim IHt1. elim IHt2. intros.
  exists (add_bintree A a x x0).
  apply mirror_add.
  + exact p0.
  + exact p.
Qed.

(* 2.2 *)
Lemma MirrorC3: forall (A:Set) (t:bintree A), {t':bintree A|(mirror A t t')}.
Proof.
intros.
exists (inverse A t).
induction t.
- simpl. apply mirror_empty.
- simpl. apply mirror_add.
  + exact IHt1.
  + exact IHt2.
Qed.

Require Import FunInd.
Functional Scheme inverse_ind := Induction for inverse Sort Prop.
Hint Constructors mirror : core.

Lemma MirrorC2: forall (A:Set) (t:bintree A), {t':bintree A|(mirror A t t')}.
Proof.
intros.
exists (inverse A t).
functional induction (inverse A t); auto.
Qed.

End Ejercicio2.

(* 2.3 *)
(*
Require Import Coq.extraction.ExtrHaskellBasic.

Extraction Language Haskell.
Extraction "mirror_function" MirrorC.
Extraction "mirror_function2" MirrorC2.
*)


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
 | band e1 e2 => match beval1 e1, beval1 e2 with
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
Lemma beval1C: forall e: BoolExpr, {b: Value |(BEval e b)}.
Proof.
intro.
exists (beval1 e).
induction e; simpl.
- apply ebool.
- case_eq (beval1 e1); intros; rewrite H in IHe1.
  + case_eq (beval1 e2); intros; rewrite H0 in IHe2.
    * apply eandrl.
      exact IHe1.
      exact IHe2.
    * apply eandr.
      exact IHe2.
  + apply eandl.
    exact IHe1.
- case_eq (beval1 e); intros; rewrite H in IHe.
  + apply enott.
    exact IHe.
  + apply enotf.
    exact IHe.
Qed.

Lemma beval2C: forall e: BoolExpr, {b: Value |(BEval e b)}.
Proof.
intros.
exists (beval2 e).
induction e; simpl.
- apply ebool.
- case_eq (beval2 e1); intros; rewrite H in IHe1.
  + case_eq (beval2 e2); intros; rewrite H0 in IHe2.
    * apply eandrl.
      exact IHe1.
      exact IHe2.
    * apply eandr.
      exact IHe2.
  + apply eandl.
    exact IHe1.
- case_eq (beval2 e); intros; rewrite H in IHe.
  + apply enott.
    exact IHe.
  + apply enotf.
    exact IHe.
Qed.


(* 3.2 *)
Require Import FunInd.
Functional Scheme beval1_ind := Induction for beval1 Sort Prop.
Functional Scheme beval2_ind := Induction for beval2 Sort Prop.
Hint Constructors BEval : core.

Lemma beval1C_2: forall e: BoolExpr, {b: Value |(BEval e b)}.
Proof.
intro.
exists (beval1 e).
functional induction (beval1 e); auto.
- rewrite e3 in IHv. rewrite e4 in IHv0. constructor. exact IHv. exact IHv0.
- rewrite e4 in IHv0. constructor.




Lemma beval2C: forall e: BoolExpr, {b: Value |(BEval e b)}.
Proof.
