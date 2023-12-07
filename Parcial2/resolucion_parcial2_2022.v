Require Export List.
Require Export Arith.  (* Aca viene Nat.eqb *)
Require Import Lia.

Set Implicit Arguments. (* Puede quitar esta línea si lo prefiere *) 


(* ----------- Ej1 ----------- *)

Fixpoint elim (z:nat) (l:list nat) {struct l} : list nat :=
     match l with
         | nil => nil
         | cons x xs => if (Nat.eqb z x) then elim z xs else x::(elim z xs)
     end.

Fixpoint pertenece (z:nat) (l:list nat) {struct l} : bool :=
     match l with
         | nil => false
         | cons x xs => if (Nat.eqb z x) then true else pertenece z xs
     end.
 
Lemma Ej1_3_1 : forall (l:list nat) (x:nat), pertenece x (elim x l) = false.
Proof.
    intros l x.
    induction l; simpl.
    auto.
    case_eq (Nat.eqb x a); intros; simpl.
    exact IHl.
    rewrite H.
    exact IHl.
Qed.

Lemma Ej1_3_2 : forall (l:list nat) (x:nat), length (elim x l) <= length l.
Proof.
    intros l x. 
    elim l; simpl; intros.
    auto.
    case_eq (Nat.eqb x a); intros; simpl.
    auto.
    lia.
Qed.

Lemma Ej1_3_3 : forall (l:list nat) (x:nat), pertenece x l = true -> l <> elim x l.
Proof.
    unfold not. intros.
    rewrite H0 in H.
    rewrite Ej1_3_1 in H.
    discriminate.
Qed.


(* ----------- Ej2 ----------- *)

Inductive sublista (A : Set) : list A -> list A -> Prop :=
  | prefijo_id : forall l : list A, sublista nil l
  | prefijo_cons :
      forall (a : A) (l1 l2 : list A),
      sublista l1 l2 -> sublista (a::l1) (a::l2).

Local Hint Constructors sublista.

Lemma Ej2_2_1 : forall (A : Set) (l1 l2 : list A), sublista l1 l2 -> length l1 <= length l2.
Proof.
     intros A l1 l2 sub_l1_l2.
     induction sub_l1_l2;
     simpl; lia.
Qed.

Lemma Ej2_2_2 : forall (l1 l2: list nat), sublista l1 l2 -> sublista l2 l1 -> l1 = l2.
Proof.
     intros l1 l2 H1; induction H1; simpl; intros; auto.
     inversion_clear H; auto.
     inversion_clear H in IHsublista; auto.
     rewrite (IHsublista H0); auto.
Qed.


(* ----------- Ej3 ----------- *)

Inductive perm (A:Set): (list A) -> (list A) -> Prop:=
 p_refl: forall l:list A, perm l l
|p_trans: forall l m n:list A, (perm l m) -> (perm m n) -> perm l n
|p_ccons: forall (a b: A) (l:list A), perm (cons a (cons b l)) (cons b (cons a l))
|p_cons: forall (a:A) (l m:list A), (perm l m) -> perm (cons a l) (cons a m).


Fixpoint swap (A:Set) (l:list A) {struct l}: list A :=
    match l with 
        nil => nil
      | cons a l2 => match l2 with 
			                  nil => l
            		      | cons b l3 => cons b (cons a (swap l3))
		                 end
    end.


Local Hint Constructors perm : core.

Require Import FunInd.

Functional Scheme swap_ind := Induction for swap Sort Set.

Lemma Ej3: forall (A:Set) (l:list A), {l2:list A | perm l l2}.
Proof.
intros A l.
exists (swap l).
functional induction swap l.
auto.
auto.
apply p_trans with (a :: b :: swap l3); auto.
(* o simplmente:
intros A l; exists (swap l).
functional induction swap  l; eauto.
*)
Qed.
