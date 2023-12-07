(*
NOMBRE COMPLETO:
Ines Cipullo
*)

Require Export List.

Require Import Lia.

Require Export Arith.
Print beq_nat.


Section Problema1.

Fixpoint eliminar (z:nat) (l:list nat) {struct l} : list nat :=
match l with
  | nil => nil
  | cons x xs => if (Nat.eqb x z) then xs else cons x (eliminar z xs)
end.


Fixpoint pertenece (z:nat) (l:list nat) {struct l} : bool :=
match l with
  | nil => false
  | cons x xs => if (Nat.eqb x z) then true else pertenece z xs
end.


Lemma L1_1: forall (A:Set) (l:list A) (x:A), l <> x::l.
Proof. 
unfold not.
induction l.
- discriminate.
- intros. injection H.
  intros.
  apply (IHl a).
  exact H0.
Qed.


Lemma L1_2: forall (l:list nat) (x:nat), pertenece x l = true -> eliminar x l <> l.
Proof. 
induction l.
- intros.
  simpl in H.
  discriminate H.
- intros.
  simpl.
  case_eq (Nat.eqb a x); intros.
  -- apply L1_1.
  -- simpl in H.
     rewrite H0 in H.
     intro.
     apply (IHl x).
     exact H.
     injection H1.
     intros.
     exact H2.
Qed.


End Problema1.


Section Problema2.

Inductive distintas (A:Set) : list A -> list A -> Prop :=
| distintas_nil: distintas A nil nil
| distintas_cons: forall (a1 a2: A) (l1 l2 : list A), 
    a1 <> a2 -> distintas A l1 l2 -> distintas A (cons a1 l1) (cons a2 l2).

Hint Constructors distintas.


Fixpoint not (l : list bool) : list bool :=
match l with
  | nil => nil
  | cons x xs => cons (negb x) (not xs)
end.


Lemma L2_aux: forall l1: list bool, distintas bool l1 (not l1).
Proof.
intro.
induction l1; simpl.
- constructor.
- destruct a;
  apply distintas_cons; 
  try discriminate;
  exact IHl1.
Qed.


Lemma L2: forall (l1:list bool), { l2: list bool | distintas bool l1 l2 }.
Proof.
intros.
induction l1.
- exists nil.
  apply distintas_nil.
- destruct a;
  [exists (cons false (not l1)) | exists (cons true (not l1))];
  apply distintas_cons;
  try discriminate;
  apply (L2_aux l1).
Qed.

End Problema2.


(* Ejercicio 2 c *)
Require Import Coq.extraction.ExtrHaskellBasic.

Extraction Language Haskell.
Extraction "not_lista" L2.


Section Problema3.
 
Definition Var := nat.
Definition Valor := nat.

Definition Memoria := Var -> Valor.
 
Inductive Instr : Set :=
  | Ass : Var -> Valor -> Instr
  | Seq : Instr -> Instr -> Instr
  | If : Var -> Valor -> Instr -> Instr -> Instr.

Definition lookup (m : Memoria) (v : Var) : Valor := m v.
 
Definition update (m : Memoria) (v : Var) (w : Valor) : Memoria :=
fun var: Var => if Nat.eqb v var then w else m var.
 
Inductive Execute : Memoria -> Instr -> Memoria -> Prop :=
  | xAss : forall (m: Memoria) (v: Var) (w: Valor), Execute m (Ass v w) (update m v w)
  | xSeq : forall (m1 m2 m3: Memoria) (i1 i2 : Instr),
              Execute m1 i1 m2 -> Execute m2 i2 m3 -> Execute m1 (Seq i1 i2) m3
  | xIfT : forall (m1 m2: Memoria) (v: Var) (w: Valor) (i1 i2: Instr),
              lookup m1 v = w -> Execute m1 i1 m2 -> Execute m1 (If v w i1 i2) m2
  | xIfF : forall (m1 m2: Memoria) (v: Var) (w: Valor) (i1 i2: Instr),
              lookup m1 v <> w -> Execute m1 i2 m2 -> Execute m1 (If v w i1 i2) m2.

Hint Constructors Execute : core.

Lemma L3_1: forall (m1 m2:Memoria) (v:Var) (val:Valor) (I1 I2:Instr), 
(lookup m1 v = val -> False) -> Execute m1 (If v val I1 I2) m2 -> Execute m1 I2 m2.
Proof.
intros.
inversion H0.
- rewrite H7 in H.
  absurd (val = val -> False).
  + intro.
    apply H9.
    reflexivity.
  + exact H.
- exact H8.
Qed.


Lemma L3_2: forall (m1 m2 m3:Memoria)(v1 v2:Var) (val:Valor) (i1 i2:Instr), 
v1 <> v2 -> Execute m1 (Seq (Ass v1 val) (Ass v2 (S val))) m2 -> Execute m2 i2 m3 -> 
Execute m2 (If v2 (lookup m2 v1) i1 i2) m3.
Proof.
intros.
inversion_clear H0.
inversion H2.
rewrite <- H4 in H3.
inversion H3.
rewrite H8.
apply xIfT.
- rewrite <- H8.
  unfold lookup.
  unfold update.
  admit.
- admit.
Admitted.
 
End Problema3.