(* Ejemplo de Parcial 1 - Octubre 2012 *)

(* Problema 1 *)
Section Problema1. (* VER QUE PASA CUANDO NO SE USA Section *)

Variables NM RED CONS UTIL : Prop.
Hypothesis Hip1 : ~NM \/ ~RED.
Hypothesis Hip2 : CONS \/ ~UTIL.

Theorem Tesis: NM /\ UTIL -> CONS /\ ~RED.
Proof.
intro and.
elim and; intros nm util.
split.
- elim Hip2.
  intro cons.
  exact cons.
  intro noutil.
  absurd UTIL.
  exact noutil.
  exact util.
- elim Hip1.
  intro nonm.
  absurd NM.
  exact nonm.
  exact nm.
  intro nored.
  exact nored.
Qed.

End Problema1.


(* Problema 2 *)
Section Problema2.

Variable U : Set.
Variable R : U -> U -> Prop.

Definition Irreflexiva := forall x: U, ~ (R x x).
Definition Asimetrica := forall x y: U, R x y -> ~ (R y x).

Theorem p2: Asimetrica -> Irreflexiva.
Proof.
intros asim x.
unfold not.
intro r_x_x.
apply (asim x x); exact r_x_x.
Qed.

End Problema2.


(* Problema 3 *)
Section Problema3.
Require Import Classical.

Variable C : Set.
Variable P : C -> C -> Prop.

(* Eliminando el lado izquierdo *)
Lemma L3: (exists x y : C, P x y) \/ ~(exists x : C, P x x).
Proof.
elim (classic (exists x y : C, P x y)).
- intro H; left; exact H.
- intro noH; right; intro H1.
  apply noH.
  elim H1; intros x p.
  exists x; exists x; exact p.
Qed.

(* Eliminando el lado derecho *)
Lemma L3_2: (exists x y : C, P x y) \/ ~(exists x : C, P x x).
Proof.
elim (classic (exists x : C, P x x)).
- intro H.
  elim H; intros x p.
  left.
  exists x; exists x; exact p.
- intro noH; right; exact noH.
Qed.

End Problema3.


(* Problema 4 *)
Section Problema4.
Variable Nat: Set.
Variable zero: Nat.
Variable suc: Nat->Nat.
Variable sum: Nat->Nat->Nat.
Variable prod: Nat->Nat->Nat.
Axiom sum0 : forall n: Nat, sum n zero = n.
Axiom sumS : forall m n: Nat, sum m (suc n) = suc (sum m n).
Axiom prod0 : forall n: Nat, prod n zero = zero.
Axiom prodS : forall m n: Nat, prod m (suc n) = sum m (prod m n).
Axiom allNat : forall n: Nat, n = zero \/ exists m: Nat, suc m = n.
Axiom discNat : forall n: Nat, suc n <> zero.

Lemma L41: forall n: Nat, exists m: Nat, prod n (suc m) = sum n n.
Proof.
intro n.
exists (suc zero).
rewrite prodS.
rewrite prodS.
rewrite prod0.
rewrite sum0.
reflexivity.
Qed.

Lemma L42: forall m n: Nat, m <> zero -> sum n m <> zero.
Proof.
intros m n m_no_0 sum_n_m.
elim (allNat m).
- exact m_no_0.
- intro e; elim e; intros.
  rewrite <- H in sum_n_m.
  rewrite sumS in sum_n_m.
  apply (discNat (sum n x)).
  exact sum_n_m.
Qed.

Lemma L43: forall m n: Nat, sum m n = zero -> m = zero /\ n = zero.
Proof.
intros n m s.
elim (allNat m); elim (allNat n); intros; split; try assumption;
try (rewrite H0 in s;
rewrite sum0 in s;
exact s);
try (elim H0; intros;
rewrite <- H1 in s;
rewrite sumS in s;
elim (discNat (sum n x));
exact s).
Qed.

End Problema4.


(* Problema 5 *)
Section Problema5.
Parameter type : Set.
Parameter exp : type -> Set.

Parameter TNat : type.
Parameter TBool : type.

Parameter NConst : nat -> exp TNat.
Parameter Plus : exp TNat -> exp TNat -> exp TNat.

Parameter BConst : bool -> exp TBool.
Parameter And : exp TBool -> exp TBool -> exp TBool.

Parameter Eq : exp TNat -> exp TNat -> exp TBool.

Parameter If: forall X: type, exp TBool -> exp X -> exp X -> exp X.

Parameter eval : exp TBool -> bool.
Parameter IfFancy: forall (t1 t2 : type) (b : exp TBool), exp t1 -> exp t2 -> match (eval b) with
  | true => exp t1
  | false => exp t2
end.

End Problema5.


(* Problema 6 *)
Section Problema6.
Variable D : Set.
Variable e : D.
Variable V : D -> D -> Prop.
Variable Q T : D -> Prop.

Lemma L6a: (forall x y: D, V x y -> V y x) -> exists z : D, V e z -> V z e.
Proof.
exact (fun (H: (forall x y: D, V x y -> V y x)) => ex_intro _ e (H e e)).
Qed.

Lemma L6b: (forall x: D, Q x) \/ (forall y: D, T y) -> forall z: D, Q z \/ T z.
Proof.
intro or; elim or; intros; [left | right]; exact (H z).
Qed.

(* Para dar el lambda termino de L6b con exact:

Proof.
exact (fun h => fun z => match h with
  | or_introl l => or_introl (l z)
  | or_intror r => or_intror (l z)
end).
Qed.
*)

End Problema6.
