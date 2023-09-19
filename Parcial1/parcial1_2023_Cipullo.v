(* 
Parcial 1 - CFPTT - 2023
Alumna: Inés Cipullo
*)


Section Problema1. (* PROBLEMA 1 *)

Variable NM RED CONS UTIL : Prop.

Hypothesis H1 : NM -> not RED.
Hypothesis H2 : CONS \/ not UTIL.

Lemma lema1 : ~CONS \/ RED -> ~NM \/ ~UTIL.
Proof.
intro H; elim H.
- intro noCons.
  elim H2.
  intro Cons.
  absurd CONS.
  exact noCons.
  exact Cons.
  intro noUtil.
  right.
  exact noUtil.
- intro Red.
  left.
  intro Nm.
  apply H1.
  exact Nm.
  exact Red.
Qed.

End Problema1.


Section Problema2. (* PROBLEMA 2 *)

Variable C : Set.
Variables T U : C -> C -> Prop.

Lemma lema2: (forall (x y : C), (U x y -> ~(T x y))) /\ (exists z : C, T z z) -> exists w : C, ~(U w w).
Proof.
intro H; elim H; intros H1 H2.
elim H2; intros z H3.
exists z; intro H4.
apply (H1 z z).
exact H4.
exact H3.
Qed.

End Problema2.


Section Problema3. (* PROBLEMA 3 *)

Variable Bool: Set.
Variable TRUE : Bool.
Variable FALSE : Bool.

Variable Not : Bool -> Bool.
Variable Or : Bool -> Bool -> Bool.
Variable And : Bool -> Bool -> Bool.

Axiom BoolVal : forall b : Bool, b = TRUE \/ b = FALSE.

Axiom NotTrue : Not TRUE = FALSE.
Axiom NotFalse : Not FALSE = TRUE.

Axiom AndTrue : forall b : Bool, And TRUE b = b.
Axiom AndFalse : forall b : Bool, And FALSE b = FALSE.

Axiom OrTrue : forall b : Bool, Or TRUE b = TRUE.
Axiom OrFalse : forall b : Bool, Or FALSE b = b.


Lemma lema3_1 : forall b : Bool, Not (Not b) = b.
Proof.
intro b.
elim (BoolVal b); intro valb; rewrite valb.
- rewrite NotTrue.
  rewrite NotFalse.
  reflexivity.
- rewrite NotFalse.
  rewrite NotTrue.
  reflexivity.
Qed.


Lemma lema3_2 : forall b1 b2 : Bool, Not (Or b1 b2) = And (Not b1) (Not b2).
Proof.
intros b1 b2.
elim (BoolVal b1); elim (BoolVal b2); intros valb2 valb1; rewrite valb1; rewrite valb2;
try (rewrite OrTrue); try (rewrite OrFalse);
try (rewrite NotTrue); try (rewrite NotFalse);
try (rewrite AndTrue); try (rewrite AndFalse);
reflexivity.
Qed.

Lemma lema3_3 : forall b1 : Bool, exists b2 : Bool, And b1 b2 = Or b1 b2.
Proof.
intro b1.
exists b1.
elim (BoolVal b1); intro valb1; rewrite valb1.
- rewrite AndTrue.
  rewrite OrTrue.
  reflexivity.
- rewrite AndFalse.
  rewrite OrFalse.
  reflexivity.
Qed.

End Problema3.


Section Problema4. (* PROBLEMA 4 *)

Parameter Array : Set -> nat -> Set.
(* a*)
Parameter empty : forall X : Set, Array X 0.
Check empty.

(* b *)
Parameter add : forall (X : Set) (l : nat), X -> X -> Array X l -> Array X (l+2).
Check add.

(* c *)
Definition A2 := add nat 0 5 6 (empty nat). (* arreglo de largo 2 *)
Definition A4 := add nat 2 3 4 A2. (* arreglo de largo 4 *)
Definition A6 := add nat 4 1 2 A4. (* arreglo de largo 6 pedido con elementos del 1 al 6 *) 
Check A6.

(* d *)
Parameter singleton : forall X : Set, X -> Array X 1.

Definition A3 := add nat 1 7 8 (singleton nat 9). (* arreglo de largo 3 pedido con elementos 7, 8 y 9 *)
Check A3.

End Problema4.


Section Problema5. (*PROBLEMA 5 *)

Variable S : Set.
Variable e1 e2 : S.
Variable P1 P2 : S -> S -> Prop.
Variable P3 P4 : S -> Prop.

(* a *)
Lemma lema5_1 : (forall x y : S, P1 x y -> P2 y x) -> (P1 e1 e2) ->  P2 e2 e1.
Proof.
exact (fun H => H e1 e2).
Qed.

(* b *)
Lemma lema5_2 : (forall x:S, P3 x) \/ (forall y:S, P4 y) -> forall z:S, P3 z \/ P4 z.
Proof.
intro H1; elim H1; intros H2 z; [left | right]; exact (H2 z).
Qed.

End Problema5.