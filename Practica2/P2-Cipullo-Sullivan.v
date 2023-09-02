(* Entrega Práctico 2 - CFPTT *)
(* Alumnas: Cipullo, Inés - Sullivan, Katherine *)

(* Ejercicio 2.2 *)
Section Ejercicio2.

Variable U  : Set.
Variable A B: U -> Prop.
Variable P Q: Prop.
Variable R S: U -> U -> Prop.

(* Ej 2.2.1 *)
Theorem e21 : (forall x:U, ((A x)-> ~(forall x:U, ~ (A x)))).
Proof.
intros x a_x.
unfold not.
intro not_a_y.
apply (not_a_y x).
exact a_x.
Qed.

(* Ej 2.2.2 *)
Theorem e22 : (forall x y:U, ((R x y)))-> (forall x:U, (R x x)).
Proof.
intros r_x_y x.
apply (r_x_y x).
Qed.

(* Ej 2.2.3 *)
Theorem e23 : (forall x:U, ((P -> (A x)))) -> (P -> (forall x: U, (A x))).
Proof.
intros a_x p x.
apply a_x; exact p.
Qed.

(* Ej 2.2.4 *)
Theorem e24 : (forall x:U, ((A x) /\ (B x))) -> (forall x:U, (A x)) -> (forall x:U, (B x)).
Proof.
intros a_x_and_b_x a_x x.
apply (a_x_and_b_x x).
Qed.

(* Ej 2.2.5 *)
Theorem e25 : (forall x:U, (A x)) \/ (forall x:U, (B x)) -> forall x:U, ~(~(A x) /\ ~(B x)).
Proof.
intros a_x_or_b_x x.
unfold not; intro not_a_x_and_not_b_x.
elim not_a_x_and_not_b_x; intros not_a_x not_b_x.
elim a_x_or_b_x.
- intro a_x.
apply not_a_x; apply a_x.
- intro b_x.
apply not_b_x; apply b_x.
Qed.

End Ejercicio2.


(* Ejercicio 2.3 *)
Section Ejercicio3.

Variable U   : Set.
Variable A B : U -> Prop.
Variable P Q : Prop.
Variable R S : U -> U -> Prop.

Definition Reflexiva := forall x:U, (R x x).
Definition Simetrica := forall x y:U, R x y -> R y x.
Definition Transitiva := forall x y z:U, R x y /\ R y z -> R x z.

Definition H1 := Reflexiva.
Definition H2 := forall x y z:U, (R x y) /\ (R x z) -> (R y z).

(* Ej 2.3.1 *)
Theorem e231: H1 /\ H2 -> Reflexiva /\ Simetrica /\ Transitiva.
Proof.
intro h1_and_h2; elim h1_and_h2; intros h1 h2.
split.
(* Reflexividad *)
exact h1.
split.
(* Simetria *)
intros x y r_x_y.
apply (h2 x y x).
split; [exact r_x_y | exact (h1 x)].
(* Transitividad *)
intros x y z r_x_y_and_r_y_z.
apply (h2 y x z).
elim r_x_y_and_r_y_z; intros r_x_y r_y_z.
split.
-apply (h2 x y x);split; [exact r_x_y | exact (h1 x)].
-exact r_y_z.
Qed.

Definition Asimetrica := forall x y:U, R x y -> ~ R y x.
Definition Irreflexiva := forall x:U, ~ (R x x).

(* Ej 2.3.2 *)
Lemma e232 : Asimetrica -> Irreflexiva.
Proof.
intros asim x.
unfold not; intro r_x_x.
apply (asim x x).
-exact r_x_x.
-exact r_x_x.
Qed.

End Ejercicio3.


(* Ejercicio 2.4 *)
Section Ejercicio4.

Variable U : Set.
Variable A B : U->Prop.
Variable R : U->U->Prop.

(* Ej 2.4.1 *)
Theorem e41: (exists x:U, exists y:U, (R x y)) -> exists y:U, exists x:U, (R x y).
Proof.
intro exists_x_y.
elim exists_x_y.
intro x.
intro exists_y.
elim exists_y.
intro y.
intro r_x_y.
exists y.
exists x.
exact r_x_y.
Qed.

(* Ej 2.4.2 *)
Theorem e42: (forall x:U, A(x)) -> ~ exists x:U, ~ A(x).
Proof.
intro forall_x_a.
unfold not.
intro exists_x_no_a.
elim exists_x_no_a.
intros x no_a.
apply no_a.
apply (forall_x_a x).
Qed.

(* Ej 2.4.3 *)
Theorem e43: (exists x:U, ~(A x)) -> ~(forall x:U, (A x)).
Proof.
unfold not.
intro exists_x_no_a.
elim exists_x_no_a.
intros x no_a.
intro forall_x_a.
apply no_a.
apply (forall_x_a x).
Qed.

(* Ej 2.4.4 *)
Theorem e44: (forall x:U, ((A x) /\ (B x))) -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
intro forall_x_a_y_b.
split.
- intro x.
  apply (forall_x_a_y_b x).
- intro x.
  apply (forall_x_a_y_b x).
Qed.

(* Ej 2.4.5 *)
Theorem e45: (exists x:U, (A x \/ B x)) -> (exists x:U, A x) \/ (exists x:U, B x).
Proof.
intro exists_x_a_o_b.
elim exists_x_a_o_b.
intros x a_o_b.
elim a_o_b.
- intro a_x.
  left.
  exists x.
  exact a_x.
- intro b_x.
  right.
  exists x.
  exact b_x.
Qed.

(* Ej 2.4.6 *)
Theorem e46: (forall x:U, A x) \/ (forall y:U, B y) -> forall z:U, A z \/ B z.
Proof.
intro o.
elim o.
- intro forall_x_a.
  intro x.
  left.
  apply forall_x_a.
- intro forall_x_b.
  intro x.
  right.
  apply forall_x_b.
Qed.

End Ejercicio4.


(* Ejercicio 5 *)
Section Ejercicio5.

Variable nat      : Set.
Variable S        : nat -> nat.
Variable a b c    : nat.
Variable odd even : nat -> Prop.
Variable P Q      : nat -> Prop.
Variable f        : nat -> nat.

(* Ej 2.5.1 *)
Theorem e51: forall x:nat, exists y:nat, (P(x)->P(y)).
Proof.
intro x.
exists x.
intro p_x.
exact p_x.
Qed.

(* Ej 2.5.2 *)
Theorem e52: exists x:nat, (P x) -> (forall y:nat, (P y)->(Q y)) -> (exists z:nat, (Q z)).
Proof.
exists a.
intro p_a.
intro forall_x_p_q.
exists a.
apply forall_x_p_q.
exact p_a.
Qed.

(* Ej 2.5.3 *)
Theorem e53: even(a) -> (forall x:nat, (even(x)->odd (S(x)))) -> exists y: nat, odd(y).
Proof.
intro even_a.
intro forall_x_even_odd_s.
exists (S(a)).
apply forall_x_even_odd_s.
exact even_a.
Qed.

(* Ej 2.5.4 *)
Theorem e54: (forall x:nat, P(x) /\ odd(x) ->even(f(x)))
                            -> (forall x:nat, even(x)->odd(S(x)))
                            -> even(a)
                            -> P(S(a))
                            -> exists z:nat, even(f(z)).
Proof.
intro func.
intro func2.
intro even_a.
intro p_s_a.
exists (S(a)).
apply func.
split.
- exact p_s_a.
- apply func2.
  exact even_a.
Qed.

End Ejercicio5.


(* Ejercicio 2.7 *)
Section Ejercicio7.

Variable U   : Set.
Variable A B : U -> Prop.

(* Ej 2.7.1 *)
Theorem e71: (forall x:U, ((A x) /\ (B x))) -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
intro func; split; [apply func | apply func].
Qed.

(* Ej 2.7.2 *)
Theorem e72: (exists x:U, (A x \/ B x))->(exists x:U, A x )\/(exists x:U, B x).
Proof.
intro o; elim o; intros x a_o_b; elim a_o_b; intro f; [left | right]; exists x; exact f.
Qed.

(* Ej 2.7.3 *)
Theorem e73: (forall x:U, A x) \/ (forall y:U, B y) -> forall z:U, A z \/ B z.
Proof.
intro a_o_b; elim a_o_b; intros f x; [left | right]; apply f.
Qed.

End Ejercicio7.


(* Ejercicio 2.8 *)
Section Ejercicio8.

Variables U : Set.
Variables T V : U -> Prop.
Variables R : U -> U -> Prop.

(* Ej 2.8.1 *)
Theorem e81: (exists y : U, forall x : U, R x y) -> forall x : U, exists y : U, R x y.
Proof.
intros exists_r_x_y x0.
elim exists_r_x_y.
intros x1 y.
exists x1.
apply y.
Qed.

(* Ej 2.8.1 *)
Theorem e82: (exists x:U, True) /\ (forall x:U, (T x) \/ (V x)) -> (exists z:U, (T z)) \/ (exists w:U, (V w)).
Proof.
intro and.
elim and.
intros true forall_a_t_o_v.
elim true.
intros x t.
elim (forall_a_t_o_v x).
- intro t_x.
  left.
  exists x.
  exact t_x.
- intro v_x.
  right.
  exists x.
  exact v_x.
Qed.

(* 
Ej 2.8.3: La proposición (exists x:U, True) en e82 es necesaria para poder probar el teorema ya que necesito 
tener un elemento del conjunto U para poder instanciar el forall.
*)

End Ejercicio8.


(* Ejercicio 2.9 *)
Section Ejercicio9.
Require Import Classical.
Variables U : Set.
Variables A : U -> Prop.

(* Ej 2.9.1 *)
Lemma not_ex_not_forall: (~exists x :U, ~A x) -> (forall x:U, A x).
Proof.
unfold not.
intro e.
intro x.
elim (classic (A x)).
- intro a_x.
  exact a_x.
- intro no_a_x.
  absurd (exists x : U, A x -> False).
  exact e.
  exists x.
  exact no_a_x.
Qed.

(* Ej 2.9.2 *)
Lemma not_forall_ex_not: (~forall x :U, A x) -> (exists x:U,  ~A x).
Proof.
unfold not.
intro no_forall_x_a.
apply NNPP.
unfold not.
intro e.
apply no_forall_x_a.
apply not_ex_not_forall.
exact e.
Qed.

End Ejercicio9.


(* Ejercicio 2.10 *)

Section Ejercicio10.
Variable nat : Set.
Variable  O  : nat.
Variable  S  : nat -> nat.

Axiom disc   : forall n:nat, ~O=(S n).
Axiom inj    : forall n m:nat, (S n)=(S m) -> n=m.
Axiom allNat : forall n: nat, n = O \/ exists m: nat, S m = n.

Variable sum prod : nat->nat->nat.

Axiom sum0   : forall n :nat, (sum n O)=n.
Axiom sumS   : forall n m :nat, (sum n (S m))=(S (sum n m)).
Axiom prod0  : forall n :nat, (prod n O)=O.
Axiom prodS  : forall n m :nat, (prod n (S m))=(sum n (prod n m)).

(* Ej 2.10.1 *)
Lemma L10_1: (sum (S O) (S O)) = (S (S O)).
Proof.
rewrite (sumS (S O) O).
rewrite (sum0 (S O)).
reflexivity.
Qed.

(* Ej 2.10.2 *)
Lemma L10_2: forall n :nat, ~(O=n /\ (exists m :nat, n = (S m))).
Proof.
intros n and.
elim and.
intros n_0 e_n_sm.
elim e_n_sm.
intros m n_sm.
apply (disc m).
rewrite <- n_0 in n_sm.
exact n_sm.
Qed.

(* Ej 2.10.3 *)
Lemma prod_neutro: forall n :nat, (prod n (S O)) = n.
Proof.
intro n.
rewrite prodS.
rewrite prod0.
rewrite sum0.
reflexivity.
Qed.

(* Ej 2.10.4 *)
Lemma diff: forall n:nat, ~(S (S n))=(S O).
Proof.
intros n H.
apply (inj (S n) O) in H.
apply (disc n).
symmetry.
exact H.
Qed.

(* Ej 2.10.5 *)
Lemma L10_3: forall n: nat, exists m: nat, prod n (S m) = sum n n. 
Proof.
intro n; exists (S O).
rewrite prodS; rewrite prodS.
rewrite prod0.
rewrite sum0.
reflexivity.
Qed.

(* Ej 2.10.6 *)
Lemma L10_4: forall m n: nat, n <> O -> sum m n <> O.  
Proof.
intros m n n_not_0 sum_m_n.
elim (allNat n).
- intro n_0.
  absurd (n = O).
  exact n_not_0.
  exact n_0.
- intro e; elim e; intros.
  rewrite <- H in sum_m_n.
  rewrite sumS in sum_m_n.
  apply (disc (sum m x)).
  symmetry.
  exact sum_m_n.
Qed.

(* Ej 2.10.7 *)
Lemma L10_5: forall m n: nat, sum m n = O -> m = O /\ n = O.  
Proof.
intros n m sum_0.
elim (allNat m); elim (allNat n); intros; split; try assumption.
- rewrite H0 in sum_0.
  rewrite sum0 in sum_0.
  exact sum_0.
- elim H0; intros.
  rewrite <- H3 in sum_0.
  rewrite sumS in sum_0.
  elim (disc (sum n x)).
  symmetry.
  exact sum_0.
- elim H0; intros.
  rewrite <- H3 in sum_0.
  rewrite sumS in sum_0.
  elim (disc (sum n x)).
  symmetry.
  exact sum_0.
- elim H0; intros.
  rewrite <- H3 in sum_0.
  rewrite sumS in sum_0.
  elim (disc (sum n x)).
  symmetry.
  exact sum_0.
Qed.

(* Lema auxiliar utilizado en la prueba de L10_6 *)
Lemma lemma_aux: forall n m: nat, ~(sum (S n) m = O).
Proof.
intros n m.
elim (allNat m).
- intro m0.
  rewrite m0.
  rewrite sum0.
  intro H.
  apply (disc n).
  symmetry.
  exact H.
- intro e; elim e; intros.
  rewrite <- H.
  rewrite sumS.
  intro H0.
  apply (disc (sum (S n) x)).
  symmetry.
  exact H0.
Qed.

(* Ej 2.10.8 *)
Lemma L10_6: forall m n: nat, prod m n = O -> m = O \/ n = O.  
Proof.
intros m n prod_0.
elim (allNat n); elim (allNat m); intros.
- left; exact H.
- right; exact H0.
- left; exact H.
- elim H; intros.
  elim H0; intros.
  rewrite <- H3 in prod_0.
  rewrite <- H4 in prod_0.
  rewrite prodS in prod_0.
  elim (lemma_aux x (prod (S x) x0)).
  exact prod_0.
Qed.


End Ejercicio10.
