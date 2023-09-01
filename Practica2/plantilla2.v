Section Ejercicio1.

Variable U  : Set.
Variable A B: U -> Prop.
Variable P Q: Prop.
Variable R S: U -> U -> Prop.

Theorem e11 : (forall x:U, A(x)) -> forall y:U, A(y).
Proof.
intro a_x; apply a_x.
Qed.

Theorem e12 : (forall x y:U, (R x y)) -> forall x y:U, (R y x).
Proof.
intro r_x_y.
intro x; intro y.
apply r_x_y.
(* mas explicitamente
   apply (r_x_y y x). *)
Qed.


Theorem e13 : (forall x: U, ((A x)->(B x)))
                        -> (forall y:U, (A y))
                          -> (forall z:U, (B z)).
Proof.
intro a_x_to_b_x; intro a_y.
intro z.
(* Forma más compacta de hacer esto? *)
apply (a_x_to_b_x z).
apply (a_y z).
Qed.

End Ejercicio1.

Section Ejercicio2.

Variable U  : Set.
Variable A B: U -> Prop.
Variable P Q: Prop.
Variable R S: U -> U -> Prop.

Theorem e21 : (forall x:U, ((A x)-> ~(forall x:U, ~ (A x)))).
Proof.
intros x a_x.
unfold not.
intro not_a_y.
apply (not_a_y x).
exact a_x.
Qed.

Theorem e22 : (forall x y:U, ((R x y)))-> (forall x:U, (R x x)).
Proof.
intros r_x_y x.
apply (r_x_y x).
Qed.

Theorem e23 : (forall x:U, ((P -> (A x))))
                        -> (P -> (forall x: U, (A x))).
Proof.
intros a_x p x.
apply a_x; exact p.
Qed.


Theorem e24 : (forall x:U, ((A x) /\ (B x)))
                        -> (forall x:U, (A x))
                          -> (forall x:U, (B x)).
Proof.
intros a_x_and_b_x a_x x.
apply (a_x_and_b_x x).
Qed.


Theorem e25 : (forall x:U, (A x)) \/ (forall x:U, (B x)) -> 
                      forall x:U, ~(~(A x) /\ ~(B x)).
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

Theorem e25_2 : (forall x:U, (A x)) \/ (forall x:U, (B x)) -> 
                      forall x:U, (A x) \/ (B x).
Proof.
intros a_x_or_b_x x; elim a_x_or_b_x.
- left; apply H.
- right; apply H.
Qed.

End Ejercicio2.

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

Lemma e232 : Asimetrica -> Irreflexiva.
Proof.
intros asim x.
unfold not; intro r_x_x.
apply (asim x x).
(* R x x -> R x x -> False 
   Resta probar R x x 2 veces *)
-exact r_x_x.
-exact r_x_x.
Qed.

End Ejercicio3.

Section Ejercicio4.

Variable U : Set.
Variable A B : U->Prop.
Variable R : U->U->Prop.

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

Theorem e44: (forall x:U, ((A x) /\ (B x))) -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
intro forall_x_a_y_b.
split.
- intro x.
  apply (forall_x_a_y_b x).
- intro x.
  apply (forall_x_a_y_b x).
Qed.


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



Section Ejercicio5.

Variable nat      : Set.
Variable S        : nat -> nat.
Variable a b c    : nat.
Variable odd even : nat -> Prop.
Variable P Q      : nat -> Prop.
Variable f        : nat -> nat.


Theorem e51: forall x:nat, exists y:nat, (P(x)->P(y)).
Proof.
intro x.
exists x.
intro p_x.
exact p_x.
Qed.


Theorem e52: exists x:nat, (P x) -> (forall y:nat, (P y)->(Q y)) -> (exists z:nat, (Q z)).
Proof.
exists a.
intro p_a.
intro forall_x_p_q.
exists a.
apply forall_x_p_q.
exact p_a.
Qed.


Theorem e53: even(a) -> (forall x:nat, (even(x)->odd (S(x)))) -> exists y: nat, odd(y).
Proof.
intro even_a.
intro forall_x_even_odd_s.
exists (S(a)).
apply forall_x_even_odd_s.
exact even_a.
Qed.


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


Section Ejercicio6.

Variable nat : Set.
Variable S   : nat -> nat.
Variable le  : nat -> nat -> Prop.
Variable f   : nat -> nat.
Variable P   : nat -> Prop.

Axiom le_n: forall n:nat, (le n n).
Axiom le_S: forall n m:nat, (le n m) -> (le n (S m)).
Axiom monoticity: forall n m:nat, (le n m) -> (le (f n) (f m)).


Lemma le_x_Sx: forall x:nat, (le x (S x)).
Proof.
intro x.
apply le_S.
apply le_n.
Qed.

Lemma le_x_SSx: forall x:nat, (le x (S (S x))).
Proof.
intro x.
apply le_S; apply le_S.
apply le_n.
Qed.

Theorem T1: forall a:nat, exists b:nat, (le (f a) b).
Proof.
intro a.
exists (f(a)).
apply monoticity.
apply le_n.
Qed.

End Ejercicio6.


Section Ejercicio7.

Variable U   : Set.
Variable A B : U -> Prop.

Theorem e71: (forall x:U, ((A x) /\ (B x))) -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
intro func; split; [apply func | apply func].
Qed.

Theorem e72: (exists x:U, (A x \/ B x))->(exists x:U, A x )\/(exists x:U, B x).
Proof.
intro o; elim o; intros x a_o_b; elim a_o_b; intro f; [left | right]; exists x; exact f.
Qed.

Theorem e73: (forall x:U, A x) \/ (forall y:U, B y) -> forall z:U, A z \/ B z.
Proof.
intro a_o_b; elim a_o_b; intros f x; [left | right]; apply f.
Qed.

End Ejercicio7.


Section Ejercicio8.

Variables U : Set.
Variables T V : U -> Prop.
Variables R : U -> U -> Prop.

Theorem e81: (exists y : U, forall x : U, R x y) -> forall x : U, exists y : U, R x y.
Proof.
intros exists_r_x_y x0.
elim exists_r_x_y.
intros x1 y.
exists x1.
apply y.
Qed.

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
Parte 8.3. La proposición (exists x:U, True) en e82 es necesaria para poder probar el teorema ya que necesito 
tener un elemento del conjunto U para poder instanciar el forall.
*)

End Ejercicio8.


Section Ejercicio9.
Require Import Classical.
Variables U : Set.
Variables A : U -> Prop.

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

Axiom reflexivity: forall n: nat, n = n.

Lemma symmetry: forall n m: nat, n = m -> m = n.
Proof.
intros n m n_e_m.
rewrite n_e_m.
apply (reflexivity m).
Qed.

Lemma transitivity: forall n m: nat, n = m -> exists p: nat, n = p /\ p = m.
Proof.
intros n m n_e_m.
exists n.
split.
- apply (reflexivity n).
- rewrite n_e_m.
  apply (reflexivity m).
Qed.


Lemma L10_1: (sum (S O) (S O)) = (S (S O)).
Proof.
  
Admitted.

Lemma L10_2: forall n :nat, ~(O=n /\ (exists m :nat, n = (S m))).
Proof.
  
Qed.

Lemma prod_neutro: forall n :nat, (prod n (S O)) = n.
Proof.
  
Qed.

Lemma diff: forall n:nat, ~(S (S n))=(S O).
Proof.
  
Qed.

Lemma L10_3: forall n: nat, exists m: nat, prod n (S m) = sum n n. 
Proof.
  ...
Qed.

Lemma L10_4: forall m n: nat, n <> O -> sum m n <> O.  
Proof.
  ...
Qed.

Lemma L10_5: forall m n: nat, sum m n = O -> m = O /\ n = O.  
Proof.
  ...
Qed.

Lemma L10_6: forall m n: nat, prod m n = O -> m = O \/ n = O.  
Proof.
  ...
Qed.


End Ejercicio10.



Section Ejercicio11.

Variable le : nat->nat->Prop.
Axiom leinv: forall n m:nat, (le n m) -> n=O \/
      (exists p:nat, (exists q:nat, n=(S p)/\ m=(S q) /\ (le p q))).

Lemma notle_s_o: forall n:nat, ~(le (S n) O).
Proof.
  
Qed.

End Ejercicio11.
