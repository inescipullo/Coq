(* Entrega Práctico 1 - CFPTT *)
(* Alumnas: Cipullo, Inés - Sullivan, Katherine *)

Section P1.
Variables A B C:Prop.

(* Ej 4.1 *)
Theorem e41: A -> ~~A.
Proof.
unfold not.
intros a impl.
apply impl.
assumption.
Qed.

(* Ej 4.2 *)
Theorem e42: A -> B -> (A /\ B).
Proof.
intros a b.
split.
assumption.
assumption.
Qed.

(* Ej 4.3 *)
Theorem e43: (A->B->C) -> (A/\B->C).
Proof.
intros impl and.
elim and.
assumption.
Qed.

(* Ej 4.4 *)
Theorem e44: A->(A\/B).
Proof.
intro a.
left.
assumption.
Qed.

(* Ej 4.5 *)
Theorem e45: B->(A\/B).
Proof.
intro b.
right.
assumption.
Qed.

(* Ej 4.6 *)
Theorem e46: (A \/ B) -> (B \/ A).
Proof.
intro or.
elim or.
(*1*) right.
      assumption.
(*2*) left.
      assumption.
Qed.

(* Ej 4.7 *)
Theorem e47: (A->C)->(B->C)->A\/B->C.
Proof.
intros ac bc aob.
elim aob.
assumption.
assumption.
Qed.

(* Ej 4.8 *)
Theorem e48: False->A.
Proof.
intro bottom.
elim bottom.
Qed.

(* Ej 5.1 *)
Theorem e51: (A->B)-> ~B-> ~A.
Proof.
intro ab.
unfold not.
intro bfalse.
intro a.
apply bfalse.
apply ab.
exact a.
Qed.

(* Ej 5.2 *)
Theorem e52: ~(A/\~A).
Proof.
unfold not.
intro a_y_noa.
elim a_y_noa.
intros a afalse.
apply afalse.
exact a.
Qed.

(* Ej 5.3 *)
Theorem e53: (A->B)-> ~(A/\~B).
Proof.
intro ab.
intro ayb.
elim ayb.
intro a.
unfold not.
intro bfalse.
apply bfalse.
apply ab.
exact a.
Qed.

(* Ej 5.4 *)
Theorem e54: (A/\B)->~(A->~B).
Proof.
intro ayb.
unfold not.
intro abfalse.
elim ayb.
exact abfalse.
Qed.

(* Ej 5.5 *)
Theorem e55: (~A /\ ~~A) -> False.
Proof.
unfold not.
intro y.
elim y.
intro afalse.
intro afalsefalse.
apply afalsefalse.
exact afalse.
Qed.

(* Ej 6.1 *)
Theorem e61: (A\/B) -> ~(~A/\~B).
Proof.
intro aob.
unfold not.
intro af_y_bf.
elim af_y_bf.
intro af.
intro bf.
elim aob.
exact af.
exact bf.
Qed.

(* Ej 6.2 *)
Theorem e62: A\/B <-> B\/A.
Proof.
unfold iff.
split.
(* 1 *)
    intro aob.
    elim aob.
      (*a*) intro a.
            right.
            exact a.
      (*b*) intro b.
            left.
            exact b.
(* 2 *)
  intro boa.
  elim boa.
      (*b*) intro b.
            right.
            exact b.
      (*a*) intro a.
            left.
            exact a.
Qed.

(* Ej 6.3 *)
Theorem e63: A\/B -> ((A->B)->B).
Proof.
intro aob.
intro ab.
elim aob.
  (*1*)
    exact ab.
  (*2*)
    intro b.
    exact b.
Qed.

End P1.

Section Logica_Clasica.
Variables A B C: Prop.

Require Import Classical.
Check classic.

(* Ej 8.1 *)
Theorem e81: forall A: Prop, ~~A->A.
Proof.
intro A0.
intro nonoa0.
elim (classic A0).
(*1*)intro a0.
     exact a0.
(*2*)intro noa0.
     absurd (~A0).
     exact nonoa0.
     exact noa0.
Qed.

(* Ej 8.2 *)
Theorem e82: forall A B:Prop, (A->B)\/(B ->A).
Proof.
intros A0 B0.
elim (classic A0).
(*1*)intro a0.
     right.
     intro b0.
     exact a0.
(*2*)intro noa0.
     left.
     intro a0.
     absurd A0.
     exact noa0.
     exact a0.
Qed.

(* Ej 8.3 *)
Theorem e83: forall A B:Prop, ~(A/\B)-> ~A \/ ~B.
Proof.
intros A0 B0.
elim (classic A0).
(*1*) intro a0.
      unfold not.
      intro noa0yb0.
      right.
      intro b0.
      apply noa0yb0.
      split.
      exact a0.
      exact b0.
(*2*) intro noa0.
      intro noa0yb0.
      left.
      exact noa0.
Qed.

End Logica_Clasica.

Section Ej9.

(* Ej 9 *)
(* Definiciones *)
Variables NM RED CONS UTIL : Prop.

Hypothesis H1 : ~NM \/ ~RED.
Hypothesis H2 : CONS \/ ~UTIL.

Theorem ej9 : NM /\ UTIL -> CONS /\ ~RED.
Proof.
intro nmyutil.
elim H2.
(*1*) intro cons.
      split.
      exact cons.
      elim H1.
      (*a*) intro nonm.
            elim nmyutil.
            intro nm.
            absurd NM.
            exact nonm.
            exact nm.
      (*b*) intro nored.
            exact nored.
(*2*) intro noutil.
      elim nmyutil.
      intro nm.
      intro util.
      absurd UTIL.
      exact noutil.
      exact util.
Qed.

End Ej9.

Section Ej12.

(* Ej 12 *)
(* Definiciones *)
Variable PF:Prop. (* el paciente tiene fiebre *)
Variable PA:Prop. (* el paciente tiene piel amarillenta *)
Variable PH:Prop. (* el paciente tiene hepatitis *)
Variable PR:Prop. (* el paciente tiene rubeola *)

Hypothesis Regla1: (PF \/ PA) -> (PH \/ PR). 
(* si el paciente tiene fiebre o el paciente tiene la piel amarillenta, 
entonces tiene hepatitis o rubeola *)

Hypothesis Regla2: ~PR \/ PF.
(* el paciente no tiene rubeola o tiene fiebre *)

Hypothesis Regla3: PH /\ ~PR -> PA.
(* si el paciente tiene hepatitis, pero no la rubeola, entonces tiene 
la piel amarillenta *)

(* Vamos a probar que el paciente que llegó, que no tiene la piel 
amarilla pero tiene fiebre, tiene hepatitis o rubeola, pero no 
puede tener hepatitis y no rubeola a la vez. *)

Theorem ej12a2: (~PA /\ PF) -> ~(PH /\ ~PR).
Proof.
intro nopaypf.
elim nopaypf.
intro nopa.
intro pf.
unfold not.
intro phynopr.
absurd PA.
(*1*) exact nopa.
(*2*) apply Regla3.
      exact phynopr.
Qed.


Theorem ej12a1: (~PA /\ PF) -> PH \/ PR.
Proof.
intro nopaypf.
apply Regla1.
left.
elim nopaypf.
intro nopa.
intro pf.
exact pf.
Qed.

Theorem ej12: (~PA /\ PF) -> (PH \/ PR) /\ ~(PH /\ ~PR).
Proof.
intro nopaypf.
split.
apply ej12a1.
exact nopaypf.
apply ej12a2.
exact nopaypf.
Qed.

(* En principio, leyendo el ejercicio el diagnóstico al que habíamos 
llegado era que el paciente sí tenía rubeola y podía o no tener 
hepatitis. Sin embargo, solo pudimos probarlo teniendo la hipótesis 
de la lógica clásica. Dejamos esa prueba acá. *)

Require Import Classical.
Check classic.

Theorem ej12a3: (~PA /\ PF) -> PR.
Proof.
intro nopaypf.
elim (classic PH).
(*1*) intro ph.
      elim (classic PR).
      (*a*) intro pr.
            exact pr.
      (*b*) intro nopr.
            absurd PA.
            (*A*) elim nopaypf.
                  intro nopa.
                  intro pf.
                  exact nopa.
            (*B*) apply Regla3.
                  split.
                  exact ph.
                  exact nopr.
(*2*) intro noph.
      elim (classic PR).
      (*a*) intro pr.
            exact pr.
      (*b*) intro nopr.
            absurd (PH \/ PR).
            (*A*) unfold not.
                  intro phypr.
                  elim phypr.
                  exact noph.
                  exact nopr.
            (*B*) apply Regla1.
                  left.
                  elim nopaypf.
                  intro nopa.
                  intro pf.
                  exact pf.
Qed.


End Ej12.

