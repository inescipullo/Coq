(* Practica 1 *)

Section P1.
Variables A B C:Prop. (* son tipos *)

(*
Al costado de cada linea aparecen la cantidad de secuencias a probar
*)

(* Ej 1.1 *)

Theorem e11: A->A.
Proof.
  intro H.
  exact H. (* assumption *)
  Show Proof.
Qed.


(* Ej 1.2 *)
Theorem e12: A->B->A.
Proof.
  intro A1.
  intro B1.
  assumption.
Qed.

(* Ej 1.3 *)
Theorem e13: (A->(B->C))->(A->B)->(A->C).
Proof.
intros f g x.
Show Proof.
apply f.
Show Proof.
  assumption. (* a / x*)
  Show Proof.
    apply g.
    Show Proof.
      assumption.
Qed.

(*Ej 2.1 *)
Theorem e21: (A->B)->(B->C)->A->C.
Proof.
intros g f a.
Show Proof.
  apply f.
  Show Proof.
    apply g.
    Show Proof.
      assumption.
Qed.

(*Ej 2.2 *)
Theorem e22: (A->B->C)->B->A->C.
Proof.
intros f g x.
Show Proof.
  apply f.
  Show Proof.
    assumption.
    Show Proof.
      assumption.
Qed.

(*Ej 3.1 *)
Theorem e31_1: A->A->A.
Proof.
intros A1 A2.
assumption.
(* exact A2 para asegurarse que sean distintas *)
Qed.

Theorem e31_2: A->A->A.
Proof.
intro A1.
intro A2.
exact A1.
Qed.

(* Ej 3.2 *)
Theorem e32_1: (A->B->C)->A->(A->C)->B->C.
Proof.
intros f g x.
Show Proof.
  intro b.
  apply x.
  assumption.
Qed.

Theorem e32_2: (A->B->C)->A->(A->C)->B->C.
Proof.
intros f a g b.
apply g.
exact a.
Qed.

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
Show Proof.
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
(* neutro de las tacticas - idtac*)
Theorem e46: (A \/ B) -> (B \/ A).
Proof.
intro or; elim or; [right | left]; assumption.
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
unfold not.
Show Proof.
intro y.
elim y.
intro a.
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

(* Ej 7.1 *)
Theorem e71: A \/ ~A -> ~~A->A.
Proof.
intro aonoa.
elim aonoa.
  (*1*) intro a.
        intro aff.
        exact a.
  (*2*) intro af.
        intro aff.
        absurd (A -> False).
        exact aff.
        exact af.
Qed.

(*
a -> b <-> noa o b
*)

(* Ej 7.2 *)
Theorem e72: A\/~A -> ((A->B) \/ (B->A)).
Proof.
unfold not.
intro aonoa.
elim aonoa.
(* 1 *) intro a.
        right.
        intro b.
        exact a.
(* 2 *) intro noa.
        left.
        intro a.
        absurd A.
        exact noa.
        exact a.
Qed.



(* Ej 7.3 *)
Theorem e73: (A \/ ~A) -> ~(A /\ B) -> ~A \/ ~B.
Proof.
intro aonoa.
elim aonoa.
(*1*) intro a.
      unfold not.
      intro noayb.
      right.
      intro b.
      apply noayb.
      split.
      exact a.
      exact b.
(*2*) intro noa.
      intro noayb.
      left.
      exact noa.
Qed.


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

Theorem e83aux: forall A:Prop, A->~~A.
Proof.
intro A0.
intro a0.
elim (classic (~A0)).
(*1*)intro noa0.
     absurd A0.
     exact noa0.
     exact a0.
(*2*)intro nonoa0.
     exact nonoa0.
Qed.

(* Ej 8.3 *)
Theorem e83: forall A B:Prop, ~(A/\B)-> ~A \/ ~B.
Proof.
intros A0 B0.
elim (classic A0).
(*1*)intro a0.
     intro noayb.
     elim (classic B0).
     (*a*)intro b0.
          absurd (~(A0 /\B0)).
            cut (A0 /\ B0).
            (*A*)intro a0yb0.
                 apply (e83aux (A0 /\ B0)).
                 exact a0yb0.
            (*B*)split.
                 exact a0.
                 exact b0.
           exact noayb.
     (*b*)intro nob0.
          right.
          exact nob0.
(*2*)intro noa0.
     intro noa0yb0.
     left.
     exact noa0.
Qed.

(* EL 8.3 DE LA ENTREGA ES EL 7.3 ADAPTADO *)

End Logica_Clasica.


Section Traducciones.

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


(* Ej 10 y 11 *)
(* Formalizaciones a cargo del estudiante *)

(* Ej 11 *)
Variable MD: Prop. (* usa medias rojas *)
Variable ES: Prop. (* es escocés *)
Variable KL: Prop. (* usa kilt *)
Variable CA: Prop. (* es casado *)
Variable DO: Prop. (* sale los domingos *)


Hypothesis R1: ~ES -> MD.  (* Regla 1: Todo no escocés debe usar medias rojas *)
    (* Regla 2: Todo miembro usa kilt o no usa medias rojas *)
(* Regla 3: Los miembros casados no salen los domingos *)
(* Regla 4: Un miembro sale los domingos si y sólo si es escocés *)
(* Regla 5: Todo miembro que usa kilt es escocés y es casado *)
(* Regla 6: Todo miembro escocés usa kilt *)

End Traducciones. 

Section EJ12.
(* Ej 12 *)
(* Definiciones *)
Variable PF:Prop. (* el paciente tiene fiebre *)
Variable PA:Prop. (* el paciente tiene piel amarillenta *)
Variable PH:Prop. (* el paciente tiene hepatitis *)
Variable PR:Prop. (* el paciente tiene rubeola *)

Hypothesis Regla1: (PF \/ PA) -> (PH \/ PR). 
(* Si el paciente tiene fiebre o el paciente tiene la piel amarillenta, 
entonces tiene hepatitis o rubeola *) (*tiene hep o rubeola*)
Hypothesis Regla2: ~PR \/ PF.
(* El paciente no tiene rubeola o tiene fiebre.  *) (*puede o no tener rubeola*)
Hypothesis Regla3: PH /\ ~PR -> PA.
(* Si el paciente tiene hepatitis, pero no la rubeola, entonces tiene la piel
amarillenta. *) (*si hep y no rubeola -> piel amarill -> no puede (tener hep y no rub)*)
(* no tiene piel amarilla -> no (tiene hep y no rubeola)) = notienehep o nono tiene rub*)
(*tiene hep 
  apply r3
  rub **aca se nec logica clasica
no tiene hep
  rub*) (* pero no tengo logica clasica*)

(*
PH /\ PR
PH /\ ~PR -> se descarta por esto ~(PH /\ ~PR)
PR /\ ~PH
~PR /\ ~PH -> se descarta con el or
*)

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
            elim nopaypf.
            intro nopa.
            intro pf.
            exact nopa.
            apply Regla3.
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


Theorem ej12a2: (~PA /\ PF) -> ~(PH /\ ~PR).
Proof.
intro nopaypf.
elim nopaypf.
intro nopa.
intro pf.
unfold not.
intro phynopr.
elim phynopr.
intro ph.
intro nopr. (*no hacian falta estos intros*)
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

End EJ12.