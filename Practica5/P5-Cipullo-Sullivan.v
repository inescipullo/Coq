(* Entrega Práctico 5 - CFPTT *)
(* Alumnas: Cipullo, Inés - Sullivan, Katherine *)


Section Ejercicio4.

Variable A : Set.
Inductive AB : Set := null_ab : AB
                    | cons_ab : A -> AB -> AB -> AB.

(* a *)
Inductive Pertenece (x : A) : AB -> Prop :=
 | here_ab : forall (l : AB) (r : AB), Pertenece x (cons_ab x l r)
 | there_lab : forall (l r : AB), Pertenece x l -> forall y : A, Pertenece x (cons_ab y l r)
 | there_rab : forall (l r : AB), Pertenece x r -> forall y : A, Pertenece x (cons_ab y l r).

(* b *)
Parameter eqGen : A->A->bool.
Fixpoint Borrar (x : A) (t : AB) {struct t} : AB :=
  match t with
   | null_ab => null_ab
   | cons_ab y l r => if eqGen x y then null_ab else cons_ab y (Borrar x l) (Borrar x r)
  end.

(* c *)
Axiom eqGen1: forall x:A, ~(eqGen x x) = false.
Lemma BorrarNoPertenece: forall (x:AB) (a:A), ~(Pertenece a (Borrar a x)).
Proof.
unfold not.
induction x; intros.
- simpl in H. inversion H.
- simpl in H.
  case_eq (eqGen a0 a); intro; rewrite H0 in H; inversion H.
  * rewrite H2 in H0.
    apply (eqGen1 a H0).
  * apply (IHx1 a0 H2).
  * apply (IHx2 a0 H2).
Qed.

(* d *)
Inductive SinRepetidos : AB -> Prop :=
 | sr_null : SinRepetidos null_ab
 | sr_cons : forall (x : A) (l r : AB), ~(Pertenece x l) -> ~(Pertenece x r) -> SinRepetidos (cons_ab x l r).

End Ejercicio4.


Section Ej5.

(* 1 *)
Definition Var := nat.

Inductive Exp : Set :=
  | Evar : Var -> Exp
  | Ebool : bool -> Exp
  | Eand : Exp -> Exp -> Exp
  | Enot : Exp -> Exp.


(* 2 *)
Definition Valor := bool.

Definition Memoria := Var -> Valor.

Definition lookup := 
fun (v: Var) (m : Memoria) => m v.

Inductive BEval : Exp -> Memoria -> Valor -> Prop :=
  | evar : forall (m:Memoria) (v:Var), BEval (Evar v) m (lookup v m)
  | eboolt : forall (m:Memoria), BEval (Ebool true) m true
  | eboolf : forall (m:Memoria), BEval (Ebool false) m false
  | eandl : forall (m:Memoria) (e1 e2:Exp), 
            BEval e1 m false -> BEval (Eand e1 e2) m false
  | eandr : forall (m:Memoria) (e1 e2:Exp),
            BEval e2 m false -> BEval (Eand e1 e2) m false
  | eandrl : forall (m:Memoria) (e1 e2:Exp), BEval e1 m true -> 
            BEval e2 m true -> BEval (Eand e1 e2) m true
  | enott : forall (m:Memoria) (e1:Exp),
            BEval e1 m true -> BEval (Enot e1) m false
  | enotf: forall (m:Memoria) (e1:Exp),
            BEval e1 m false -> BEval (Enot e1) m true.

(* 3 a *)
Theorem exp_true : forall (m:Memoria), ~BEval (Ebool true) m false.
Proof.
unfold not.
intros.
inversion H.
Qed.

(* 3 b *)
Theorem new_and : forall (m:Memoria) (e1 e2:Exp) (v:Valor),
BEval e1 m true -> BEval e2 m v -> BEval (Eand e1 e2) m v.
Proof.
intros. destruct e2.
- destruct v.
  -- constructor. exact H. exact H0.
  -- apply eandr. exact H0.
- destruct v. 
  -- apply eandrl. exact H. exact H0.
  -- apply eandr. exact H0.
- destruct v.
  -- constructor.
     exact H. exact H0.
  -- apply eandr.
     exact H0.
- destruct v.
  -- constructor. exact H. exact H0.
  -- apply eandr. exact H0.
Qed.

(* 3 c *)
Theorem determinismo : forall (m:Memoria) (e:Exp) (v1 v2:Valor),
BEval e m v1 -> BEval e m v2 -> v1=v2.
Proof.
induction e; intros.
- inversion H.
  inversion H0.
  reflexivity.
- inversion H.
  -- rewrite <- H2 in H0.
     inversion H0.
     reflexivity.
  -- rewrite <- H2 in H0.
     inversion H0.
     reflexivity.
- inversion H.
  -- inversion H0.
      --- reflexivity.
      --- reflexivity.
      --- apply IHe1. exact H5. exact H8.
  -- inversion H0.
      --- reflexivity.
      --- reflexivity.
      --- apply IHe2. exact H5. exact H11.
  -- inversion H0.
      --- apply IHe1. exact H3. exact H11.
      --- apply IHe2. exact H6. exact H11.
      --- reflexivity.
- inversion H.
  -- inversion H0.
     --- reflexivity.
     --- apply IHe. exact H6. exact H2.
  -- inversion H0.
     --- apply IHe. exact H6. exact H2.
     --- reflexivity.
Qed.

(* 3 d *)
Theorem no_e1: forall (m:Memoria) (e1 e2:Exp),
BEval e1 m false -> BEval (Enot (Eand e1 e2)) m true.
Proof.
intros.
constructor.
constructor.
exact H.
Qed.

(* 4 *)
Fixpoint beval (e:Exp) (m:Memoria) {struct e}: Valor :=
  match e with
   | Evar v0 => lookup v0 m
   | Ebool b => b
   | Eand e1 e2 => if beval e1 m then beval e2 m else false
   | Enot e1 => if beval e1 m then false else true
  end.

(* 5 *)
Theorem equiv : forall (e: Exp) (m:Memoria),
BEval e m (beval e m).
Proof.
intros. induction e.
- simpl. constructor.
- destruct b.
  -- simpl. constructor.
  -- simpl. constructor.
- simpl. destruct (beval e1 m).
  -- apply (new_and m e1 e2). exact IHe1. exact IHe2.
  -- constructor. exact IHe1.
- simpl. destruct (beval e m).
  -- constructor. exact IHe.
  -- constructor. exact IHe.
Qed.

End Ej5.


Section Ejercicio6.

(* 1 *)
Inductive Instr : Set :=
  | Skip : Instr
  | Assign : Var -> Exp -> Instr
  | IfThenElse : Exp -> Instr -> Instr -> Instr
  | WhileDo : Exp -> Instr -> Instr
  | Repeat : nat -> Instr -> Instr
  | BeginEnd : LInstr -> Instr

with LInstr : Set :=
  | Empty : LInstr
  | Seq : Instr -> LInstr -> LInstr.


(* 2 *)
Infix ";" := Seq (right associativity, at level 60).

(* 2 a *)
Variables v1 v2: Var.
Definition PP := BeginEnd (Assign v1 (Ebool true); Assign v2 (Enot (Evar v1)); Empty).
(*
Begin
 v1 := true ;
 v2 := ~v1
End
*)

(* 2 b *)
Variable aux: Var.
Definition swap := BeginEnd (Assign aux (Evar v1); Assign v1 (Evar v2); Assign v2 (Evar aux); Empty).
(*
Begin
 aux := v1 ;
 v1 := v2 ;
 v2 := aux
End
*)

(* 3 *)
Parameter eq_var : Var -> Var -> bool.
Definition update (mem: Memoria) (var: Var) (val: Valor) := (* -> Memoria *)
  fun v: Var => if eq_var v var then val else mem v.


(* 4 *)
Axiom reflexivity_eq_var : forall x : Var, eq_var x x = true.
Lemma LookupUpdate: forall (mem: Memoria) (var: Var) (val:Valor), lookup var (update mem var val) = val.
Proof.
intros.
unfold lookup.
unfold update.
rewrite reflexivity_eq_var.
reflexivity.
Qed.


(* 5 *)
Axiom symmetry_eq_var : forall x y : Var, eq_var x y = eq_var y x.
Lemma LookupUpdate2: forall (mem: Memoria) (var1 var2: Var) (val:Valor),
  eq_var var1 var2 = false -> lookup var2 (update mem var1 val) = lookup var2 mem.
Proof.
intros.
unfold lookup.
unfold update.
rewrite symmetry_eq_var.
rewrite H.
reflexivity.
Qed.


End Ejercicio6.


Section Ejercicio7.
Infix ";" := Seq (right associativity, at level 60).

(* 1 *)
Inductive Execute: Instr -> Memoria -> Memoria -> Prop :=
   | xSkip : forall m: Memoria, Execute Skip m m
   | xAss : forall (m: Memoria) (v: Var) (e: Exp) (w: Valor), 
            BEval e m w -> Execute (Assign v e) m (update m v w)
   | xIFthen : forall (m m1: Memoria) (e: Exp) (p1 p2: Instr),
               BEval e m true -> Execute p1 m m1 -> Execute (IfThenElse e p1 p2) m m1
   | xIFelse : forall (m m1: Memoria) (e: Exp) (p1 p2: Instr),
               BEval e m false -> Execute p2 m m1 -> Execute (IfThenElse e p1 p2) m m1
   | xWhileTrue : forall (m m1 m2: Memoria) (e: Exp) (p: Instr),
                  BEval e m true -> Execute p m m1 -> Execute (WhileDo e p) m1 m2 -> Execute (WhileDo e p) m m2
   | xWhileFalse : forall (m: Memoria) (e: Exp) (p: Instr),
                   BEval e m false -> Execute (WhileDo e p) m m
   | xRepeat0 : forall (m: Memoria) (p: Instr), Execute (Repeat 0 p) m m
   | xRepeatS : forall (m1 m2 m3: Memoria) (n: nat) (p: Instr),
                Execute p m1 m2 -> Execute (Repeat n p) m2 m3 -> Execute (Repeat (S n) p) m1 m3
   | xBeginEnd : forall (m m1: Memoria) (ps: LInstr),
                 ExecuteL ps m m1 -> Execute (BeginEnd ps) m m1
with ExecuteL : LInstr -> Memoria -> Memoria -> Prop :=
   | xEmptyblock : forall m: Memoria, ExecuteL Empty m m
   | xNext : forall (m m1 m2: Memoria) (p: Instr) (ps: LInstr),
             Execute p m m1 -> ExecuteL ps m1 m2 -> ExecuteL (p; ps) m m2.

(* 2 *)
Lemma ExecuteIf: forall (e: Exp) (p1 p2: Instr) (m m': Memoria), 
Execute (IfThenElse (Enot e) p1 p2) m m' -> Execute (IfThenElse e p2 p1) m m'.
Proof.
intros.
inversion H; inversion H5.
- apply xIFelse.
  exact H8.
  exact H6.
- apply xIFthen.
  exact H8.
  exact H6.
Qed.

(* 3 *)
Lemma ExecuteWhile: forall (p: Instr) (m m': Memoria), Execute (WhileDo (Ebool false) p) m m' -> m = m'.
Proof.
intros.
inversion H.
- inversion H2.
- reflexivity.
Qed.

(* 4 *)
Lemma ExecuteIfWhile: forall (e: Exp) (p: Instr) (m m': Memoria),
Execute (BeginEnd ((IfThenElse e p Skip); (WhileDo e p); Empty)) m m' -> Execute (WhileDo e p) m m'.
Proof.
intros.
inversion H.
inversion H1.
inversion H9.
inversion H6.
- apply (xWhileTrue m m3 m').
  + exact H21.
  + exact H22.
  + inversion H15.
    rewrite H25 in H12.
    exact H12.
- inversion H22.
  inversion H15.
  rewrite H27 in H12.
  exact H12.
Qed.

Lemma mas1 : forall n:nat, n+1 = S n.
Proof.
induction n.
- simpl. reflexivity.
- simpl. rewrite IHn. reflexivity.
Qed.

(* 5 *)
Lemma ExecuteRepeat: forall (n: nat) (p: Instr) (m1 m2: Memoria),
Execute (BeginEnd (p; (Repeat n p); Empty)) m1 m2 -> Execute (Repeat (n+1) p) m1 m2.
Proof.
intros.
inversion H.
inversion H1.
inversion H9.
inversion H15.
rewrite H18 in H12.
rewrite (mas1 n).
apply (xRepeatS m1 m4 m2 n p).
- exact H6.
- exact H12.
Qed.

(* 6 *)

Lemma ExecuteRepeat2: forall (n1 n2 : nat) (p: Instr) (ma mb mc: Memoria),
Execute (Repeat n1 p) ma mb -> Execute (Repeat n2 p) mb mc -> Execute (Repeat (n1+n2) p) ma mc.
Proof.
induction n1; intros; simpl.
- inversion H.
  exact H0.
- inversion H.
  apply (xRepeatS ma m2 mc).
    -- exact H3.
    -- apply (IHn1 n2 p m2 mb mc).
       --- exact H6.
       --- exact H0.
Qed.

(* 7 *)
Lemma ExecutePP: forall (m: Memoria) (v1 v2: Var), 
eq_var v1 v2 = false -> Execute (PP v1 v2) m (update (update m v1 true) v2 false).
Proof.
intros.
apply xBeginEnd.
apply (xNext m (update m v1 true) (update (update m v1 true) v2 false)).
- apply xAss.
  apply eboolt.
- apply (xNext (update m v1 true)
              (update (update m v1 true) v2 false)
              (update (update m v1 true) v2 false)).
  * apply xAss.
    apply enott.
    rewrite <- (LookupUpdate m v1 true).

    assert ((update m v1 true) = (update m v1 (lookup v1 (update m v1 true)))).
    rewrite LookupUpdate. reflexivity.

    rewrite <- H0.
    apply evar.
  * apply xEmptyblock.
Qed.

End Ejercicio7.