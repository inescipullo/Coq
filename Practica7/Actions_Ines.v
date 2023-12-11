(*******************************************************************
 * Este archivo especifica las acciones Como transformadores de estado.
 * LAS DEFINICIONES DADAS PUEDEN SER USADAS DIRECTAMENTE O CAMBIADAS.
 ******************************************************************)
(* Load "/home/administrador/Descargas/tpcoq/State". *)
Load "/Users/inescipullo/Documents_/Coq/Practica7/State".

Parameter ctxt : context.

Section Actions.

Definition differ_at_most_memory (s s': State) (ma: madd) : Prop :=

              active_os s = active_os s'

           /\ aos_exec_mode s = aos_exec_mode s'

           /\ aos_activity s = aos_activity s'

           /\ oss s = oss s'

           /\ hypervisor s = hypervisor s'

           /\ forall (m: madd), m <> ma -> (memory s) m = (memory s') m.
  
  Inductive Action :=
  | read (va : vadd)
  | write (va: vadd) (val: value)
  | chmod.

  (* Action preconditions *)
  Definition Pre (s : State) (a : Action) : Prop :=
    match a with
    | read va => (ctxt_vadd_accessible ctxt) va = true
                      /\ (aos_activity s) = running
                      /\ exists (ma : madd) (pg : page),
                          (va_mapped_to_ma s va ma
                          /\ memory s ma = Some pg
                          /\ is_RW (page_content pg))
    | write va val => (ctxt_vadd_accessible ctxt) va = true
                      /\ (aos_activity s) = running
                      /\ exists (ma : madd) (pg : page),
                          (va_mapped_to_ma s va ma
                          /\ memory s ma = Some pg
                          /\ is_RW (page_content pg))
    | chmod => (aos_activity s) = waiting
               /\ (exists (o : os), oss s (active_os s) = Some o /\ hcall o = None)
    end.

Definition differ_in_state (s s': State) (em : exec_mode) (act : os_activity) :=
(aos_exec_mode s') = em 
/\ (aos_activity s') = act
/\ (active_os s) = (active_os s')
/\ (oss s) = (oss s')
/\ (hypervisor s) = (hypervisor s')
/\ (memory s) = (memory s').

  (* Action postconditions *)
  Definition Post (s : State) (a : Action) (s' : State) : Prop :=
    match a with
    | read va => s = s'
    | write va val => exists (ma : madd), va_mapped_to_ma s va ma 
                                          /\ (memory s') = 
                                              update (memory s) ma
                                                (mk_page (RW (Some val)) (Os (active_os s)))
                                          /\ differ_at_most_memory s s' ma
    | chmod => (trusted_os ctxt s /\ differ_in_state s s' svc running)
               \/
               (~(trusted_os ctxt s) /\ differ_in_state s s' usr running)
    end.

(* if the hypervisor (hypervisor running si activity es waiting)
 or a trusted OS is running 
the processor must be in supervisor mode*)
  Definition valid_state_iii (s : State) : Prop :=
  ((aos_activity s) = waiting) \/
    ((aos_activity s) = running /\ trusted_os ctxt s)
  -> (aos_exec_mode s) = svc.

  Definition inyective {A B : Set} (pmap : A ⇸ B) :=
    forall x y, pmap x = pmap y -> x = y.

(*

(* paged_owned_by ((memory s) ((hypervisor s) (active_os s) phyadd)) = (active_os s) *)
  Definition valid_state_v_aux (s : State) : Prop :=
    forall phyadd : padd, 
      match (hypervisor s) (active_os s) with
        | Some map => 
            match map phyadd with
              | Some mchadd => 
                  match (memory s) mchadd with
                     | Some page => 
                         match page_owned_by page with
                            | Os osid => osid = (active_os s)
                            | Hyp => False
                            | No_Owner => False
                         end
                     | _ => False
                  end
              | _ => False
            end
        | _ => False
      end.

(*the hypervisor maps an OS physical address to a machine address owned by
that same OS. This mapping is also injective*)
  Definition valid_state_v (s : State) : Prop :=
  match (hypervisor s) (active_os s) with
    | Some map => inyective map /\ valid_state_v_aux s
    | _ => False
  end.


(*  all page tables of an OS o
map accessible virtual addresses to pages owned by o and not accessible ones to
pages owned by the hypervisor *)
  Definition valid_state_vi (s : State) : Prop :=
  forall mchadd : madd, 
   match (memory s) mchadd with
     | Some page =>
        match page_content page with
          | PT pgtable => 
              forall viradd : vadd, 
               match pgtable viradd with
                | Some maddok => 
                    match (memory s) maddok with
                     | Some pageok => 
                              (ctxt_vadd_accessible ctxt) viradd = true -> 
                                page_owned_by pageok = Os (active_os s)
                              /\
                              (ctxt_vadd_accessible ctxt) viradd = false ->
                                page_owned_by pageok = Hyp
                     | _ => True
                    end
                | _ => True
              end
          | _ => True
        end
     | _ => True (* si no hay match quiero que sea vdd *)
    end.

*)

Definition Prop5 (s : State) : Prop :=
  forall (pa : padd) (pm : padd -> option madd) (ma : madd) (pg : page),
      (hypervisor s) (active_os s) = Some pm
      /\ pm pa = Some ma
      /\ memory s ma = Some pg
      /\ page_owned_by pg = Os (active_os s)
      /\ inyective pm.

Definition Prop6 (s : State) : Prop :=
  forall (pg pg' : page) (vtm : vadd -> option madd) (va : vadd) (ma : madd) (o : os_ident),
    page_content pg = PT vtm 
    /\ page_owned_by pg = Os o
    /\ vtm va = Some ma
    /\ memory s ma = Some pg'
    /\ (ctxt_vadd_accessible ctxt va = true -> page_owned_by pg' = Os o)
    /\ (ctxt_vadd_accessible ctxt va = false -> page_owned_by pg' = Hyp).

Definition valid_state (s : State) : Prop :=
    valid_state_iii s /\ Prop5 s /\ Prop6 s.

(*
  Definition valid_state (s : State) : Prop :=
    valid_state_iii s /\ valid_state_v s /\ valid_state_vi s.
*)

  Inductive one_step : State -> Action -> State -> Prop :=
  | step : forall (s s': State) (a: Action), 
      valid_state(s) -> Pre s a -> Post s a s' -> one_step s a s'.

  Notation "a ⇒ s ↪ s'" := (one_step s a s') (at level 50).



  Theorem one_step_preserves_prop_iii : forall (s s' : State) (a : Action),
      a ⇒ s ↪ s' -> valid_state_iii s'.
  Proof.
  intros.
  inversion H.
  inversion H0.
  unfold valid_state_iii. intros.
  destruct a.
  - inversion H2.
    rewrite H9 in H6.
    elim H6; intros.
    + reflexivity.
    + exact H8.
  - inversion H2.
    elim H9. intros.
    elim H11. intros.
    unfold differ_at_most_memory in H13.
    elim H13. intros. elim H15. intros. elim H17. intros.
    rewrite <- H16.
    apply H6.
    elim H8; intros.
    + left.
      rewrite H18.
      exact H20.
    + right.
      elim H20. intros.
      split.
      rewrite H18.
      exact H21.
      unfold trusted_os.
      rewrite H14.
      exact H22.
  - inversion H2.
    + elim H9. intros.
      unfold differ_in_state in H11.
      elim H11. intros.
      exact H12.
    + elim H9. intros.
      unfold differ_in_state in H11.
      elim H11. intros. elim H13. intros. elim H15. intros.
      elim H8; intros.
      * absurd (aos_activity s' = waiting).
        rewrite H14. discriminate.
        exact H18.
      * unfold trusted_os in H10.
        rewrite H16 in H10.
        elim H18. intros.
        absurd (trusted_os ctxt s').
        exact H10.
        exact H20.
  Qed.


  Theorem read_isolation : forall (s s' : State) (va : vadd), read va ⇒ s ↪ s' -> 
  exists ma: madd, va_mapped_to_ma s va ma /\ 
  exists pg: page, Some pg = (memory s) ma /\ (page_owned_by pg) = Os (active_os s).
  Proof.
  intros.
  inversion H.
  unfold valid_state in H0. elim H0. intros. elim H7. intros.
  inversion H2.
  unfold Pre in H1.
  elim H1. intros. elim H12. intros. elim H14. intros. elim H15. intros.
  exists x.
  split.
  - rewrite <- H10.
    elim H16. intros.
    exact H17.
  - destruct (memory s x).
    + exists p.
      rewrite H10 in H8.
      elim (H8 (curr_page ) (hypervisor_map (active_os s')) x p).
    + contradiction H15.
  Qed.

Definition Prop5 (s : State) : Prop :=
  forall (pa : padd) (pm : padd -> option madd) (ma : madd) (pg : page),
      (hypervisor s) (active_os s) = Some pm
      /\ pm pa = Some ma
      /\ memory s ma = Some pg
      /\ page_owned_by pg = Os (active_os s)
      /\ inyective pm.


End Actions.