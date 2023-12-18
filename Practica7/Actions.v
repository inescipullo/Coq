(*******************************************************************
 * Este archivo especifica las acciones Como transformadores de estado.
 * LAS DEFINICIONES DADAS PUEDEN SER USADAS DIRECTAMENTE O CAMBIADAS.
 ******************************************************************)
Load "/home/administrador/Documentos/Coq/Practica7/State".
(* Load "/Users/inescipullo/Documents_/Coq/Practica7/State". *)

Parameter ctxt : context.

Section Actions.

  Inductive Action :=
  | read (va : vadd)
  | write (va: vadd) (val: value)
  | chmod.

  (* Action preconditions *)
  Definition Pre (s : State) (a : Action) : Prop :=
    match a with
    | read va => (ctxt_vadd_accessible ctxt) va = true 
                 /\ (aos_activity s) = running
                 /\ exists (ma : madd),
                      va_mapped_to_ma s va ma
                      /\ match memory s ma with
                          | Some page => is_RW (page_content page)
                          | _ => False
                         end
    | write va val => (ctxt_vadd_accessible ctxt) va = true 
                      /\ (aos_activity s) = running
                      /\ exists (ma : madd),
                           va_mapped_to_ma s va ma
                           /\ match memory s ma with
                               | Some page => is_RW (page_content page)
                               | _ => False
                              end
    | chmod => (aos_activity s) = waiting ->
                  match ((oss s) (active_os s)) with
                   | Some os => hcall os = None
                   | _ => False
                  end
    end.

Definition differ_in_state (s s': State) (em : exec_mode) (act : os_activity) :=
   aos_exec_mode s' = em
/\ aos_activity s' = act
/\ active_os s = active_os s'
/\ oss s = oss s'
/\ hypervisor s = hypervisor s'
/\ memory s = memory s'.

Definition differ_at_most_memory (s s': State) (ma: madd) : Prop :=
   aos_activity s = aos_activity s'
/\ aos_exec_mode s = aos_exec_mode s'
/\ active_os s = active_os s'
/\ oss s = oss s'
/\ hypervisor s = hypervisor s'
/\ forall (m: madd), m <> ma -> (memory s) m = (memory s') m.


  (* Action postconditions *)
  Definition Post (s : State) (a : Action) (s' : State) : Prop :=
    match a with
    | read va => s = s'
    | write va val => exists (ma : madd), va_mapped_to_ma s va ma 
                                          /\ (memory s') =
                                              update (memory s) ma
                                                 (mk_page (RW (Some val))
                                                   (Os (active_os s)))
                                          /\ differ_at_most_memory s s' ma
    | chmod => (trusted_os ctxt s /\ differ_in_state s s' svc running)
               \/
               (~(trusted_os ctxt s) /\ differ_in_state s s' usr running)
    end.

(* if the hypervisor (hypervisor running si activity es waiting)
 or a trusted OS is running 
the processor must be in supervisor mode*)

  Definition valid_state_iii (s : State) : Prop :=
  (aos_activity s = waiting) \/ (aos_activity s = running /\ trusted_os ctxt s)
    -> (aos_exec_mode s) = svc.

  Definition inyective {A B : Set} (pmap : A ⇸ B) :=
    forall x y, pmap x = pmap y -> x = y.

(*the hypervisor maps an OS physical address to a machine address owned by
that same OS. This mapping is also injective*)
Definition valid_state_v (s : State) : Prop :=
  forall (ma : madd) (pg : page) (pa : padd) (pm : padd -> option madd),
      (hypervisor s) (active_os s) = Some pm
      /\ pm pa = Some ma
      /\ memory s ma = Some pg
      /\ page_owned_by pg = Os (active_os s)
      /\ inyective pm.

(*  all page tables of an OS o
map accessible virtual addresses to pages owned by o and not accessible ones to
pages owned by the hypervisor *)
Definition valid_state_vi (s : State) : Prop :=
  forall (pg pg' : page) (vtm : vadd -> option madd) (va : vadd) (ma : madd) (o : os_ident),
    page_content pg = PT vtm 
    /\ page_owned_by pg = Os o
    /\ vtm va = Some ma
    /\ memory s ma = Some pg'
    /\ (ctxt_vadd_accessible ctxt va = true -> page_owned_by pg' = Os o)
    /\ (ctxt_vadd_accessible ctxt va = false -> page_owned_by pg' = Hyp).

(*
Es algo que debatimos pero consideramos que tanto las propiedades 5 como la 6
deberían quedar formuladas así:
forall (ma : madd) (pg : page) (pa : padd) (pm : padd -> option madd),
      (hypervisor s) (active_os s) = Some pm
      /\ pm pa = Some ma
      /\ memory s ma = Some pg
      -> page_owned_by pg = Os (active_os s)
         /\ inyective pm.

  forall (pg pg' : page) (vtm : vadd -> option madd) (va : vadd) (ma : madd) (o : os_ident),
    page_content pg = PT vtm 
    /\ page_owned_by pg = Os o
    /\ vtm va = Some ma
    /\ memory s ma = Some pg'
    -> (ctxt_vadd_accessible ctxt va = true -> page_owned_by pg' = Os o)
        /\ (ctxt_vadd_accessible ctxt va = false -> page_owned_by pg' = Hyp).

Pero la realidad es que con esta variante del valid_state_v no pudimos
probar read_isolation
*)

  Definition valid_state (s : State) : Prop :=
    valid_state_iii s /\ valid_state_v s /\ valid_state_vi s.

  Inductive one_step : State -> Action -> State -> Prop :=
  | step : forall (s s': State) (a: Action), 
      valid_state(s) -> Pre s a -> Post s a s' -> one_step s a s'.

  Notation "a ⇒ s ↪ s'" := (one_step s a s') (at level 50).


  Theorem one_step_preserves_prop_iii : forall (s s' : State) (a : Action),
      a ⇒ s ↪ s' -> valid_state_iii s'.
  Proof.
  intros.
  destruct H.
  induction a.

  (*Read*)
  - simpl in H1.
    rewrite H1 in H.
    unfold valid_state in H.
    elim H. intros.
    exact H2.
  
  (*Write*)
  - inversion H0.
    elim H3. intros. clear H3.
    inversion H1. elim H3. intros. clear H3.
    elim H7. intros. clear H7.
    elim H8. intros. clear H8. elim H9. intros. clear H9.
    elim H10. intros. clear H10. clear H11.
    unfold valid_state in H.
    unfold valid_state_iii in H.
    elim H. intros. clear H11.
    unfold valid_state_iii. intros.
    clear H2. clear H5. clear H6. clear H3. 

    (* Vemos caso waiting o running y trusted *)
    elim H11.

      (*Sabemos que esta running*)
      -- rewrite <- H7. rewrite H4. discriminate.

      (*Probamos que vale viendo que vale exec mode s = svc 
        usando que para s' vale trusted_os y que sus exec
        modes son iguales*)
      -- clear H7.
         intros. elim H2. intros.
         rewrite <- H8.
         apply H10.
         right.
         split.
          --- exact H4.
          --- unfold trusted_os.
              rewrite H9. exact H5.

  (*Chmod*)
  - inversion H1. elim H2. intros. clear H2. unfold differ_in_state in H4.
    (*Sacamos la información que queremos de differ_in_state*)
    elim H4. intros. clear H4. elim H5. intros. clear H5. clear H6.
      elim H3.

    (*Analizamos por casos si es trusted os s o no*)

    -- unfold valid_state_iii. intros.
       exact H2. 

    -- elim H2. intros. clear H2.
       unfold valid_state_iii. intros.

       elim H4. intros. clear H4. elim H6. intros. clear H6. elim H7. intros. clear H7. clear H8.

       (*Vemos caso waiting o running y trusted*)
       elim H2; intros. 
        --- absurd (aos_activity s' = waiting). (*sabemos que esta running*)
            ---- rewrite H4 in H7. discriminate.
            ---- exact H7.
        --- unfold trusted_os in H3. (*Usamos que no trusted_os de s*)
            rewrite H6 in H3. (*para probar que no trusted_os de s'*)
            elim H7. intros. clear H7. (*y como por hip de --- es trusted*)
            absurd (trusted_os ctxt s'). (*tenemos contradicción*)
            ---- exact H3.
            ---- exact H9.
 Qed.

  Theorem read_isolation : forall (s s' : State) (va : vadd), read va ⇒ s ↪ s' -> 
  exists ma: madd, va_mapped_to_ma s va ma /\ exists pg: page, Some pg = (memory s) ma /\ (page_owned_by pg) = Os (active_os s).
  Proof.

  intros.
  inversion H.
  inversion H2.
  rewrite <- H6.
  elim H1. intros. elim H8. intros.
  elim H10. intros.
  elim H11. intros.

  exists x.
  split.

  (*Sabemos que vale el mapeo por la Pre de read*)
  - exact H12.
  
  (*Vemos que la pagina a la que apunta, gracias al valid state 5,
   es del SO*)
  - destruct (memory s x).
    -- exists p.
       split.
       --- reflexivity.

       --- unfold valid_state in H0.
           elim H0. intros. elim H15. intros.
           unfold valid_state_v in H16.
           apply (H16 x p).
           ---- destruct (oss s (active_os s)) eqn:hay_os.
                ----- exact (curr_page o).
                ----- unfold va_mapped_to_ma in H12.
                      destruct (oss s (active_os s)).
                      ------ discriminate.
                      ------ contradiction.
           ---- destruct (hypervisor s (active_os s)) eqn:hay_map.
                ----- exact p0.
                ----- unfold va_mapped_to_ma in H12.
                      destruct (oss s (active_os s)).
                      ------ destruct (hypervisor s (active_os s)) eqn:hay_map2.
                             * discriminate.
                             * contradiction.
                      ------ contradiction.
    -- contradiction.
  Qed.

End Actions.