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
                      (va_mapped_to_ma s va ma 
                        /\ match memory s ma with
                            | Some page => is_RW (page_content page)
                            | _ => False
                           end)
    | write va val => (ctxt_vadd_accessible ctxt) va = true 
                        /\ (aos_activity s) = running 
                         /\ exists (ma : madd), 
                            (va_mapped_to_ma s va ma 
                              /\ match memory s ma with
                                  | Some page => is_RW (page_content page)
                                  | _ => False
                                 end)
    | chmod => (aos_activity s) = waiting -> 
                  match ((oss s) (active_os s)) with 
                  | Some os => hcall os = None
                  | _ => False
                  end
    end.

Definition differ_in_state (s s': State) (em : exec_mode) (act : os_activity) :=
(aos_exec_mode s') = em 
/\ (aos_activity s') = act
/\ (active_os s) = (active_os s')
/\ (oss s) = (oss s')
/\ (hypervisor s) = (hypervisor s')
/\ (memory s) = (memory s').

Definition differ_at_most_memory (s s': State) (ma: madd) : Prop :=
  aos_activity s = aos_activity s'
/\ aos_exec_mode s = aos_exec_mode s'
/\  active_os s = active_os s'
/\ oss s = oss s'
/\ hypervisor s = hypervisor s'
/\ forall (m: madd), m <> ma -> (memory s) m = (memory s') m.
  

  (* Action postconditions *)
  Definition Post (s : State) (a : Action) (s' : State) : Prop :=
    match a with
    | read va => s = s'
    | write va val => exists (ma : madd), (va_mapped_to_ma s va ma 
                                          /\ (memory s') = 
                                              update (memory s) ma
                                                 (mk_page (RW (Some val)) 
                                                        (Os (active_os s)))
                                           ) 
                                          /\ differ_at_most_memory s s' ma
    | chmod => (trusted_os ctxt s /\ 
                 differ_in_state s s' svc running)
               \/ 
               (~(trusted_os ctxt s) /\ 
                differ_in_state s s' usr running)
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
(*   Definition valid_state_v (s : State) : Prop :=
  match (hypervisor s) (active_os s) with
    | Some map => inyective map /\ valid_state_v_aux s
    | _ => False
  end. *)

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
(*   Definition valid_state_vi (s : State) : Prop :=
  forall (p: page),
    match (page_content p), (page_owned_by p) with
      | PT pt, Os o => 
        forall viradd : vadd, 
          match pt viradd with
           | Some ma => 
               match (memory s) ma with
                  | Some pageok => 
                                (ctxt_vadd_accessible ctxt) viradd = true -> 
                                  page_owned_by pageok = Os o
                                /\
                                (ctxt_vadd_accessible ctxt) viradd = false ->
                                  page_owned_by pageok = Hyp
                   | _ => False
               end
           | _ => True
          end
      | _, _ => True
     end. *)

Definition valid_state_vi (s : State) : Prop :=
  forall (pg pg' : page) (vtm : vadd -> option madd) (va : vadd) (ma : madd) (o : os_ident),
    page_content pg = PT vtm 
    /\ page_owned_by pg = Os o
    /\ vtm va = Some ma
    /\ memory s ma = Some pg'
    /\ (ctxt_vadd_accessible ctxt va = true -> page_owned_by pg' = Os o)
    /\ (ctxt_vadd_accessible ctxt va = false -> page_owned_by pg' = Hyp).

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
  - simpl in H1.
    rewrite H1 in H.
    unfold valid_state in H.
    elim H. intros.
    exact H2.
  - inversion H0.
    elim H3. intros.
    inversion H1. elim H6. intros.
    unfold differ_at_most_memory in H8.
    elim H8. intros. elim H10. intros. elim H12. intros.
    unfold valid_state in H.
    unfold valid_state_iii in H.
    elim H. intros.
    unfold valid_state_iii. intros. (*Dejamos las hipótesis como nos interesan*)
    elim H17. (* Vemos caso waiting or running *)
      -- rewrite <- H9. rewrite H4. discriminate. (*Sabemos que esta running*)
      -- intros. elim H18. intros.
         rewrite <- H11. (*Probamos que vale viendo que vale exec mode s = svc*)
         apply H15. (*y para probar eso usamos que para s' vale trusted_os*)
         right.
         split.
          --- exact H4.
          --- unfold trusted_os.
              rewrite H13.
              exact H20.
  - inversion H1; elim H2; intros; unfold differ_in_state in H4;
      elim H4; intros. (*Analizamos por casos si es trusted os s o no*)
    -- unfold valid_state_iii. intros.
       exact H5. (*Por el differ_in_state sabemos que esta en svc*)
    -- elim H6. intros. elim H8. intros.
       unfold valid_state_iii. intros.
       elim H11; intros. (*Vemos si esta waiting or running y trusted*)
        --- absurd (aos_activity s' = waiting). (*sabemos que esta running*)
          rewrite H7. discriminate. (*por lo que absurdo que waiting*)
          exact H12.
        --- unfold trusted_os in H3. (*Usamos que no trusted_os de s*)
          rewrite H9 in H3. (*para probar que no trusted_os de s'*)
          elim H12. intros. (*y como por hip de --- es trusted*)
          absurd (trusted_os ctxt s'). (*tenemos contradicción*)
          exact H3.
          exact H14.
 Qed.

  Theorem read_isolation : forall (s s' : State) (va : vadd), read va ⇒ s ↪ s' -> 
  exists ma: madd, va_mapped_to_ma s va ma /\ exists pg: page, Some pg = (memory s) ma /\ (page_owned_by pg) = Os (active_os s).
  Proof.
  intros.
  inversion H.
  inversion H2.
  rewrite <- H6.
  unfold Pre in H1.
  elim H1. intros. elim H8. intros.
  elim H10. intros.
  elim H11. intros.
  exists x.
  split.
  - exact H12.
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