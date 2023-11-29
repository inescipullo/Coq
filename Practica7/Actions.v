(*******************************************************************
 * Este archivo especifica las acciones Como transformadores de estado.
 * LAS DEFINICIONES DADAS PUEDEN SER USADAS DIRECTAMENTE O CAMBIADAS.
 ******************************************************************)
Load "/home/administrador/Descargas/tpcoq/State".

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
                  -> (aos_activity s) = running 
                   -> exists (ma : madd), 
                      (va_mapped_to_ma s va ma 
                        -> match memory s ma with
                            | Some page => is_RW (page_content page)
                            | _ => False
                           end)
    | write va val => (ctxt_vadd_accessible ctxt) va = true 
                        -> (aos_activity s) = running 
                         -> exists (ma : madd), 
                            (va_mapped_to_ma s va ma 
                              -> match memory s ma with
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

  (* Action postconditions *)
  Definition Post (s : State) (a : Action) (s' : State) : Prop :=
    match a with
    | read va => s = s'
    | write va val => exists (ma : madd), (va_mapped_to_ma s va ma 
                                          -> (memory s') = 
                                              update (memory s) ma
                                                 (mk_page (RW (Some val)) 
                                                        (Os (active_os s)))
                                           ) -> differ_at_most_memory s s' ma
    | chmod => (trusted_os ctxt s -> 
                 differ_in_state s s' svc running)
               \/ 
               (~(trusted_os ctxt s) -> 
                differ_in_state s s' usr running)
    end.

(* if the hypervisor (hypervisor running si activity es waiting)
 or a trusted OS is running 
the processor must be in supervisor mode*)
  Definition valid_state_iii (s : State) : Prop :=  
  ((aos_activity s) = waiting) \/ 
    ((aos_activity s) = running -> trusted_os ctxt s) 
  -> (aos_exec_mode s) = svc.
  
  Definition inyective {A B : Set} (pmap : A ⇸ B) :=
    forall x y, pmap x = pmap y -> x = y.

  Definition valid_state_v (s : State) : Prop :=
  ...

  Definition valid_state_vi (s : State) : Prop :=
  ...  
  
  Definition valid_state (s : State) : Prop :=
    valid_state_iii s /\ valid_state_v s /\ valid_state_vi s.
  
  Inductive one_step : State -> Action -> State -> Prop :=
  ...
 
  Notation "a ⇒ s ↪ s'" := (one_step s a s') (at level 50).


  Theorem one_step_preserves_prop_iii : forall (s s' : State) (a : Action),
      a ⇒ s ↪ s' -> valid_state_iii s'.
  Proof.
  ...
  Qed. 


  Theorem read_isolation : forall (s s' : State) (va : vadd),
  ...  
  Proof.
  ...
  Qed.

End Actions.