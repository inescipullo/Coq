(*******************************************************************
 * Este archivo especifica el estado y los elementos relacionados.
 * LAS DEFINCIONES DADAS PUEDEN SER USADAS DIRECTAMENTE O CAMBIADAS. 
 ******************************************************************)
(* Entrega Práctico 7 - CFPTT *)
(* Alumnas: Cipullo, Inés - Sullivan, Katherine *)

(* Shortcut notation for partial functions *)
Definition partial a b := a -> option b.
Notation "a ⇸ b" := (partial a b) (at level 51, right associativity).
(* NOTA: Con esto no es necesario usar Maps.v mencionado en el práctico 7 *)


Section State.

  (** Identificadores de OSs e Hypercalls *)
  Parameter os_ident : Set.
  Parameter os_ident_eq : forall oi1 oi2 : os_ident, {oi1 = oi2} + {oi1 <> oi2}.

  Parameter Hyperv_call : Set.

  (* Memoria y direcciones *)

  (** Direcciones Virtuales. **)
  Parameter vadd : Set.
  Parameter vadd_eq : forall va1 va2 : vadd, {va1 = va2} + {va1 <> va2}.

  (** Direcciones de Máquina. **)
  Parameter madd :  Set.
  Parameter madd_eq : forall ma1 ma2 : madd, {ma1 = ma2} + {ma1 <> ma2}.

  (** Direcciones Físicas **)
  Parameter padd : Set.
  Parameter padd_eq : forall pa1 pa2 : padd, {pa1 = pa2} + {pa1 <> pa2}.

  (** Memory values. **)
  Parameter value : Set.
  Parameter value_eq : forall val1 val2 : value, {val1 = val2} + {val1 <> val2}.


  (* Environment *)
  Record context : Set :=
    Context {
        (** una dirección virtual es accesible, no está reserveda por el HV **)
        ctxt_vadd_accessible: vadd -> bool;
        (** guest Oss (Confiable/No Confiable) **)
        ctxt_oss : os_ident -> bool
      }.
  

  (* Operative Systems *)
  Record os := mk_os { curr_page : padd; hcall : option Hyperv_call }.

  Definition oss_map := os_ident ⇸ os.

  (* Execution Modes *)
  Inductive exec_mode := usr | svc.
  Inductive os_activity := running | waiting.

  (* Memory Mappings *)
  Definition hypervisor_map := os_ident ⇸ padd ⇸ madd.

  Inductive content :=
  | RW (v : option value)
  | PT (va_to_ma : vadd ⇸ madd)
  | Other.

  Definition is_RW c :=
    match c with
    | RW _ => True
    | _ => False
    end.

  Inductive page_owner :=
  | Hyp
  | Os (osi : os_ident)
  | No_Owner.

  Record page := mk_page { page_content : content; page_owned_by : page_owner }.

  Definition system_memory := madd ⇸ page.

  Definition update mem addr page : system_memory :=
    fun addr' => if madd_eq addr' addr
                 then Some page
                 else mem addr'.

  (* States *)
  Record State :=
    mk_State {
        active_os : os_ident;
        aos_exec_mode : exec_mode;
        aos_activity : os_activity;
        oss : oss_map;
        hypervisor : hypervisor_map;
        memory : system_memory
      }.

  
Definition va_mapped_to_ma (s : State) (va : vadd) (ma : madd) :=
    match oss(s) (active_os(s)) with
      | Some os =>
      match hypervisor(s) (active_os(s)) with
        | Some hyp =>
        match hyp (curr_page(os)) with
          | Some madd =>
          match memory(s) madd with
            | Some page =>
            match page_content(page) with
              | PT mapping =>
              match mapping va with
                | Some ma' => ma' = ma
                | _ => False end
              | _ => False end
            | _ => False end
          | _ => False end
        | _ => False end
      | _ => False end.

  Definition trusted_os (ctxt : context) (s : State) : Prop :=
    ctxt_oss ctxt (active_os s) = true. 

End State.
