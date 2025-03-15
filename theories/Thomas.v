From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Std.

From Ltac2 Require Fresh.
From Ltac2 Require Import Control.
From Ltac2 Require Import Message.
From Ltac2 Require Import Std.
From Ltac2 Require Import Printf.

Import Ltac2.Notations.

Require Import DlStalk.Lemmas.
Require Import DlStalk.Tactics.
Require Import DlStalk.LTS.
Require Import DlStalk.Model.
Require Import DlStalk.ModelData.
Require Import DlStalk.Network.
Require Import DlStalk.SRPC.
Require Import DlStalk.Que.
Require Import DlStalk.Locks.
Require Import DlStalk.SRPC.
Require Import DlStalk.SRPCNet.
Require Import DlStalk.Transp.
Require Import DlStalk.Sound.
Require Import DlStalk.Compl.

From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Structures.Equalities.
Import ListNotations.
Open Scope string_scope.

(* this must be extracted or else coq bugs https://github.com/coq/coq/issues/19994 *)
Inductive Name_ : Set :=
| Initiator : string -> nat -> Name_
| Worker :> string -> Name_
.

Definition name_str (n : Name_) : option (list Byte.byte) :=
  match n with Worker n => Some (list_byte_of_string n) | _ => None end.
Definition str_name (s : list Byte.byte) : Name_ :=
  Worker (string_of_list_byte s).

String Notation Name_ str_name name_str : list_scope.

Lemma Name_neq_IW : forall i si sw, Initiator si i <> Worker sw. attac. Qed.
Lemma Name_neq_WI : forall i si sw, Worker sw <> Initiator si i. attac. Qed.
Hint Resolve Name_neq_WI Name_neq_IW : core.

Module Name_ <: UsualDecidableSet.
  Definition t' := Name_.
  Definition t := Name_.
  Definition eq := @eq t.

  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition eq_equiv := Build_Equivalence eq eq_refl eq_sym eq_trans.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof.
    intros x y.
    destruct x; destruct y; try (first [left; solve [eattac] | right; solve [eattac]]).
    - ltac1:(decide equality); eauto using PeanoNat.Nat.eq_dec, string_dec.
    - ltac1:(decide equality); eauto using PeanoNat.Nat.eq_dec, string_dec.
  Defined.

  Definition eqb : t -> t -> bool.
    intros x y. destruct (eq_dec x y) > [apply true | apply false].
  Defined.

  Lemma eqb_eq : forall x y : t, eqb x y = true <-> eq x y.
  Proof.
    intros x y. split; intros H.
    - destruct x; destruct y; unfold eqb in H.
      destruct (string_dec s s0), (PeanoNat.Nat.eq_dec n n0); subst.
      all: blast_cases; attac.
    - unfold eq, eqb, eq_dec in *; subst.
      blast_cases; auto.
  Qed.

  Lemma eqb_neq : forall x y : t, eqb x y = false <-> x <> y.
  Proof.
    intros x y. split; intros H.
    - destruct x; destruct y; unfold eqb in H.
      destruct (string_dec s s0), (PeanoNat.Nat.eq_dec n n0); subst.
      all: blast_cases; attac.
    - unfold eq, eqb, eq_dec in *; subst.
      blast_cases; attac.
  Qed.
End Name_.

Module Thomas.
  Module DetConf <: Compl.DETECT_CONF.
    Parameter Val : Set.

    Module NAME := Name_.
    Module TAG := Locks.Tag_.

    Declare Module NetMod : Network.NET_MOD(NAME).

    Definition Msg := @Compl.MProbe' NAME.t'.
    Definition MState := @Compl.MState' NAME.t'.
  End DetConf.


  Module Import Sound := ModelData.Empty <+ Sound.SOUND(DetConf). (* TODO fix separation: this includes Compl *)

  Lemma Name_eqb_refl (n0 : Name) : NAME.eqb n0 n0 = true.
  Proof. apply NAME.eqb_eq. auto. Qed.

  Hint Rewrite -> Name_eqb_refl using assumption : LTS LTS_concl.


  Import SrpcNet.

  Definition recvq (cont : Name -> Val -> Proc) : Proc :=
    PRecv (
        fun m =>
          let (c, t) := m in
          match t with
          | R => None
          | Q => Some (cont c)
          end
      ).

  Definition recvr (from : Name) (cont : Val -> Proc) : Proc :=
    PRecv (
        fun m =>
          let (s, t) := m in
          match t with
          | Q => None
          | R => if NAME.eqb s from
                then Some cont
                else None
          end
      ).


  Definition call (to : string) (arg : Val) (cont : Val -> Proc) :=
    PSend (Worker to, Q) arg (recvr (Worker to) cont).


  Inductive Handler (state_t : Set) :=
  | h_reply (reply : Val) (next_state : state_t) : Handler state_t
  | h_call (to : string) (arg : Val) (cont : Val -> Handler state_t) : Handler state_t
  .


  Inductive GenState (state_t : Set) :=
  | GSReady : state_t -> GenState _ | GSHandle : Name -> Handler state_t -> GenState _.

  Record GenServer_ (state_t : Set) :=
    { gs_state : GenState state_t
    ; gs_handler : option string -> Val -> state_t -> Handler state_t
    }.

  CoFixpoint run_gen_server [state_t : Set] :=
    fun (impl : GenServer_ state_t) =>
      match impl with
      | {|gs_state:=GSReady _ gss; gs_handler:=gsh|} =>
          recvq (
              fun from arg =>
                let name := match from with Worker n => Some n | _ => None end in
                run_gen_server {|gs_state:=GSHandle _ from (gsh name arg gss); gs_handler:=gsh|}
            )
      | {|gs_state:=GSHandle _ client (h_reply _ reply next_state); gs_handler:=gsh|} =>
          PSend (client, R) reply (run_gen_server {|gs_state := GSReady _ next_state; gs_handler := gsh|})
      | {|gs_state:=GSHandle _ client (h_call _ to arg handler_cont); gs_handler:=gsh|} =>
          call to arg (fun v =>
                         run_gen_server {|gs_state:=GSHandle _ client (handler_cont v); gs_handler := gsh|}
            )
      end.


  Import Locks.

  Import Srpc.
  Import SrpcDefs.


  Lemma SRPC_recvr_h client serv cont :
    (forall v, SRPC (Work client) (cont v)) ->
    SRPC_Busy (BLock client serv) (recvr serv cont).

  Proof.
    intros.
    constructor; intros.
    - eexists.
      constructor.
      rewrite Name_eqb_refl. auto.
    - kill H0.
      blast_cases; attac.
      rewrite NAME.eqb_eq in Heqb.
      attac.
    - kill H0.
      blast_cases; attac.
      rewrite NAME.eqb_eq in Heqb.
      specialize (H v).
      kill H.
      attac.
  Qed.

  Lemma SRPC_recvr client serv cont :
    (forall v, SRPC (Work client) (cont v)) ->
    SRPC (Lock client serv) (recvr serv cont).

  Proof.
    intros.
    constructor; intros.
    - eapply SRPC_recvr_h; auto.
    - kill H0; bs.
    - kill H0; bs.
    - kill H0.
      blast_cases; attac.
    - kill H0; bs.
  Qed.

  Lemma SRPC_call client cont :
    (forall v, SRPC (Work client) (cont v)) ->
    forall to arg, SRPC (Work client) (call to arg cont).

  Proof.
    intros.
    unfold call.
    assert (SRPC (Lock client (Worker to)) (recvr (Worker to) cont)) by eauto using SRPC_recvr.
    clear H.
    constructor; intros; doubt.
    - constructor; intros; doubt.
      kill H0; attac.
    - kill H.
  Qed.


  Lemma SRPC_gen_server_hwork [state_t] :
    forall client st gsh,
      SRPC_Busy (BWork client) (@run_gen_server state_t {|gs_state:=GSHandle _ client st; gs_handler:=gsh|}).

  Proof.
    intros.
    induction st; attac.
    - constructor; intros; doubt.
      + rewrite (unfold_Proc (run_gen_server _)) in H.
        kill H.
      + rewrite (unfold_Proc (run_gen_server _)) in H.
        kill H.
      + rewrite (unfold_Proc (run_gen_server _)) in H.
        kill H.
      + rewrite (unfold_Proc (run_gen_server _)).
        attac.
      + rewrite (unfold_Proc (run_gen_server _)).
        attac.
    - rewrite (unfold_Proc (run_gen_server _)).
      simpl.
      constructor; intros; doubt.
      kill H0.
      constructor; intros; doubt.
      + eexists.
        constructor.
        rewrite Name_eqb_refl.
        eattac.
      + kill H0.
        blast_cases; attac.
        rewrite NAME.eqb_eq in Heqb.
        attac.
      + kill H0.
        destruct n.
        destruct t; doubt.
        blast_cases; doubt.
        kill H1.
        apply NAME.eqb_eq in Heqb.
        subst.
        attac.
  Qed.


  CoFixpoint SRPC_gen_server [state_t] :
    forall st gsh,
    SRPC Free (@run_gen_server state_t {|gs_state:=GSReady _ st; gs_handler:=gsh|})
  with
  SRPC_gen_server_work [state_t] :
    forall client st gsh,
      SRPC (Work client) (@run_gen_server state_t {|gs_state:=GSHandle _ client st; gs_handler:=gsh|}).

  Proof.
    all: intros.
    - constructor; intros.
      + clear C.
        eexists.
        rewrite (unfold_Proc (run_gen_server _)).
        simpl.
        constructor.
        attac.
      + rewrite (unfold_Proc (run_gen_server _)) in H.
        simpl in H.
        kill H.
        destruct n.
        destruct t; doubt.
        kill H0.
        exists n, v.
        split; auto.
    - constructor; intros; doubt.
      + apply SRPC_gen_server_hwork.
      + rewrite (unfold_Proc (run_gen_server _)) in H.
        simpl in *.
        blast_cases; doubt.
        attac.
      + rewrite (unfold_Proc (run_gen_server _)) in H.
        simpl in *.
        blast_cases; doubt.
        kill Heqp.
        attac.
        constructor; intros; doubt.
        * constructor; intros; doubt.
          -- eexists.
             constructor.
             rewrite Name_eqb_refl.
             attac.
          -- kill H.
             blast_cases; attac.
             apply NAME.eqb_eq in Heqb.
             attac.
          -- kill H.
             destruct n.
             destruct t; doubt.
             kill H0.
             blast_cases; doubt.
             kill H.
             eapply SRPC_gen_server_hwork.
        * kill H.
          blast_cases; doubt.
          kill H0.
          apply NAME.eqb_eq in Heqb.
          subst.
          auto.
      + rewrite (unfold_Proc (run_gen_server _)) in H.
        simpl in *.
        blast_cases; doubt.
      + rewrite (unfold_Proc (run_gen_server _)) in H.
        simpl in *.
        blast_cases; doubt.
  Qed.


  Definition gen_server [state_t : Set] (init : state_t) (handle_call : option string -> Val -> state_t -> Handler state_t) :=
    run_gen_server {|gs_state:=GSReady _ init; gs_handler:=handle_call|}.


  Arguments h_call {state_t} to arg cont.
  Arguments h_reply {state_t} reply next_state.

  Definition Echo := gen_server tt (fun _ v st => h_reply v st).

  Definition Finger name i to arg :=
    match i with
    | 0 => call to arg (fun v => PSend (Initiator name 1, R) v Echo)
    | S i' => recvr (Initiator name i') (fun v => PSend (Initiator name (S i), R) v Echo)
    end.

  Definition Init name to arg := Finger name 0 to arg.

  Record ServiceConf :=
    sconf { state_t : Set
          ; init : state_t
          ; handle_call (from : option string) (msg : Val) (state : state_t) : Handler state_t
      }.

  Record InitConf := iconf { target : string; arg : Val }.

  Record NetConf :=
    { services : string -> ServiceConf
    ; inits : string -> InitConf
    }.


  Definition gen_net (conf : NetConf) : PNet :=
    NetMod.init (
        fun n => match n with
              | Worker name =>
                  match services conf name with
                    sconf _ init_call_ handle_call => serv [] (gen_server init_call_ handle_call) []
                  end
              | Initiator name i =>
                  match inits conf name with
                  | iconf to arg => serv [] (Finger name i to arg) []
                  end
              end
      ).


  Lemma SRPC_Finger : forall name to arg i,
      SRPC (Lock (Initiator name (S (S i))) (Initiator name i)) (Finger name (S i) to arg).

  Proof.
    intros.
    constructor; intros; doubt.
    - constructor; intros; doubt.
      + eexists.
        constructor.
        rewrite Name_eqb_refl.
        attac.
      + kill H.
        blast_cases; eattac.
        apply NAME.eqb_eq in Heqb.
        attac.
      + kill H.
        destruct n.
        blast_cases; doubt.
        rewrite NAME.eqb_eq in Heqb.
        kill H0.
        constructor; intros; doubt.
    - kill H.
      blast_cases; doubt.
      apply NAME.eqb_eq in Heqb.
      kill H0.
      constructor; intros; doubt.
      + constructor; intros; doubt.
      + kill H.
        unfold Echo.
        apply SRPC_gen_server.
  Qed.


  Lemma SRPC_Init : forall name to arg,
      SRPC (Work (Initiator name 1)) (Init name to arg).

  Proof.
    intros.
    constructor; intros; doubt.
    - constructor; intros; doubt.
      kill H.
      constructor; intros; doubt.
      + eexists.
        constructor.
        rewrite Name_eqb_refl.
        attac.
      + kill H.
        blast_cases; eattac.
        apply NAME.eqb_eq in Heqb.
        attac.
      + kill H.
        destruct n.
        blast_cases; doubt.
        rewrite NAME.eqb_eq in Heqb.
        kill H0.
        constructor; intros; doubt.
    - kill H.
      constructor; intros; doubt.
      + constructor; intros; doubt.
        * eexists.
          constructor.
          rewrite Name_eqb_refl.
          attac.
        * kill H.
          blast_cases; eattac.
          apply NAME.eqb_eq in Heqb.
          attac.
        * kill H.
          destruct n.
          blast_cases; doubt.
          rewrite NAME.eqb_eq in Heqb.
          kill H0.
          constructor; intros; doubt.
      + kill H.
        blast_cases; doubt.
        apply NAME.eqb_eq in Heqb.
        kill H0.
        constructor; intros; doubt.
        * constructor; intros; doubt.
        * kill H.
          unfold Echo.
          apply SRPC_gen_server.
  Qed.


  Lemma gen_net_SRPC : forall conf, SRPC_net (gen_net conf).

  Proof.
    unfold SRPC_net.
    intros.
    unfold gen_net.
    rewrite NetMod.init_get.
    destruct n as [name [|i] | name].
    - destruct (inits conf name).
      exists (Work (Initiator name 1)).
      eapply SRPC_Init.
    - destruct (inits conf name).
      exists (Lock (Initiator name (S (S i))) (Initiator name i)).
      eapply SRPC_Finger with (to:=target0)(arg:=arg0).
    - destruct (services conf name).
      exists Free.
      apply SRPC_gen_server.
  Qed.


  Lemma gen_net_service_wf : forall conf, service_wf_net (gen_net conf).

  Proof.
    unfold service_wf_net.
    intros.
    unfold gen_net.
    rewrite NetMod.init_get.
    destruct n as [name [|i] | name].
    - destruct (inits conf name).
      exists (Work (Initiator name 1)).
      constructor; attac.
      eapply SRPC_Init.
    - destruct (inits conf name).
      exists (Lock (Initiator name (S (S i))) (Initiator name i)).
      constructor; attac.
      eapply SRPC_Finger with (to:=target0)(arg:=arg0).
    - destruct (services conf name).
      exists Free.
      constructor; attac.
      apply SRPC_gen_server.
  Qed.


  Lemma gen_lock_set_finger : forall conf name i,
      lock (gen_net conf) (Initiator name (S i)) (Initiator name i).

  Proof.
    intros.
    eexists [_]. 1: attac.
    unfold lock_set.
    unfold gen_net.
    rewrite NetMod.init_get.
    blast_cases.
    assert (Decisive (Finger name (S i) target0 arg0)).
    {
      enough (AnySRPC (Finger name (S i) target0 arg0)) by auto using SRPC_Decisive.
      eexists; eauto using SRPC_Finger.
    }
    constructor; auto.
    eapply SRPC_Lock_lock.
    eauto using SRPC_Finger.
  Qed.

  Lemma gen_lock_set_init : forall conf name other,
      ~ lock (gen_net conf) (Initiator name 0) other.

  Proof.
    intros.
    intros ?.
    apply lock_singleton in H.
    2: apply SRPC_lock_set_uniq; eauto using gen_net_SRPC.
    2: apply SRPC_lock_set_neq_nil; eauto using gen_net_SRPC.
    unfold lock_set in *.
    unfold gen_net in *.
    rewrite NetMod.init_get in *.
    blast_cases.
    kill H.
  Qed.

  Lemma gen_lock_set_worker : forall conf name other,
      ~ lock (gen_net conf) (Worker name) other.

  Proof.
    intros.
    intros ?.
    apply lock_singleton in H.
    2: apply SRPC_lock_set_uniq; eauto using gen_net_SRPC.
    2: apply SRPC_lock_set_neq_nil; eauto using gen_net_SRPC.
    unfold lock_set in *.
    unfold gen_net in *.
    rewrite NetMod.init_get in *.
    blast_cases.
    kill H.
    assert (SRPC Free (gen_server &init0 handle_call0)) by eauto using SRPC_gen_server.
    apply lock_SRPC_Lock in H1.
    - attac.
      bs (Lock c other = Free).
    - eexists; eauto.
  Qed.

  Lemma gen_net_client_finger : forall conf name i,
      pq_client  (Initiator name (S i)) (NetMod.get (Initiator name i) (gen_net conf)).

  Proof.
    intros.
    unfold gen_net.
    rewrite NetMod.init_get.
    blast_cases.
    constructor; auto.
    destruct i.
    - assert (SRPC (Work (Initiator name 1)) (Finger name 0 target0 arg0)) by eauto using SRPC_Init.
      attac.
    - assert (SRPC (Lock (Initiator name (S (S i))) (Initiator name i)) (Finger name (S i) target0 arg0)) by eauto using SRPC_Finger.
      attac.
  Qed.

  Lemma gen_net_client_worker : forall conf name other,
      ~ pq_client other (NetMod.get (Worker name) (gen_net conf)).

  Proof.
    intros.
    intros ?.
    unfold gen_net in *.
    rewrite NetMod.init_get in *.
    kill H; blast_cases; doubt; attac.
    assert (SRPC Free (gen_server init0 handle_call0)) by apply SRPC_gen_server.
    consider (proc_client _ _).
    bs (Busy _ = Free).
  Qed.


  Lemma gen_lock_set_inv : forall conf n0 n1,
      lock (gen_net conf) n0 n1 ->
      exists name i, n0 = Initiator name (S i) /\ n1 = Initiator name i.

  Proof.
    intros.
    destruct n0 as [name0 [|i0] | name0].
    - apply gen_lock_set_init in H; bs.
    - assert (lock (gen_net conf) (Initiator name0 (S i0)) (Initiator name0 i0)) by
        eauto using gen_lock_set_finger.
      assert (n1 = Initiator name0 i0) by (eapply SRPC_lock_set_uniq; eauto using gen_net_SRPC).
      attac.
    - apply gen_lock_set_worker in H; bs.
  Qed.


  Lemma gen_net_client_inv : forall conf n0 n1,
      pq_client n0 (NetMod.get n1 (gen_net conf)) ->
      exists name i, n0 = Initiator name (S i) /\ n1 = Initiator name i.

  Proof.
    intros.
    unfold gen_net in *.
    rewrite NetMod.init_get in *.
    kill H; blast_cases; doubt; attac.
    - destruct n.
      + assert (SRPC (Work (Initiator s 1)) (Finger s 0 target0 arg0)) by eauto using SRPC_Init.
        kill H0.
        assert (Busy x = Work (Initiator s 1)) by attac.
        attac.
      + assert (SRPC (Lock (Initiator s (S (S n))) (Initiator s n)) (Finger s (S n) target0 arg0)) by eauto using SRPC_Finger.
        kill H0.
        eassert (Busy x = Lock _ (Initiator s _)) by attac.
        attac.
    - assert (SRPC Free (gen_server init0 handle_call0)) by eauto using SRPC_gen_server.
      kill H0.
      bs (Busy x = Free).
  Qed.


  Lemma make_well_formed : forall conf, (well_formed (gen_net conf)).

  Proof.
    intros.
    constructor.
    - apply gen_net_service_wf.
    - intros n0 n1 **.
      apply (gen_lock_set_inv conf n0 n1) in H.
      attac.
      apply gen_net_client_finger.
    - intros n0 n1 **.
      apply (gen_net_client_inv conf n0 n1) in H.
      attac.
      apply gen_lock_set_finger.
  Qed.


  Definition make_mon_state n : MState :=
    match n with
    | Worker name => {| self := n
                    ;  lock := None
                    ;  lock_id := 0
                    ;  wait := []
                    ;  alarm := false
                    |}
    | Initiator name 0 => {| self := n
                         ;  lock := None
                         ;  lock_id := 0
                         ;  wait := [Initiator name 1]
                         ;  alarm := false
                         |}
    | Initiator name (S i) => {| self := n
                             ;  lock := Some (Initiator name i)
                             ;  lock_id := 0
                             ;  wait := [Initiator name (S (S i))]
                             ;  alarm := false
                             |}
    end.


  Definition make_instr : instr :=
    instr_ (fun n => _mon_assg [] MQ_Clear_nil (MRecv (make_mon_state n))).

  Definition gen_mnet (conf : NetConf) := make_instr (gen_net conf).


  Lemma gen_net_dep : forall conf name i0 i1,
      lt i1 i0 ->
      dep_on (gen_net conf) (Initiator name i0) (Initiator name i1).

  Proof.
    induction i0; intros.
    1: attac.

    kill H.
    - constructor.
      eapply gen_lock_set_finger.
    - econstructor 2.
      eapply gen_lock_set_finger.
      eapply IHi0.
      kill H0; attac.
  Qed.

  Lemma gen_net_dep_inv : forall conf n0 n1,
      dep_on (gen_net conf) n0 n1 ->
      exists name i0 i1, n0 = Initiator name i0 /\ n1 = Initiator name i1 /\ lt i1 i0.

  Proof.
    intros.
    apply dep_lock_chain in H as [L [H ?]].
    generalize dependent n0.
    induction L; intros; kill H.
    - apply gen_lock_set_inv in H1.
      attac.
      exists name, (S i), i.
      attac.
    - hsimpl in *.
      specialize (IHL ltac:(auto) a ltac:(auto)).
      apply gen_lock_set_inv in H1.
      attac.
      exists name0, (S i0), i1.
      attac.
  Qed.


  Lemma gen_mnet_KIC : forall conf, (KIC (gen_mnet conf)).
    intros.
    constructor; intros; ltac1:(autounfold with LTS_get in * ).
    1: unfold gen_mnet; rewrite net_deinstr_instr; eauto using make_well_formed.

    1: destruct (NetMod.get n (gen_mnet conf)) eqn:?.
    2: destruct (NetMod.get n0 (gen_mnet conf)) eqn:?.
    3: destruct (NetMod.get n0 (gen_mnet conf)) eqn:?.
    4: destruct (NetMod.get n0 (gen_mnet conf)) eqn:?.

    1: unfold gen_mnet, make_instr, apply_instr, serv_instr, gen_net in *; try (rewrite NetMod.init_get in * ); simpl in *.
    - hsimpl in *.
      unfold make_mon_state.
      blast_cases; compat_hsimpl in *; attac.
    - unfold gen_mnet in *.
      rewrite net_deinstr_instr in *.
      apply gen_lock_set_inv in H.
      attac.
      unfold gen_net, make_instr, apply_instr, serv_instr in *.
      attac.
    - unfold gen_mnet in *.
      rewrite net_deinstr_instr in *.
      apply gen_lock_set_inv in H.
      attac.
      unfold gen_net, make_instr, apply_instr, serv_instr in *.
      attac.
      destruct i; attac.
    - unfold gen_mnet in *.
      rewrite net_deinstr_instr in *.
      apply gen_net_dep_inv in H.
      attac.
  Qed.


  Lemma gen_mnet_KIS : forall conf, (KIS (gen_mnet conf)).
    intros.
    constructor; intros; ltac1:(autounfold with LTS_get in * ).
    1: unfold gen_mnet; rewrite net_deinstr_instr; eauto using make_well_formed.

    - destruct (NetMod.get n0 (gen_mnet conf)) eqn:?.
      unfold gen_mnet, make_instr, apply_instr, serv_instr, gen_net, make_mon_state in *; try (rewrite NetMod.init_get in * ); simpl in *.
      blast_cases; attac.
      blast_cases; attac.
    - left.
      unfold gen_mnet in *.
      rewrite net_deinstr_instr.
      unfold gen_mnet, make_instr, apply_instr, serv_instr, gen_net, make_mon_state in *; try (rewrite NetMod.init_get in * ); simpl in *.

      blast_cases; attac.
      blast_cases; attac.
      apply gen_lock_set_finger.
    -  unfold gen_mnet in *.
       rewrite net_deinstr_instr.
       unfold make_instr, apply_instr, serv_instr, gen_net, make_mon_state in * |-; try (rewrite NetMod.init_get in * ); simpl in *.

       blast_cases; attac.
       blast_cases; attac.
       apply gen_lock_set_finger.
       apply gen_lock_set_finger.
    - unfold gen_mnet in *.
      rewrite net_deinstr_instr.
      unfold make_instr, apply_instr, serv_instr, gen_net, make_mon_state in * |-; try (rewrite NetMod.init_get in * ); simpl in *.

      blast_cases; attac.
    - unfold gen_mnet, make_instr, apply_instr, serv_instr, gen_net, make_mon_state in *; try (rewrite NetMod.init_get in * ); simpl in *.
      blast_cases; attac.
    - unfold gen_mnet, make_instr, apply_instr, serv_instr, gen_net, make_mon_state in *; try (rewrite NetMod.init_get in * ); simpl in *.

      blast_cases.
      rewrite NetMod.get_map in *.
      rewrite NetMod.init_get in *.
      destruct p.
      simpl in *.
      bs.
    - unfold gen_mnet in *.
      rewrite net_deinstr_instr.
      unfold make_instr, apply_instr, serv_instr, gen_net, make_mon_state in * |-; try (rewrite NetMod.init_get in * ); simpl in *.
      blast_cases.
      rewrite NetMod.get_map in *.
      rewrite NetMod.init_get in *.
      bs.
    - unfold gen_mnet in *.
      rewrite net_deinstr_instr.
      unfold make_instr, apply_instr, serv_instr, gen_net, make_mon_state in * |-; try (rewrite NetMod.init_get in * ); simpl in *.
      blast_cases.
      rewrite NetMod.get_map in *.
      rewrite NetMod.init_get in *.
      bs.
    - unfold gen_mnet in *.
      rewrite net_deinstr_instr.
      unfold make_instr, apply_instr, serv_instr, gen_net, make_mon_state in * |-; try (rewrite NetMod.init_get in * ); simpl in *.
      blast_cases.
      rewrite NetMod.get_map in *.
      rewrite NetMod.init_get in *.
      blast_cases; attac.
  Qed.


  Notation "'let?' x := service '!' arg 'in' cont" :=
    (h_call service arg (fun x => cont))
      ( x pattern,
        at level 61,
        right associativity,
        service at next level,
        arg at next level
      ).

  Notation reply := h_reply.

  Section Example.
    Axiom valnat : (Net.Channel.Val = nat).
    Definition valnat_trans (v : Net.Channel.Val) : nat. rewrite valnat in v. apply v. Defined.
    Definition natval_trans (n : nat) : Net.Channel.Val. rewrite <- valnat in n. exact n. Defined.
    Hint Rewrite valnat : LTS LTS_concl.
    Coercion natval_trans : nat >-> Net.Channel.Val.
    Lemma veq : forall x, valnat_trans (natval_trans x) = x. intros. unfold valnat_trans, natval_trans.
                                                        rewrite valnat. auto.
    Qed.
    Hint Rewrite veq using assumption : LTS LTS_concl.

    Definition echo := {| state_t := unit; init := tt; handle_call from msg st := reply msg st |}.

    Definition service (target : string) :=
      {| state_t := _;
        init := tt;
        handle_call (_from : option string) (msg : Val) st :=
          match valnat_trans msg with
          | 0 => reply msg st
          | S msg' =>
              let? x := target ! msg' in
              reply x st
          end
      |}.


    Definition example_net : PNet :=
      gen_net
        {| services name :=
            match name with
            | "C" => service "B" | "D" => service "A"
            | "A" => service "C" | "B" => service "D"
            | _ => echo
            end;
          inits name :=
            match name with
            | "iA" => iconf "A" 2 | "iB" => iconf "B" 2
            | _ => iconf "" 0
            end
        |}.


  Lemma can_deadlock : exists path N, (example_net =[path]=> N) /\ DeadSet ["A"; "B"; "C"; "D"]%list N.
  Proof.
    eexists ?[path], ?[N].

    eassert (example_net =[?path]=> ?N).
    {
      (* Session 0 *)
      eapply path_seq1 with (act := NTau (Initiator "iA" 0) Tau).
      {
        unfold example_net, gen_net, call, recvr, recvq.
        repeat econstructor.
        rewrite NetMod.init_get.
        eattac.
      }

      eapply path_seq1 with (act := NComm (Initiator "iA" 0) (Worker "A") Q _).
      {
        unfold example_net, gen_net, call, recvr, recvq.
        eapply NComm_neq; eattac.
        - repeat econstructor.
          compat_hsimpl in *.
          eattac.
        - repeat econstructor.
          compat_hsimpl in *.
          rewrite NetMod.init_get.
          eattac.
      }

      eapply path_seq1 with (act := NTau (Worker "A") Tau).
      {
        unfold example_net, gen_net, call, recvr, recvq.
        rewrite (unfold_Proc (gen_server _ _)).
        simpl.
        repeat econstructor.
        compat_hsimpl.
        eattac.
      }

      eapply path_seq1 with (act := NTau (Worker "A") Tau).
      {
        unfold example_net, gen_net, call, recvr, recvq.
        rewrite (unfold_Proc (run_gen_server _)); simpl.
        repeat econstructor.
        compat_hsimpl.
        eattac.
      }

      eapply path_seq1 with (act := NComm (Worker "A") (Worker "C") Q _).
      {
        unfold example_net, gen_net, call, recvr, recvq.
        eapply NComm_neq; eattac.
        - repeat econstructor.
          compat_hsimpl in *.
          eattac.
        - repeat econstructor.
          compat_hsimpl in *.
          rewrite NetMod.init_get.
          eattac.
      }

      (* Session 1 *)
      eapply path_seq1 with (act := NTau (Initiator "iB" 0) Tau).
      {
        unfold example_net, gen_net, call, recvr, recvq.
        repeat econstructor.
        compat_hsimpl.
        rewrite NetMod.init_get.
        eattac.
      }

      eapply path_seq1 with (act := NComm (Initiator "iB" 0) (Worker "B") Q _).
      {
        unfold example_net, gen_net, call, recvr, recvq.
        eapply NComm_neq; eattac.
        - repeat econstructor.
          compat_hsimpl in *.
          eattac.
        - repeat econstructor.
          compat_hsimpl in *.
          rewrite NetMod.init_get.
          eattac.
      }

      eapply path_seq1 with (act := NTau (Worker "B") Tau).
      {
        unfold example_net, gen_net, call, recvr, recvq.
        rewrite (unfold_Proc (gen_server _ _)).
        simpl.
        repeat econstructor.
        compat_hsimpl.
        eattac.
      }

      eapply path_seq1 with (act := NTau (Worker "B") Tau).
      {
        unfold example_net, gen_net, call, recvr, recvq.
        rewrite (unfold_Proc (run_gen_server _)); simpl.
        repeat econstructor.
        compat_hsimpl.
        eattac.
      }

      eapply path_seq1 with (act := NComm (Worker "B") (Worker "D") Q _).
      {
        unfold example_net, gen_net, call, recvr, recvq.
        eapply NComm_neq; eattac.
        - repeat econstructor.
          compat_hsimpl in *.
          eattac.
        - repeat econstructor.
          compat_hsimpl in *.
          rewrite NetMod.init_get.
          eattac.
      }

      (* Cross *)
      eapply path_seq1 with (act := NTau (Worker "D") Tau).
      {
        unfold example_net, gen_net, call, recvr, recvq.
        rewrite (unfold_Proc (gen_server _ _)).
        simpl.
        repeat econstructor.
        compat_hsimpl.
        eattac.
      }

      eapply path_seq1 with (act := NTau (Worker "D") Tau).
      {
        unfold example_net, gen_net, call, recvr, recvq.
        rewrite (unfold_Proc (run_gen_server _)); simpl.
        repeat econstructor.
        compat_hsimpl.
        eattac.
      }

      eapply path_seq1 with (act := NComm (Worker "D") (Worker "A") Q _).
      {
        unfold example_net, gen_net, call, recvr, recvq.
        eapply NComm_neq; eattac.
        - repeat econstructor.
          compat_hsimpl in *.
          eattac.
        - repeat econstructor.
          compat_hsimpl in *.
          repeat econstructor.
      }

      eapply path_seq1 with (act := NTau (Worker "C") Tau).
      {
        unfold example_net, gen_net, call, recvr, recvq.
        rewrite (unfold_Proc (gen_server _ _)).
        simpl.
        repeat econstructor.
        compat_hsimpl.
        eattac.
      }

      eapply path_seq1 with (act := NTau (Worker "C") Tau).
      {
        unfold example_net, gen_net, call, recvr, recvq.
        rewrite (unfold_Proc (run_gen_server _)); simpl.
        repeat econstructor.
        compat_hsimpl.
        eattac.
      }

      eapply path_seq1 with (act := NComm (Worker "C") (Worker "B") Q _).
      {
        unfold example_net, gen_net, call, recvr, recvq.
        eapply NComm_neq; eattac.
        - repeat econstructor.
          compat_hsimpl in *.
          eattac.
        - repeat econstructor.
          compat_hsimpl in *.
          repeat econstructor.
      }

      eapply STnil.
    }

    match! goal with [_ : _ =[_]=> ?n |- _] => remember $n as N end.

    assert (forall n, Decisive_q (NetMod.get n N)).
    {
      enough (forall n, AnySRPC (serv_p (NetMod.get n N))) by (unfold Decisive_q; eauto using SRPC_Decisive).
      enough (forall n, AnySRPC_serv (NetMod.get n N)) by (intros;
                                                    destruct `(AnySRPC_serv (NetMod.get n N)) as [srpc ?]; exists srpc;
                                                    destruct (NetMod.get n N);
                                                    eauto).
      enough (SRPC_net N) by eauto.
      enough (SRPC_net example_net) by eauto with LTS.
      clear.
      eauto using gen_net_SRPC.
    }

    split; eauto.
    constructor. 1: { clear; attac. }
    intros.
    unfold lock_set.
    compat_hsimpl.
    specialize (H0 n).
    clear H.
    repeat (destruct `(_ \/ _)).
    - exists [Worker "C"].
      subst.
      compat_hsimpl in *.
      split; attac.
      blast_cases. 2: bs.
      apply NAME.eqb_eq in Heqb.
      auto.
    - exists [Worker "D"].
      subst.
      compat_hsimpl in *.
      split; attac.
      blast_cases. 2: bs.
      apply NAME.eqb_eq in Heqb.
      auto.
    - exists [Worker "B"].
      subst.
      compat_hsimpl in *.
      split; attac.
      blast_cases. 2: bs.
      apply NAME.eqb_eq in Heqb.
      auto.
    - exists [Worker "A"].
      subst.
      compat_hsimpl in *.
      split; attac.
      blast_cases. 2: bs.
      apply NAME.eqb_eq in Heqb.
      auto.
    - bs.
  Qed.
  End Example.
End Thomas.
