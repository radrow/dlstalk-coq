(* -*- company-coq-local-symbols: (("pi" . ?π)); -*- *)
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
Require Import DlStalk.ModelData.
Require Import DlStalk.Que.
Require Import DlStalk.Model.
Require Import DlStalk.Network.
Require Import DlStalk.Locks.
Require Import DlStalk.NetLocks.
Require Import DlStalk.SRPC.
Require Import DlStalk.SRPCNet.
Require Import DlStalk.Transp.

Require Import Lia.

From Coq Require Import Program.Equality.
From Coq Require Import Structures.Equalities.

From Coq Require Import Bool.
From Coq Require Import Nat.
From Coq Require Import Structures.OrderedTypeEx.
Require Import OrderedType.

Import ListNotations.
Import BoolNotations.

Record MProbe' {n : Set} : Set := {init : n; index : nat}.

Record MState' {n : Set} : Set :=
  { self : n
  ; lock_id : nat
  ; lock : option n
  ; wait : list n
  ; alarm : bool
  }.


Module Type DETECT_CONF.
  Include SRPC_NET_CONF.
  Include MON_CONF with Definition Msg := @MProbe' NAME.t'
            with Definition MState := @MState' NAME.t'.
End DETECT_CONF.

Module Type MH(Import Conf : DETECT_CONF)(Import Params : MON_PARAMS(Conf)) <: MON_HANDLE(Conf)(Params).
  #[local] Notation Name := NAME.t'.
  Open Scope nat_scope.

  Definition initial (self : Name) : MState :=
    {|self := self
    ; lock := None
    ; lock_id := 0
    ; wait := []
    ; alarm := false
    |}.

  Definition MSend_all (ns : list Name) t v (P : Params.MProc) :=
    List.fold_right (fun n P' => MSend (n, t) v P') P ns.

  Definition mon_handle (ev : Event) (mstate : MState) : MProc :=
          match ev, mstate with
      (* Back probe *)
      | EvRecv (from, R) probe, {|lock := Some l|} =>
          if NAME.eqb from l
          then
            if NAME.eqb (init probe) (self mstate)
            then
              if (lock_id mstate =? index probe)%nat
              then
                (* ALARM *)
                MRecv {|self := self mstate
                      ; lock_id := lock_id mstate
                      ; lock := lock mstate
                      ; wait := wait mstate
                      ; alarm := true
                      |}
              else
                MRecv mstate
            else
              (* Propagate *)
              MSend_all (wait mstate) R probe (MRecv mstate)
          else (MRecv mstate)

      (* Send query *)
      | TrSend (to, Q) _, _ =>
          MRecv {|self := self mstate
                ; lock_id := S (lock_id mstate)
                ; lock := Some to
                ; wait := wait mstate
                ; alarm := alarm mstate
                |}

      (* Send reply *)
      | TrSend (to, R) _, _ =>
          MRecv {|self := self mstate
                ; lock_id := lock_id mstate
                ; lock := lock mstate
                ; wait := List.remove NAME.eq_dec to (wait mstate)
                ; alarm := alarm mstate
                |}

      (* Receive query while locked *)
      | TrRecv (from, Q) _, {|lock := Some l|} =>
          MSend (from, R) {|init:=self mstate; index:=lock_id mstate|}
            (MRecv {|self := self mstate
                   ; lock_id := lock_id mstate
                   ; lock := lock mstate
                   ; wait := from :: wait mstate
                   ; alarm := alarm mstate
                   |})

      (* Receive query while not locked *)
      | TrRecv (from, Q) _, {|lock := None|} =>
          MRecv {|self := self mstate
                ; lock_id := lock_id mstate
                ; lock := lock mstate
                ; wait := from :: wait mstate
                ; alarm := alarm mstate
                |}

      (* Receive reply *)
      | TrRecv (from, R) _, {|lock := Some l|} =>
          if NAME.eqb from l
          then
            MRecv {|self := self mstate
                  ; lock_id := lock_id mstate
                  ; lock := None (* Release lock *)
                  ; wait := wait mstate
                  ; alarm := alarm mstate
                  |}
          else
            MRecv mstate

      (* Ignore anything else *)
      | _, _ => MRecv mstate
      end.

End MH.

Module Mh(Conf : DETECT_CONF)(Params : MON_PARAMS(Conf))
  := Conf <+ MON_PARAMS <+ MH.

Module Type MON_G(Conf : DETECT_CONF)(Params : MON_PARAMS(Conf)) := Conf <+ Params <+ MON_F.

Module Type MC(Conf : DETECT_CONF).
  Declare Module Proc : PROC(Conf).
  Declare Module P : MON_PARAMS(Conf) with Module Proc := Proc.
  Declare Module Export MMM : MH(Conf)(P).
  Declare Module MyMon : MON_G(Conf)(P) with Module MonHandle := MMM.
End MC.

Module Type DETECT_PARAMS(Conf : DETECT_CONF).
  Declare Module Locks : LOCKS(Conf).
  Declare Module NetLocks : NET_LOCKS(Conf) with Module Locks := Locks.
  Declare Module Mon : MC(Conf) with Module Proc := Locks.Proc.
  Declare Module Export Transp : TRANSP(Conf)
  with Module Mon := Mon.MyMon
  with Module Net := NetLocks.Net.
  Declare Module Export Srpc : SRPC(Conf)
  with Module Locks := Locks.
  Declare Module Export SrpcNet : SRPC_NET(Conf)
  with Module Srpc := Srpc
  with Module NetLocks := NetLocks.
End DETECT_PARAMS.


Module Type COMPL_F(Import Conf : DETECT_CONF)(Import Params : DETECT_PARAMS(Conf)).
  Definition MSend_all : (list Name) -> Tag -> Msg -> MProc -> MProc.
    assert (mon_handle = mon_handle) by auto.
    unfold mon_handle in H at 1.
    match! goal with [h : context [?f (wait _) R _ _] |- _] => apply $f end.
  Defined.

  Lemma next_state_Send_all M w t p :
    next_state (MSend_all w t p M) = next_state M.
  Proof. induction w; attac. Qed.

  #[export] Hint Rewrite -> @next_state_Send_all using spank : LTS LTS_concl.

  Include NetLocks.LOCKS_UNIQ.
  Import SrpcDefs.
  Import Srpc.

  Notation MProbe := (@MProbe' Name).

  Notation "'' MN" := (net_deinstr MN) (at level 1).

  Notation NoRecvQ_MQ := (Forall (fun e => match e with TrRecv (_, Q) _ => False | _ => True end)).
  Notation NoRecvR_MQ := (Forall (fun e => match e with TrRecv (_, R) _ => False | _ => True end)).

  Lemma Clear_NoRecvQ_MQ : forall MQ, MQ_Clear MQ -> NoRecvQ_MQ MQ.
  Proof. induction MQ; attac. Qed.
  Lemma Clear_NoRecvR_MQ : forall MQ, MQ_Clear MQ -> NoRecvR_MQ MQ.
  Proof. induction MQ; attac. Qed.

  #[export] Hint Immediate Clear_NoRecvQ_MQ Clear_NoRecvR_MQ : LTS.

  Definition NoRecvQ_from n MQ := forall v, ~ List.In (TrRecv (n, Q) v) MQ.

  Lemma NoRecvQ_MQ_from [MQ] v : NoRecvQ_MQ MQ -> NoRecvQ_from v MQ.
  Proof. unfold NoRecvQ_from in *. intros. intros ?. induction MQ; kill H0; attac. Qed.


  Definition NoRecvR_from n MQ := forall v, ~ List.In (TrRecv (n, R) v) MQ.

  Lemma NoRecvR_MQ_from [MQ] v : NoRecvR_MQ MQ -> NoRecvR_from v MQ.
  Proof. unfold NoRecvR_from in *. intros. intros ?. induction MQ; kill H0; attac. Qed.

  #[export] Hint Resolve NoRecvQ_MQ_from NoRecvR_MQ_from : LTS.


  Lemma pq_TrRecvQ_pop [MQ0 M0 S0 MQ1 M1 S1 a n] :
    (mserv MQ0 M0 S0 =(a)=> mserv MQ1 M1 S1) ->
    ~ NoRecvQ_from n MQ0 ->
    NoRecvQ_from n MQ1 ->
    exists v, a = MActP (Recv (n, Q) v).

  Proof.
    unfold NoRecvQ_from.
    intros.
    kill H; eattac.
    - exfalso.
      apply H0.
      intros ? ?.
      specialize (H1 v0).
      bs.
    - exfalso.
      apply H0.
      intros ? ?.
      specialize (H1 v0).
      bs.
    - destruct n0.
      destruct t.
      + exists v.
        enough (n = n0) by attac.
        smash_eq n n0.
        bs.
      + bs.
    - exfalso.
      apply H0.
      intros ? ?.
      specialize (H1 v0).
      bs.
  Qed.

  Ltac2 Notation iattac := repeat (first [split | intros ?]); attac.
  Ltac2 Notation ieattac := repeat (first [split | intros ?]); eattac.

  Lemma NoRecvQ_from_dec n0 MQ0 :
    NoRecvQ_from n0 MQ0 \/ ~ NoRecvQ_from n0 MQ0.

  Proof.
    unfold NoRecvQ_from.
    induction MQ0; attac.
    destruct IHMQ0.
    - destruct a.
      + left; attac.
      + destruct n.
        smash_eq n0 n; destruct t; attac.
        right. iattac.
        specialize (H0 v).
        attac.
      + left; attac.
    - right.
      intros ?.
      apply H.
      attac.
      specialize (H0 v).
      attac.
  Qed.


  Lemma NoRecvR_from_dec n0 MQ0 :
    NoRecvR_from n0 MQ0 \/ ~ NoRecvR_from n0 MQ0.

  Proof.
    unfold NoRecvR_from.
    induction MQ0; attac.
    destruct IHMQ0.
    - destruct a.
      + left; attac.
      + destruct n.
        smash_eq n0 n; destruct t; attac.
        right. iattac.
        specialize (H0 v).
        attac.
      + left; attac.
    - right.
      intros ?.
      apply H.
      attac.
      specialize (H0 v).
      attac.
  Qed.


  Lemma NoRecvQ_dec MQ :
    NoRecvQ_MQ MQ \/ ~ NoRecvQ_MQ MQ.

  Proof.
    induction MQ; attac.
    destruct IHMQ.
    - destruct a.
      + left; attac.
      + destruct n, t; eattac.
      + left; attac.
    - right.
      intros ?; attac.
  Qed.


  Lemma NoRecvR_dec MQ :
    NoRecvR_MQ MQ \/ ~ NoRecvR_MQ MQ.

  Proof.
    induction MQ; attac.
    destruct IHMQ.
    - destruct a.
      + left; attac.
      + destruct n, t; eattac.
      + left; attac.
    - right.
      intros ?; attac.
  Qed.


  Lemma NoSends_dec MQ :
    NoSends_MQ MQ \/ ~ NoSends_MQ MQ.

  Proof.
    induction MQ; attac.
    destruct IHMQ.
    - destruct a.
      + right; intros ?; attac.
      + left; attac.
      + left; attac.
    - right.
      intros ?; attac.
  Qed.

  #[export] Hint Unfold NetGet : LTS_get.

  Lemma flushed_in_NoRecvQ_MQ : forall MN n, flushed_in n MN -> NoRecvQ_MQ (mserv_i (MN n)).
  Proof. unfold flushed_in, NetGet. intros. destruct (NetMod.get n MN); attac. Qed.
  Lemma flushed_in_NoRecvR_MQ : forall MN n, flushed_in n MN -> NoRecvR_MQ (mserv_i (MN n)).
  Proof. unfold flushed_in, NetGet. intros. destruct (NetMod.get n MN); attac. Qed.

  #[export] Hint Immediate flushed_in_NoRecvQ_MQ flushed_in_NoRecvR_MQ : LTS.

  Lemma flushed_NoRecvQ_from [MN n] v : flushed_in n MN -> NoRecvQ_MQ (mserv_i (MN n)) -> NoRecvQ_from v (mserv_i (MN n)).
  Proof.
    unfold NoRecvQ_from in *. intros. intros ?.
    ltac1:(autounfold with LTS_get in * ). destruct (NetMod.get n MN).
    induction mserv_i0; kill H0; attac.
  Qed.

  #[export] Hint Resolve flushed_NoRecvQ_from : LTS.


  Lemma net_vis_TrRecvQ_pop [MN0 MN1 a n m n'] :
    (MN0 ~(n' @ a)~> MN1) ->
    ~ NoRecvQ_from n (mserv_i (MN0 m)) ->
    NoRecvQ_from n (mserv_i (MN1 m)) ->
    exists v, a = MActP (Recv (n, Q) v) /\ n' = m.

  Proof.
    intros.
    smash_eq m n'.
    - ltac1:(autounfold with LTS_get in * ). hsimpl in *. hsimpl in *.
      destruct (NetMod.get m MN0).
      destruct S.
      assert (exists v, a = MActP (Recv (n, Q) v)) by eauto using pq_TrRecvQ_pop.
      hsimpl in *.
      exists v; auto.
    - ltac1:(autounfold with LTS_get in * ).
      assert (NetMod.get m MN1 = NetMod.get m MN0) by eauto using NV_stay, eq_sym with LTS.
      rewrite `(NetMod.get m MN1 = _) in *.
      bs.
  Qed.


  Lemma net_TrRecvQ_pop (MN0 MN1 : MNet) a n m :
    (MN0 =(a)=> MN1) ->
    ~ NoRecvQ_from n (mserv_i (MN0 m)) ->
    NoRecvQ_from n (mserv_i (MN1 m)) ->
    exists v, a = NTau m (MActP (Recv (n, Q) v)).

  Proof.
    intros.
    kill H.
    - consider (exists v, a0 = MActP (Recv (n, Q) v) /\ n0 = m) by (eapply net_vis_TrRecvQ_pop; eauto).
      exists v. auto.
    - assert (NoRecvQ_from n (mserv_i (N0' m)) \/ ~ NoRecvQ_from n (mserv_i (N0' m))) as [|] by eauto using NoRecvQ_from_dec.
      + eapply net_vis_TrRecvQ_pop in H2; eauto.
        hsimpl in *. destruct v; bs.
      + eapply net_vis_TrRecvQ_pop in H3; eauto.
        hsimpl in *. destruct v; bs.
  Qed.


  (** A probe is hot when it has the current index of the initiator *)
  (* add lock requirement? *)
  Definition hot (MN : MNet) p n := init p = n /\ index p = lock_id (MN n).

  Definition hot_of (MN : MNet) n := {|init:=n;index:=lock_id (MN n)|}.

  Fact hot_hot_of MN n : hot MN (hot_of MN n) n.
  Proof. attac. Qed.

  Definition hot_ev (MN : MNet) e n := match e with
                              | EvRecv (_, R) p => hot MN p n
                              | _ => False
                              end.

  Definition hot_ev_of (MN : MNet) (n' n : Name) := EvRecv (n', R) (hot_of MN n).

  Fact hot_hot_ev_of MN n' n : hot_ev MN (hot_ev_of MN n' n) n.
  Proof. attac. Qed.

  (** Monitor is going to send a probe (inevitably) *)
  Inductive sends_probe : NameTag -> MProbe -> MServ -> Prop :=
  | sp_init MQ MQ' c S n n' v p :
    NoRecvR_from n' MQ -> (* We won't unlock *)
    NoSends_MQ MQ -> (* We won't change the lock_id *)
    lock c = Some n' -> (* We are locked *)
    init p = self c -> index p = lock_id c -> (* Our hot probe *)
    sends_probe (n, R)
      p
      (mserv
         (MQ ++ TrRecv (n, Q) v :: MQ') (* There is a query incoming... *)
         (MRecv c) (* We are ready to take it *)
         S
      )

  | sp_prop MQ MQ' c S n n' p :
    NoRecvR_from n' MQ -> (* We won't unlock *)
    NoSends_MQ MQ -> (* We won't change the lock_id *)
    lock c = Some n' -> (* We are locked *)
    init p <> self c -> (* The probe is not ours *)
    List.In n (wait c) \/ (exists v, List.In (TrRecv (n, Q) v) MQ) -> (* The receiver will be in wait *)
    sends_probe (n, R) p (mserv (MQ ++ EvRecv (n', R) p :: MQ') (MRecv c) S)

  | sp_send MQ M S nc p :
    sends_probe nc p (mserv MQ (MSend nc p M) S)

  | sp_late MQ M S nc nc' p p' :
    (nc' <> nc \/ p' <> p) ->
    sends_probe nc p (mserv MQ (M) S) ->
    sends_probe nc p (mserv MQ (MSend nc' p' M) S)
  .

  Hint Constructors sends_probe : LTS.


  (** ** Alarm condition *)
  (** Either there is an alarm, or an alarm is inevitable due to probe and lock alignment *)
  Inductive ac (n : Name) (MN : MNet) : Prop :=
  | ac_alarm :
    alarm (MN n) = true ->
    ac n MN

  | ac_seek [m m'] :
    (n = m \/ trans_lock MN n m) ->
    lock MN m m' ->  (* TODO: try to relate to mon states exlusively *)
    sends_probe (m, R) (hot_of MN n) (NetMod.get m' MN) ->
    ac n MN

  | ac_fin [n'] :
    lock MN n n' ->
    List.In (hot_ev_of MN n' n) (mserv_i (MN n)) ->
    ac n MN
  .


  Hint Constructors ac : LTS.

  Lemma mserv_preserve_self [a MQ0 M0 S0 MQ1 M1 S1] :
    (mserv MQ0 M0 S0 =(a)=> mserv MQ1 M1 S1) ->
    self (next_state M0) = self (next_state M1).

  Proof.
    intros.

    destruct_ma &a; destruct M0, M1; kill H; auto; Control.enter (fun () => consider ((_) =(_)=> _));
      repeat (match! goal with
              | [_ : (match ?x with _ => _ end = _) |- _] => destruct $x
              end); simpl in *; doubt; hsimpl in *; attac.
    all: destruct wait0; compat_hsimpl in *; attac.
  Qed.


  Lemma mserv_preserve_alarm [a MQ0 M0 S0 MQ1 M1 S1] :
    (mserv MQ0 M0 S0 =(a)=> mserv MQ1 M1 S1) ->
    alarm (next_state M0) = true ->
    alarm (next_state M1) = true.

  Proof.
    intros.

    destruct_ma &a; destruct M0, M1; kill H; auto; Control.enter (fun () => consider ((_) =(_)=> _));
      repeat (match! goal with
              | [_ : (match ?x with _ => _ end = _) |- _] => destruct $x
              end); simpl in *; doubt; attac.
    all: destruct wait0; compat_hsimpl in *; attac.
  Qed.


  Inductive KIC (MN : MNet) : Prop :=
  | KIC_
      (* We are well_formed *)
      (H_wf_C : well_formed '' MN)
      (* `self` is correct *)
      (H_self_C : forall n, self (MN n) = n)
      (* Monitor knows about its lock. Note that if there was any R in MQ, it would not be locked. *)
      (H_lock_C : forall n0 n1, lock MN n0 n1 -> lock (MN n0) = Some n1)
      (* Flushed monitor knows about everyone who waits on it *)
      (H_wait_C : forall n0 n1, lock MN n0 n1 -> NoRecvQ_from n0 (mserv_i (MN n1)) -> List.In n0 (wait (MN n1)))
      (* Self-dependency implies alarm condition *)
      (H_alarm_C : forall n0, trans_lock MN n0 n0 -> exists n1, trans_lock MN n0 n1 /\ ac n1 MN)
    : KIC MN.


  Lemma net_vis_preserve_alarm [a] [MN0 MN1 : MNet] [n n'] :
    (MN0 ~(n' @ a)~> MN1) ->
    alarm (MN0 n) = true ->
    alarm (MN1 n) = true.

  Proof.
    intros.

    smash_eq n n'.
    2: ltac1:(autounfold with LTS_get in * );
    replace (NetMod.get n MN0) with (NetMod.get n MN1) by eauto using NV_stay, eq_sym; auto.

    destruct (NetMod.get n MN0) as [MQ0 s0 S0] eqn:?.
    compat_hsimpl in *.
    ltac1:(autounfold with LTS_get in * ).
    rewrite `(NetMod.get n MN0 = _) in *.
    hsimpl in |- *.
    destruct S.
    eauto using mserv_preserve_alarm.
  Qed.


  Lemma net_preserve_alarm na (MN0 MN1 : MNet) n :
    (MN0 =(na)=> MN1) ->
    alarm (MN0 n) = true ->
    alarm (MN1 n) = true.

  Proof.
    intros.
    consider (MN0 =(_)=> _).
    - eauto using net_vis_preserve_alarm.
    - enough (alarm (N0' n) = true);
        eauto using net_vis_preserve_alarm.
  Qed.


  Lemma net_vis_preserve_self a (MN0 MN1 : MNet) n n' :
    (MN0 ~(n' @ a)~> MN1) ->
    self (MN0 n) = self (MN1 n).

  Proof.
    intros.

    smash_eq n n'.
    2: ltac1:(autounfold with LTS_get in * );
    replace (NetMod.get n MN0) with (NetMod.get n MN1) by eauto using NV_stay, eq_sym; auto.

    destruct (NetMod.get n MN0) as [MQ0 s0 S0] eqn:?.
    hsimpl in * |-.
    ltac1:(autounfold with LTS_get in * ).
    rewrite `(NetMod.get n MN0 = _) in *.
    destruct S.
    rewrite NetMod.get_put_eq. simpl.
    eauto using mserv_preserve_self.
  Qed.


  Lemma net_preserve_self na (MN0 MN1 : MNet) n :
    (MN0 =(na)=> MN1) ->
    self (MN0 n) = self (MN1 n).

  Proof.
    intros.
    consider (MN0 =(_)=> _).
    - eauto using net_vis_preserve_self.
    - enough (self (N0' n) = self (MN0 n));
        eauto using net_vis_preserve_self, eq_sym.
      rewrite <- `(self (_ _) = _ ).
      eauto using net_vis_preserve_self, eq_sym.
  Qed.


  Lemma SRPC_no_immediate_relock [n0 n1 P0 P1 a] :
    AnySRPC P0 ->
    (P0 =(a)=> P1) ->
    proc_lock [n0] P0 ->
    ~ proc_lock [n1] P1.

  Proof.
    intros.
    intros ?.
    assert (AnySRPC P1) by attac.
    consider (exists c, SRPC (Locked c n0) P0) by eauto using lock_SRPC_Locked.
    consider (exists c1, SRPC (Locked c1 n1) P1) by eauto using lock_SRPC_Locked.
    destruct SRPC H4 H0.
    assert (SRPC (Working c) P1) by auto.
    absurd (Working c = Locked c1 n1). intros Hx; kill Hx.
    attac.
  Qed.


  Lemma SRPC_pq_no_immediate_relock [n0 n1 S0 S1 a] :
    AnySRPC_serv S0 ->
    (S0 =(a)=> S1) ->
    serv_lock [n0] S0 ->
    serv_lock [n1] S1 ->
    n0 = n1.

  Proof.
    intros.
    specialize (serv_lock_recv `(serv_lock _ S0) `(S0 =(a)=> S1)) as ?.
    destruct a; doubt.
    compat_hsimpl in *.
    consider (serv_lock [n0] _).
    do 2 (consider (serv_lock [n1] _)).
    enough (List.In n0 [n1]) by attac.
    enough (incl [n0] [n1]) by (unfold incl in *; attac).
    eauto using proc_lock_incl.
  Qed.

  Import Srpc.


  Lemma SRPC_M_net_no_immediate_relock [n m0 m1 N0 N1 a] :
    (forall n, AnySRPC_serv (NetMod.get n '' N0)) ->
    (N0 =(a)=> N1) ->
    lock N0 n m0 ->
    lock N1 n m1 ->
    m0 = m1.

  Proof.
    intros.
    destruct (MNAct_to_PNAct a) eqn:?.
    - assert ('' N0 =(p)=> '' N1) by eauto with LTS.
      eauto using SRPC_net_no_relock.
    - replace ('' N1) with ('' N0) in H2 by eauto using eq_sym with LTS.
      eapply SRPC_lock_set_uniq; eauto with LTS.
  Qed.


  Theorem SRPC_M_net_new_lock_query [N0 N1 : MNet] [n0 n1 a] :
    well_formed '' N0 ->
    ~ lock N0 n0 n1 ->
    lock N1 n0 n1 ->
    (N0 =(a)=> N1) ->
    exists v, a = NComm n0 n1 Q (MValP v).
  Proof.
    intros.
    destruct (MNAct_to_PNAct a) eqn:?.
    - assert ('' N0 =(p)=> '' N1) by eauto with LTS.
      consider (exists v, p = NComm n0 n1 Q v) by eauto using well_formed_new_lock_send_Q.
      exists v.
      destruct a; attac; blast_cases; attac.
    - unfold lock in *.
      replace ('' N1) with ('' N0) in H1 by eauto using eq_sym with LTS.
      bs.
  Qed.


  Import SrpcNet. (* TODO why is this needed here?! *)

  Theorem SRPC_M_net_unlock_reply [N0 N1 : MNet] [n0 n1 a] :
    well_formed '' N0 ->
    lock N0 n0 n1 ->
    ~ lock N1 n0 n1 ->
    (N0 =(a)=> N1) ->
    exists v, a = NComm n1 n0 R (MValP v).

  Proof.
    intros.
    destruct (MNAct_to_PNAct a) eqn:?.
    - assert ('' N0 =(p)=> '' N1) by eauto with LTS.
      consider (exists v, p = NComm n1 n0 R v) by (eapply net_unlock_on_reply; eauto with LTS).
      exists v.
      destruct a; attac; blast_cases; attac.
    - unfold lock in *.
      replace ('' N1) with ('' N0) in H1 by eauto using eq_sym with LTS.
      bs.
  Qed.


  Lemma SRPC_M_net_new_lock_uniq [N0 N1 : MNet] [na] [n0 n1 m0 m1] :
    well_formed '' N0 ->
    (N0 =(na)=> N1) ->
    ~ lock N0 n0 n1 ->
    ~ lock N0 m0 m1 ->
    lock N1 n0 n1 ->
    lock N1 m0 m1 ->
    n0 = m0 /\ n1 = m1.

  Proof.
    intros.
    assert (exists v, na = NComm n0 n1 Q (MValP v)) by eauto using SRPC_M_net_new_lock_query.
    assert (exists v, na = NComm m0 m1 Q (MValP v)) by eauto using SRPC_M_net_new_lock_query.
    attac.
  Qed.


  Theorem SRPC_net_query_new_lock [N0 N1 : PNet] [n0 n1 v] :
    well_formed N0 ->
    (N0 =(NComm n0 n1 Q v)=> N1) ->
    (~ lock N0 n0 n1 /\ lock N1 n0 n1).

  Proof.
    split; intros.
    - intros HL.
      unfold lock, lock_set in *.
      hsimpl in *.
      kill H0; compat_hsimpl in *; bs.
    - eauto using well_formed_send_Q_new_lock.
  Qed.


  Theorem SRPC_M_net_query_new_lock [N0 N1 : MNet] [n0 n1 v] :
    well_formed '' N0 ->
    (N0 =(NComm n0 n1 Q (MValP v))=> N1) ->
    (~ lock N0 n0 n1 /\ lock N1 n0 n1).

  Proof.
    intros.
    assert ('' N0 =(@NComm _ gen_Act_PAct n0 n1 Q v)=> '' N1)
      by (eapply net_deinstr_act_do; eauto with LTS; simpl; eauto with LTS).
    eauto using SRPC_net_query_new_lock.
  Qed.


  Theorem SRPC_net_reply_unlock [N0 N1 : PNet] [n0 n1 v] :
    well_formed N0 ->
    (N0 =(NComm n0 n1 R v)=> N1) ->
    (lock N0 n1 n0 /\ ~ lock N1 n1 n0).

  Proof.
    intros.
    split.
    - eauto using well_formed_send_R_lock_l.
    - eauto using well_formed_send_R_receiver_no_lock.
  Qed.


  Theorem SRPC_M_net_reply_unlock [N0 N1 : MNet] [n0 n1 v] :
    well_formed '' N0 ->
    (N0 =(NComm n0 n1 R (MValP v))=> N1) ->
    (lock N0 n1 n0 /\ ~ lock N1 n1 n0).

  Proof.
    intros.
    assert ('' N0 =(@NComm _ gen_Act_PAct n0 n1 R v)=> '' N1)
      by (eapply net_deinstr_act_do; eauto with LTS; simpl; eauto with LTS).
    eauto using SRPC_net_reply_unlock.
  Qed.


  Lemma SRPC_proc_client_dec n P :
    AnySRPC P ->
    proc_client n P \/ ~ proc_client n P.

  Proof.
    intros.
    destruct H as [srpc Hsrpc].
    hsimpl in *.
    destruct srpc.
    - right; intros ?.
      kill H.
      absurd (Busy x = Ready); eauto using SRPC_inv with LTS.
    - smash_eq c n.
      + eauto with LTS.
      + right; intros ?.
        kill H.
        absurd (Busy x = Busy s); eauto using SRPC_inv with LTS.
  Qed.


  Lemma SRPC_pq_client_dec [n S] :
    AnySRPC_serv S ->
    pq_client n S \/ ~ pq_client n S.

  Proof.
    intros.
    destruct S as [I P O].
    destruct (SRPC_proc_client_dec n P);
      destruct (@in_dec_v _ (n, Q) &I);
      destruct (@in_dec_v _ (n, R) &O);
      eattac.

    right; intros ?.
    kill H3; eattac.
  Qed.


  (* TODO extract *)
  Lemma well_formed_lock_dec N n0 n1 :
    well_formed N ->
    lock N n0 n1 \/ ~ lock N n0 n1.

  Proof.
    intros.
    enough (pq_client n0 (NetMod.get n1 N) \/ ~ pq_client n0 (NetMod.get n1 N)) as [|] by eattac.
    eauto using SRPC_pq_client_dec with LTS.
  Qed.

  #[export] Hint Resolve well_formed_lock_dec : LTS.


  Theorem SRPC_net_tau_preserve_lock [N0 N1 : PNet] [n a] :
    well_formed N0 ->
    (N0 =(NTau n a)=> N1) ->
    forall n0 n1, lock N0 n0 n1 <-> lock N1 n0 n1.

  Proof.
    intros.
    split; intros.
    - assert (well_formed N1) by auto with LTS.
      destruct (well_formed_lock_dec N1 n0 n1); eauto.
      absurd (exists v, NTau n a = NComm n1 n0 R v); eauto using net_unlock_on_reply.
      attac.
      eapply net_unlock_on_reply with (N0:=N0)(N1:=N1); eauto with LTS.
    - destruct (well_formed_lock_dec N0 n0 n1); eauto.
      absurd (exists v, NTau n a = NComm n0 n1 Q v); eauto using well_formed_new_lock_send_Q.
      intros ?; attac.
  Qed.


  Theorem SRPC_M_net_tau_preserve_lock [N0 N1 : MNet] [n a] :
    well_formed '' N0 ->
    (N0 =(NTau n a)=> N1) ->
    forall n0 n1, lock N0 n0 n1 <-> lock N1 n0 n1.

  Proof.
    intros.
    destruct (MNAct_to_PNAct (NTau n a)) eqn:?.
    - assert ('' N0 =(p)=> '' N1) by eauto with LTS.
      destruct a; doubt; destruct p0; doubt.
      hsimpl in *; eauto using SRPC_net_tau_preserve_lock.
    - unfold lock in *.
      replace ('' N1) with ('' N0) by eauto using eq_sym with LTS.
      attac.
  Qed.


  Lemma M_vis_preserve_steady_lock [MN0 MN1 : MNet] [a n n' m0 m1] :
    (MN0 ~(n' @ a)~> MN1) ->
    lock (MN0 n) = Some m0 ->
    lock (MN1 n) = Some m1 ->
    (forall v, a <> MActT (Send (m1, Q) v)) ->
    m0 = m1.

  Proof.
    intros.
    destruct (NetMod.get n MN0) as [MQ0 s0 S0] eqn:?.
    destruct (NetMod.get n MN1) as [MQ1 s1 S1] eqn:?.

    smash_eq n n'.
    - ltac1:(autounfold with LTS_get in * ).
      rewrite `(NetMod.get n MN0 = _) in *.
      rewrite `(NetMod.get n MN1 = _) in *.
      compat_hsimpl in *.
      destruct_ma &a; try (destruct t0); doubt; auto; compat_hsimpl in *; auto; try (destruct s); simpl in *; subst;
        repeat (match! goal with
                | [_ : lock (next_state (match ?x with _ => _ end)) = _ |- _] => destruct $x
                end); simpl in *; doubt; compat_hsimpl in *; attac.

    - enough (Some m0 = Some m1) by attac.
      enough (lock (MN0 n) = lock (MN1 n)) by (rewrite `(lock (MN0 n) = _) in *; attac).
      ltac1:(autounfold with LTS_get in * ).
      assert (NetMod.get n MN0 = NetMod.get n MN1) by eauto using NV_stay with LTS.
      attac.
  Qed.


  Lemma M_preserve_steady_lock [MN0 MN1 : MNet] [na n m0 m1] :
    SRPC_net MN0 ->
    (MN0 =(na)=> MN1) ->
    lock (MN0 n) = Some m0 ->
    lock (MN1 n) = Some m1 ->
    (forall v, na <> NComm n m1 Q (MValP v)) ->
    m0 = m1.

  Proof.
    intros.
    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.
    destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.

    consider (MN0 =(_)=> _).
    - eapply M_vis_preserve_steady_lock; eauto with LTS.
      intros ? ?. attac.
    - destruct (lock (N0' n)) as [n1|] eqn:?.
      + transitivity 'n1.
        * smash_eq n0 n.
          -- kill H5.
             clear H5.
             eapply M_vis_preserve_steady_lock; eauto with LTS.
             intros ? ?. hsimpl in *.
             destruct v; doubt.
             hsimpl in *.
             ltac1:(autounfold with LTS_get in * ).
             rewrite `(NetMod.get n0 (NetMod.put _ _ _) = _) in *.
             rewrite `(NetMod.get n0 MN0 = _) in *.
             hsimpl in *. hsimpl in *.
             smash_eq n0 n1; compat_hsimpl in *; compat_hsimpl in *.
             ++ bs (NComm m1 m1 Q # v0  <> NComm m1 m1 Q # v0).
             ++ bs (NComm n0 m1 Q # v0 <> NComm n0 m1 Q # v0).
          -- enough (Some m0 = Some n1) by attac.
             enough (lock (MN0 n) = lock (N0' n))
               by (rewrite `(lock (MN0 n) = _) in *;
                   rewrite `(lock (N0' n) = _) in *;
                   attac
                  ).
             ltac1:(autounfold with LTS_get in * ).
             hsimpl in *. hsimpl in *. hsimpl in |- *.
             auto.

        * eapply M_vis_preserve_steady_lock;
            eauto with LTS.
          intros ? ?. hsimpl in *.
          destruct v; bs.
      + exfalso.
        ltac1:(autounfold with LTS_get in * ).
        destruct (NetMod.get n N0') as [MQ0' M0' S0'] eqn:?.
        smash_eq n n'; compat_hsimpl in *.
        * destruct v; kill H5; attac.
        * blast_cases; attac.
          -- smash_eq n' n0; attac.
             smash_eq n n0; attac.
          -- smash_eq n' n0; attac.
             smash_eq n n0; attac.
             compat_hsimpl in *.
             blast_cases; attac.
  Qed.


  Lemma M_lock_decide [MN0 MN1 : MNet] [na n] :
    SRPC_net MN0 ->
    (MN0 =(na)=> MN1) ->
    (forall n' v, na <> NComm n n' Q (MValP v)) ->
    lock (MN0 n) <> lock (MN1 n) -> (lock (MN0 n) = None \/ lock (MN1 n) = None).

  Proof.
    intros.
    destruct (lock (MN0 n)) as [n0|] eqn:?; auto.
    destruct (lock (MN1 n)) as [n1|] eqn:?; auto.
    assert (forall v, na <> NComm n n1 Q (MValP v)) by auto.
    assert (n0 = n1) by eauto using M_preserve_steady_lock.
    bs.
  Qed.


  Lemma M_vis_set_lock [MN0 MN1 : MNet] [a n n' n''] :
    (MN0 ~(n'' @ a)~> MN1) ->
    lock (MN0 n) = None ->
    lock (MN1 n) = Some n' ->
    exists v, a = send (n', Q) (MValP v).

  Proof.
    intros.
    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.
    destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.

    smash_eq n n''.
    - ltac1:(autounfold with LTS_get in * ).
      rewrite `(NetMod.get n MN0 = _) in *.
      rewrite `(NetMod.get n MN1 = _) in *.
      compat_hsimpl in *.
      destruct_ma &a; try (destruct t0); doubt; auto; compat_hsimpl in *; auto;
        try (destruct s); simpl in *; subst;
        repeat (match! goal with
                | [_ : lock (next_state (match ?x with _ => _ end)) = _ |- _] => destruct $x
                end); simpl in *; doubt; compat_hsimpl in *; attac.

    - ltac1:(autounfold with LTS_get in * ).
      assert (NetMod.get n MN0 = NetMod.get n MN1) by eauto using NV_stay with LTS.
      rewrite `(NetMod.get n MN1 = _) in *.
      compat_hsimpl in *. compat_hsimpl in *.
      attac.
  Qed.


  Lemma M_set_lock [MN0 MN1 : MNet] [na n n'] :
    (MN0 =(na)=> MN1) ->
    lock (MN0 n) = None ->
    lock (MN1 n) = Some n' ->
    exists v, na = NComm n n' Q (MValP v).

  Proof.
    intros.
    consider (MN0 =(_)=> MN1).
    - consider (exists v, a = send (n', Q) (MValP v)) by eauto using M_vis_set_lock.
      bs.
    - enough (exists v', n0 = n /\ n'0 = n' /\ &t = Q /\ v = MValP v') by (hsimpl in *; exists v'; f_equal; eattac).
      assert (lock (N0' n) = lock (MN1 n)).
      {
        hsimpl in *.
        ltac1:(autounfold with LTS_get in * ).
        smash_eq n n'0; hsimpl in *.
        * destruct v; compat_hsimpl in *; attac.
        * attac.
      }
      rewrite <- `(lock (N0' n) = _) in *.

      destruct (lock (N0' n)) as [n1|] eqn:?; doubt.

      consider (exists v', send (n'0, &t) v = send (n1, Q) (MValP v')) by eauto using M_vis_set_lock.
      destruct v; doubt; compat_hsimpl in *.
      unfold NetGet in *.
      smash_eq n' n0 n; attac.
  Qed.


  Lemma M_vis_unlock [MN0 MN1 : MNet] [a n n' n''] :
    (MN0 ~(n'' @ a)~> MN1) ->
    lock (MN0 n) = Some n' ->
    lock (MN1 n) = None ->
    exists v, a = MActP (Recv (n', R) v) /\ n'' = n.

  Proof.
    intros.
    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.
    destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.

    smash_eq n n''.
    - ltac1:(autounfold with LTS_get in * ).
      rewrite `(NetMod.get n MN0 = _) in *.
      rewrite `(NetMod.get n MN1 = _) in *.
      hsimpl in *.
      destruct_ma &a; try (destruct t0); doubt; auto; hsimpl in *; auto;
        try (destruct s); simpl in *; subst;
        repeat (match! goal with
                | [_ : lock (next_state (match ?x with _ => _ end)) = _ |- _] => destruct $x eqn:?
                end); simpl in *; doubt; hsimpl in *; attac.
      all: compat_hsimpl in *; blast_cases; attac.
    - ltac1:(autounfold with LTS_get in * ).
      assert (NetMod.get n MN0 = NetMod.get n MN1) by eauto using NV_stay with LTS.
      rewrite `(NetMod.get n MN1 = _) in *.
      compat_hsimpl in *. compat_hsimpl in *.
      attac.
  Qed.


  Lemma Rad_set_unlock [MN0 MN1 : MNet] [na n n'] :
    (MN0 =(na)=> MN1) ->
    lock (MN0 n) = Some n' ->
    lock (MN1 n) = None ->
    exists v, na = NTau n (MActP (Recv (n', R) v)).

  Proof.
    intros.
    consider (MN0 =(_)=> MN1).
    - consider (exists v, a = MActP (Recv (n', R) v) /\ n0 = n) by eauto using M_vis_unlock.
      exists v; auto.
    - exfalso.
      destruct (lock (N0' n)) as [n1|] eqn:?.
      + consider (exists v', recv (n0, &t) v = MActP (Recv (n1, R) v') /\ n'0 = n) by eauto using M_vis_unlock.
        destruct v; bs.
      + consider (exists v', send (n'0, &t) v = MActP (Recv (n', R) v') /\ n0 = n) by eauto using M_vis_unlock.
        destruct v; bs.
  Qed.


  Lemma MProbe_eq_dec : forall (p0 p1 : MProbe), {p0 = p1}+{p0 <> p1}.

  Proof.
    intros.
    destruct p0, p1.
    smash_eq init0 init1; destruct (PeanoNat.Nat.eq_dec index0 index1); attac.
  Qed.


  Lemma hot_dec MN p n : hot MN p n \/ ~ hot MN p n.
  Proof.
    destruct (MProbe_eq_dec p (hot_of MN n)); subst.
    - auto using hot_hot_of.
    - right.
      intros ?.
      apply `(p <> _).
      consider (hot _ _ _).
      unfold hot_of.
      destruct p.
      auto.
  Qed.


  Lemma wtf [A : Type] (l : list A) (P0 P1 : list A -> Prop) :
    (forall l, P0 l \/ ~ P0 l) ->
    (forall l, P1 l \/ ~ P1 l) ->
    (exists l0 l1, l = l0 ++ l1 /\ P0 l0 /\ P1 l0) \/
      ~ exists l0 l1, l = l0 ++ l1 /\ P0 l0 /\ P1 l0.
    intros.
    ltac1:(rev_induction l).
    - specialize (H []).
      specialize (H0 []).
      destruct H, H0.
      1: left; attac.
      all: right; intros ?; hsimpl in *; destruct l0, l1; bs.
    - intros.
      destruct H1.
      + hsimpl in *.
        rewrite <- app_assoc.
        left. exists l0, (l1 ++ [a]). auto.
      + assert (forall T (l : list T), l = [] \/ exists l' a, l = l' ++ [a]) as snoc_inv.
        {
          clear. induction l; attac. destruct IHl; attac. exists [], a; attac.
        }

        destruct (H (l ++ [a])), (H0 (l ++ [a])).
        * left. exists (l ++ [a]), []. attac.
        * right.
          intros Hx; apply H1; clear H1; hsimpl in *.
          specialize (snoc_inv _ l1) as [|]; hsimpl in *.
          -- bs.
          -- exists l0, l'.
             rewrite app_assoc in Hx.
             apply app_inj_tail in Hx.
             eattac.
        * right.
          intros Hx; apply H1; clear H1; hsimpl in *.
          specialize (snoc_inv _ l1) as [|]; hsimpl in *.
          -- bs.
          -- exists l0, l'.
             rewrite app_assoc in Hx.
             apply app_inj_tail in Hx.
             eattac.
        * right.
          intros Hx; apply H1; clear H1; hsimpl in *.
          specialize (snoc_inv _ l1) as [|]; hsimpl in *.
          -- bs.
          -- exists l0, l'.
             rewrite app_assoc in Hx.
             apply app_inj_tail in Hx.
             eattac.
  Qed.

  Lemma wtf' [A : Type] (l : list A) (P0 : list A -> Prop) :
    (forall l, P0 l \/ ~ P0 l) ->
    (exists l0 l1, l = l0 ++ l1 /\ P0 l0) \/
      ~ exists l0 l1, l = l0 ++ l1 /\ P0 l0.
    intros.
    ltac1:(rev_induction l).
    - specialize (H []).
      destruct H.
      1: left; attac.
      all: right; intros ?; hsimpl in *; destruct l0, l1; bs.
    - intros.
      destruct H0.
      + hsimpl in *.
        rewrite <- app_assoc.
        left. exists l0, (l1 ++ [a]). auto.
      + assert (forall T (l : list T), l = [] \/ exists l' a, l = l' ++ [a]) as snoc_inv.
        {
          clear. induction l; attac. destruct IHl; attac. exists [], a; attac.
        }

        destruct (H (l ++ [a])).
        * left. exists (l ++ [a]), []. attac.
        * right.
          intros Hx; apply H0; clear H0; hsimpl in *.
          specialize (snoc_inv _ l1) as [|]; hsimpl in *.
          -- bs.
          -- exists l0, l'.
             rewrite app_assoc in Hx.
             apply app_inj_tail in Hx.
             eattac.
  Qed.


  Lemma sends_probe_dec n p MS :
    sends_probe n p MS \/ ~ sends_probe n p MS.

  Proof.
    intros.
    destruct MS as [MQ M S].
    induction M.

    (* Rare case where inductive step is simpler than the base! *)
    2: destruct (NameTag_eq_dec n to);
    destruct (MProbe_eq_dec p msg);
    destruct IHM; subst; eattac; right; intros Hx; kill Hx.

    destruct n.
    destruct t.
    1: right; attac.

    pose (init_case :=
            exists (MQ' MQ'' : list Event)
                   (n' : Name) (v : Val),
              NoRecvR_from n' MQ' /\
                NoSends_MQ MQ' /\
                lock state = Some n' /\
                init p = self state /\
                index p = lock_id state /\
                MQ = (MQ' ++ TrRecv (n, Q) v :: MQ'')
         ).

    pose (prop_case :=
            exists (MQ' MQ'' : list Event)
                   (n' : Name),
              NoRecvR_from n' MQ' /\
                NoSends_MQ MQ' /\
                lock state = Some n' /\
                init p <> self state /\
                (List.In n (wait state) \/ (exists v : Val, List.In (TrRecv (n, Q) v) MQ')) /\
                MQ = (MQ' ++ EvRecv (n', R) p :: MQ'')
         ).

    enough ((init_case \/ ~ init_case) /\ (prop_case \/ ~ prop_case)).
    {
      hsimpl in *.
      consider (init_case \/ ~ init_case); hsimpl in *.
      1: subst init_case; hsimpl in *; left; econstructor 1; eauto.
      consider (prop_case \/ ~ prop_case).
      1: subst prop_case; hsimpl in *; left; econstructor 2; eauto.

      right.
      intros Hx.
      kill Hx.
      - apply `(~ init_case); subst init_case; eexists _, _, _; eattac.
      - apply `(~ prop_case); subst init_case; eexists _, _, _; eattac.
    }

    split; subst init_case prop_case; clear.
    - induction MQ.
      1: right; intros Hx; hsimpl in Hx; bs.

      destruct a.
      + right; intros ?; hsimpl in *; destruct MQ'; attac.
      + destruct (lock state) as [n1|] eqn:?.
        2: right; intros Hx; hsimpl in *; bs.
        destruct (NAME.eq_dec (init p) (self state)).
        2: right; intros Hx; hsimpl in *; bs.
        destruct (PeanoNat.Nat.eq_dec (index p) (lock_id state)).
        2: right; intros Hx; hsimpl in *; bs.
        hsimpl in * |-.

        destruct (NameTag_eq_dec n0 (n, Q)); subst.
        * destruct IHMQ.
          -- left.
             hsimpl in * |- .
             exists (TrRecv (n, Q) v :: MQ'), MQ'', n', v0.
             ieattac.
          -- left.
             exists [], MQ, n1, v.
             attac.
        * destruct IHMQ.
          -- hsimpl in * |- .
             destruct (NameTag_eq_dec n0 (n', R)).
             ++ right.
                intros Hx; hsimpl in Hx.
                destruct MQ'0; kill Hx4.
                specialize (Hx v). bs.
             ++ left.
                exists (TrRecv n0 v :: MQ'), MQ'', n', v0.
                ieattac.
          -- hsimpl in * |- .
             right; intros Hx; apply H; clear H; hsimpl in * |-.
             destruct MQ'; kill Hx4.
             exists MQ', MQ'', n', v0.
             hsimpl in * |-.
             repeat split; auto.
             intros ? ?.
             specialize (Hx v1). bs.
      + destruct IHMQ.
        * hsimpl in * |- .
          left.
          exists (EvRecv n0 m :: MQ'), MQ'', n', v. ieattac.
        * right.
          intros Hx; apply H; clear H; hsimpl in * |-.
          destruct MQ'; kill Hx4.
          hsimpl in * |-.
          exists (MQ'), MQ'', n', v.
          ieattac.
          specialize (Hx v0). eapply Hx. eattac.

    - destruct (lock state) as [n0|] eqn:?.
      2: right; intros Hx; hsimpl in *; bs.
      destruct (NAME.eq_dec (init p) (self state)) as [|Heqi].
      1: right; intros Hx; hsimpl in *; bs.

      pose (my_prop :=
              fun MQ => NoRecvR_from n0 MQ
                        /\ NoSends_MQ MQ
                        /\ (List.In n (wait state) \/ (exists v, List.In (TrRecv (n, Q) v) MQ))
                        /\ exists MQ', MQ = MQ' ++ [(EvRecv (n0, R) p)]
           ).

      assert (forall MQ, my_prop MQ \/ ~ my_prop MQ) as my_prop_dec.
      {
        clear.
        subst my_prop.
        intros.
        simpl in *.
        destruct (NoRecvR_from_dec n0 MQ).
        2: right; intros Hx; hsimpl in *; bs.
        destruct (NoSends_dec MQ).
        2: right; intros Hx; hsimpl in *; bs.

        assert (forall T (l : list T), l = [] \/ exists l' a, l = l' ++ [a]) as snoc_inv.
        {
          clear. induction l; attac. destruct IHl; attac. exists [], a; attac.
        }
        specialize (snoc_inv _ MQ) as [|]; hsimpl in *.
        1: right; intros Hx; hsimpl in *; bs.
        destruct a; subst; doubt.
        1: right; intros Hx; hsimpl in *; apply app_inj_tail in Hx3; attac.
        destruct (NameTag_eq_dec n1 (n0, R)); subst.
        2: {right; intros Hx; eapply `(n1 <> (n0, R)); hsimpl in *; apply app_inj_tail in Hx3; attac.
        }
        destruct (MProbe_eq_dec m p); subst.
        2: {right; intros Hx; eapply `(m <> p); hsimpl in *; apply app_inj_tail in Hx3; attac.
        }
        destruct (in_dec NAME.eq_dec n (wait state)).
        1: { left. repeat split; eauto; eattac. }
        assert ((exists v, List.In (TrRecv (n, Q) v) (l' ++ [EvRecv (n0, R) p])) \/ ~ (exists v, List.In (TrRecv (n, Q) v) (l' ++ [EvRecv (n0, R) p]))) as [|].
        {
          clear.
          generalize (l' ++ [EvRecv (n0, R) p]); intros.
          induction l.
          1: right; intros ?; attac.
          destruct IHl; hsimpl in *; eattac.
          destruct a as [[? ?] ?|[? [|]] ?| [? ?] ?].
          all: try (solve [right; attac]).
          smash_eq n n1.
          - left; exists v; attac.
          - right; attac.
        }
        - left; ieattac.
          specialize (H v).
          hsimpl in *. bs.
        - right; ieattac.
      }

      specialize (wtf' MQ my_prop my_prop_dec) as [|].
      + subst my_prop.
        hsimpl in *.
        left.
        exists MQ', l1, n0.
        ieattac.
        specialize (H0 v).
        eapply `(~ _).
        attac.
      + right.
        intros ?; apply H; subst my_prop; hsimpl in *.
        exists (MQ' ++ [EvRecv (n', R) p]), MQ''.
        ieattac.
        destruct `(_ \/ _); eattac.
  Qed.


  Lemma lock_M_no_sends_in [n n'] [MN : MNet] :
    lock MN n n' ->
    no_sends_in n MN.
  Proof.
    intros.
    unfold no_sends_in, NoTrSend, lock, lock_set in *.
    unfold net_deinstr in *.
    ltac1:(autorewrite with LTS in * ).
    hsimpl in *.
    destruct (NetMod.get n MN) as [MQ0 M0 [I0 P0 O0]].
    apply Forall_forall.
    intros.
    destruct x; auto.
    destruct (deinstr (mserv MQ0 M0 (serv I0 P0 O0))) as [I' P' O'] eqn:?.
    absurd (List.In (n0, v) O').
    - intros ?.
      unfold deinstr in *.
      hsimpl in *.
      kill H0.
      assert (MQ_s _ = [] /\ O0 = []) by eauto using app_eq_nil.
      attac.
      (* TODO TO LEMMA *)
      clear - H0 H1.
      induction mserv_i0; attac.
      destruct a; attac.
    - blast_cases; attac.
  Qed.


  Lemma locked_M_no_send [MN0 MN1 : MNet] [n0 n1] [m0 m1 v t] :
    lock MN0 n0 n1 ->
    (MN0 =(NComm m0 m1 t (MValP v))=> MN1) ->
    n0 <> m0.

  Proof.
    intros.
    intros ?; subst.
    assert (no_sends_in m0 MN0) by eauto using lock_M_no_sends_in.
    unfold lock, lock_set, no_sends_in, NoTrSend in *.
    kill H0.
    compat_hsimpl in *.
    bs.
  Qed.


  Lemma dep_self_deadlocked [N n] :
    well_formed N ->
    trans_lock N n n -> deadlocked n N.

  Proof.
    intros.
    eapply dep_self_deadset; eauto with LTS.
  Qed.


  Lemma well_formed_lock_chain_dec (N : PNet) n0 L n1 :
    well_formed N ->
    lock_chain N n0 L n1 \/ ~ lock_chain N n0 L n1.

  Proof.
    intros.
    generalize dependent n0.
    induction L; intros; hsimpl in *.
    1: eauto using well_formed_lock_dec with LTS.

    rename a into n0'.
    assert (lock N n0 n0' \/ ~ lock N n0 n0') as [|]
        by eauto using well_formed_lock_dec with LTS.

    - specialize (IHL n0') as [|]; attac.
      right; attac.
    - right; attac.
  Qed.


  Lemma lock_chain_connect [N0 N1] [na] [n0 n1] [L] :
    well_formed N0 ->
    (N0 =(na)=> N1) ->
    ~ List.In n1 L ->
    NoDup L ->
    ~ lock_chain N0 n0 L n1 ->
    lock_chain N1 n0 L n1 ->
    exists m0 m1 v, na = NComm m0 m1 Q v
                    /\ ((m0 = n0 /\ m1 = n1 /\ L = [])
                        \/ (m0 = n0 /\ m1 <> n1 /\ exists L1, L = m1 :: L1 /\ lock_chain N0 m1 L1 n1)
                        \/ (m0 <> n0 /\ m1 = n1 /\ exists L0, L = L0 ++ [m0] /\ lock_chain N0 n0 L0 m0)
                        \/ (exists L0 L1, L = L0 ++ [m0;m1] ++ L1 /\ lock_chain N0 n0 L0 m0  /\ lock_chain N0 m1 L1 n1)
                       ).

  Proof.
    intros.

    generalize dependent n0 n1.
    induction L; intros; hsimpl in *.
    1: consider (exists v, na = NComm n0 n1 Q v) by eauto using well_formed_new_lock_send_Q; eattac.

    rename a into n0'.

    smash_eq n0 n0'.
    {
      consider (n0 = n1).
      {
        enough (Forall (eq n0) L /\ n1 = n0) as Hx. 1: destruct Hx; eauto.
        eauto using lock_self_lock_chain_uniq with LTS.
      }
      bs.
    }

    assert (well_formed N1) by attac.

    destruct (well_formed_lock_dec N0 n0 n0'); eauto 2 with LTS.
    - assert (~ lock_chain N0 n0' L n1) by eattac.

      kill H2. (* TODO autorewrite NoDup *)
      normalize_hyp @IHL.
      specialize (IHL n1 n0').
      repeat (specialize (IHL ltac:(auto))).
      hsimpl in IHL.
      destruct `(_ \/ _) as [|[|[|]]]; hsimpl in *; hsimpl in *; eexists _,_,_; split; eauto.
      + do 2 right. left; ieattac.
      + do 3 right.
        (* split; eauto. split; eauto. *)
        exists []; eattac.
      + assert (~ lock N0 m0 n1) by attac.
        smash_eq m0 n0.
        2: right; right; left; ieattac.
        consider (n0' = n1) by (eapply SRPC_lock_set_uniq; eauto with LTS).
        bs.
      + smash_eq m0 n0.
        2: right; right; right; repeat split; auto; eattac.
        consider (n0' = m1) by (eapply SRPC_lock_set_uniq; eauto with LTS).
        bs.
    - consider (exists v, na = NComm n0 n0' Q v) by eauto using well_formed_new_lock_send_Q.
      eexists _,_,_; split; eauto.

      (* remember (NComm _ _ _ _) as a. clear Heqa. *)

      destruct (well_formed_lock_chain_dec N0 n0' L n1); eauto 2 with LTS.
      + smash_eq n0' n1.
        right; left; repeat split; auto; exists L; split; auto.

      + kill H2.
        normalize_hyp @IHL.
        specialize (IHL n1 n0').
        repeat (specialize (IHL ltac:(auto))).
        hsimpl in IHL.
        repeat (destruct `(_ \/ _) as [|]); hsimpl in IHL0; attac.
        exfalso.
        hsimpl in *.
        bs (List.In m1 (L0 ++ m0 :: m1 :: L1)).
  Qed.


  Lemma net_dep_close [N0 N1 na n0 n1] :
    well_formed N0 ->
    (N0 =(na)=> N1) ->
    ~ trans_lock N0 n0 n1 ->
    trans_lock N1 n0 n1 ->
    exists m0 m1 v, na = NComm m0 m1 Q v
                    /\ (m0 = n0 \/ (m0 <> n0 /\ trans_lock N0 n0 m0 /\ trans_lock N1 n0 m0))
                    /\ (m1 = n1 \/ (m1 <> n1 /\ trans_lock N0 m1 n1 /\ trans_lock N1 m1 n1)).

  Proof.
    intros.
    consider (
        exists L,
          lock_chain N1 n0 L n1
          /\ NoDup L
          /\ not (List.In n0 L)
          /\ not (List.In n1 L)).
    {
      apply dep_lock_chain in H2 as [? [? ?]].
      eauto using lock_chain_dedup with LTS.
    }
    clear H2.

    consider (exists m0 m1 v, na = NComm m0 m1 Q v
                              /\ ((m0 = n0 /\ m1 = n1 /\ L = [])
                                  \/ (m0 = n0 /\ m1 <> n1 /\ exists L1, L = m1 :: L1 /\ lock_chain N0 m1 L1 n1)
                                  \/ (m0 <> n0 /\ m1 = n1 /\ exists L0, L = L0 ++ [m0] /\ lock_chain N0 n0 L0 m0)
                                  \/ (exists L0 L1, L = L0 ++ [m0;m1] ++ L1 /\ lock_chain N0 n0 L0 m0  /\ lock_chain N0 m1 L1 n1)
             )) by eauto using lock_chain_connect with LTS.

    destruct `(_ \/ _) as [|[|[|]]]; hsimpl in *;
      eexists _,_,_; split; eauto; split; try (solve [left; eauto]); right; eattac.
  Qed.


  Lemma net_M_dep_close [N0 N1 : MNet] [na n0 n1] :
    well_formed '' N0 ->
    (N0 =(na)=> N1) ->
    ~ trans_lock N0 n0 n1 ->
    trans_lock N1 n0 n1 ->
    exists m0 m1 v, na = NComm m0 m1 Q (MValP v)
                    /\ (m0 = n0 \/ (m0 <> n0 /\ trans_lock N0 n0 m0 /\ trans_lock N1 n0 m0))
                    /\ (m1 = n1 \/ (m1 <> n1 /\ trans_lock N0 m1 n1 /\ trans_lock N1 m1 n1)).

  Proof.
    intros.
    destruct (MNAct_to_PNAct na) eqn:?.
    - assert ('' N0 =(p)=> '' N1) by eauto using net_deinstr_act_do.
      consider (exists m0 m1 v, p = @NComm PAct _ m0 m1 Q v
                                /\ (m0 = n0 \/ (m0 <> n0 /\ trans_lock N0 n0 m0 /\ trans_lock N1 n0 m0))
                                /\ (m1 = n1 \/ (m1 <> n1 /\ trans_lock N0 m1 n1 /\ trans_lock N1 m1 n1))
               )
        by eauto using net_dep_close with LTS.

      exists m0, m1, v.
      destruct na.
      + destruct m.
        destruct p; bs.
        destruct p; bs.
        destruct a; bs.
      + destruct p; doubt.
        attac.
    - assert ('' N0 = '' N1) by eauto using net_deinstr_act_skip.
      rewrite `('' N0 = _) in *.
      bs.
  Qed.


  Lemma SRPC_net_new_lock_no_unlock [N0 N1 : PNet] [na] [n0 n1 m0 m1] :
    well_formed N0 ->
    (N0 =(na)=> N1) ->
    ~ lock N0 n0 n1 ->
    lock N1 n0 n1 ->
    lock N0 m0 m1 ->
    lock N1 m0 m1.

  Proof.
    intros.

    assert (lock N1 m0 m1 \/ ~ lock N1 m0 m1) as [|]
        by eauto using well_formed_lock_dec with LTS.
    1: auto.

    assert (exists v', na = NComm n0 n1 Q v') by eauto using well_formed_new_lock_send_Q.
    assert (exists v', na = NComm m1 m0 R v') by (eapply net_unlock_on_reply; eauto with LTS).
    hsimpl in *.
    bs.
  Qed.


  Lemma SRPC_net_new_lock_no_unlock_dep [N0 N1 : PNet] [na] [n0 n1 m0 m1] :
    well_formed N0 ->
    (N0 =(na)=> N1) ->
    ~ lock N0 n0 n1 ->
    lock N1 n0 n1 ->
    trans_lock N0 m0 m1 ->
    trans_lock N1 m0 m1.

  Proof.
    intros.
    apply dep_lock_chain in H3.
    hsimpl in *.
    generalize dependent m0.
    induction L; intros; hsimpl in *.
    1: enough (lock N1 m0 m1); eauto using SRPC_net_new_lock_no_unlock with LTS.

    rename a into m0'.
    specialize (IHL ltac:(auto) m0' ltac:(auto)).
    enough (lock N1 m0 m0'); eauto 3 using SRPC_net_new_lock_no_unlock with LTS.
  Qed.


  Lemma deadlocked_M_get_lock [MN0 n] :
    SRPC_net '' MN0 ->
    deadlocked n '' MN0 ->
    exists n', lock MN0 n n'.

  Proof.
    intros.
    unfold deadlocked in *.
    hsimpl in *.
    eapply (deadset_lock_set `(DeadSet DS '' MN0)) in H0.
    hsimpl in *.
    unfold lock_set in *.
    consider (exists n0 : Name, serv_lock [n0] (NetMod.get n '' MN0)) by (eauto using SRPC_serv_get_lock with LTS).
    eattac.
  Qed.


  Lemma locked_M_NoRecvR [MN0 : MNet]  [n n'] :
    well_formed MN0 ->
    lock MN0 n n' ->
    NoRecvR_MQ (mserv_i (MN0 n)).
  Proof.
    intros.

    eapply Forall_forall.
    intros.
    destruct x; auto.
    destruct n0.
    destruct &t; auto.
    destruct (NetMod.get n MN0) as [MQ M S] eqn:?.

    enough (n0 = n').
    {
      subst.

      unfold lock, lock_set in *.
      hsimpl in *.
      consider (serv_lock L _).
      apply (`(~ List.In (n', R, v) _)).
      unfold net_deinstr, deinstr in *.
      ltac1:(autorewrite with LTS in * ).
      rewrite `(NetMod.get n MN0 = _) in *.
      destruct S.
      unfold NetGet in *.
      attac.
    }

    destruct S as [I P O].
    enough ((exists c0, SRPC (Locked c0 n0) P) /\ (exists c', SRPC (Locked c' n') &P)) as [[c0 ?] [c' ?]]
        by (consider (Locked c0 n0 = Locked c' n') by (eapply SRPC_inv; eattac); auto).
    split.
    - destruct (NetMod.get n (net_deinstr MN0)) as [I0 P0 O0] eqn:?.

      enough (P = P0 /\ List.In (n0, R, v) I0) as [? ?].
      {
        subst.
        unfold net_deinstr in *. simpl in *.
        ltac1:(autorewrite with LTS in * ).
        enough (exists c0, SRPC_serv (Locked c0 n0) (serv I0 P0 O0)) by attac.
        rewrite <- `(_ = serv I0 P0 O0).

        replace (deinstr (NetMod.get n MN0)) with (NetMod.get n (net_deinstr MN0)) by (unfold net_deinstr, deinstr; attac).

        eauto using well_formed_in_net_R_in_lock.
      }

      unfold net_deinstr in *.
      ltac1:(autorewrite with LTS in * ).
      split.
      + unfold deinstr in *.
        rewrite `(NetMod.get n MN0 = _) in *.
        attac.
      + rewrite `(NetMod.get n MN0 = _) in *.
        unfold NetGet in *.
        eattac.
    - assert (lock_set MN0 [n'] n) by eauto using lock_singleton with LTS.
      unfold lock_set in *.
      unfold net_deinstr, deinstr in *.
      ltac1:(autorewrite with LTS in * ).
      rewrite `(NetMod.get n MN0 = _) in *.
      eapply lock_SRPC_Locked.
      2: eattac.

      enough (NetMod.get n (net_deinstr MN0) = serv (&I ++ MQ_r MQ) P (MQ_s MQ ++ &O))
        by (enough (AnySRPC_serv (serv (&I ++ MQ_r MQ) P (MQ_s MQ ++ &O))); eauto with LTS).

      unfold net_deinstr, deinstr in *.
      ltac1:(autorewrite with LTS in * ).
      rewrite `(NetMod.get n MN0 = _) in *.
      auto.
  Qed.

  Hint Immediate locked_M_NoRecvR : LTS.


  Lemma deadlocked_M_NoRecvR [MN0 n] :
    well_formed '' MN0 ->
    deadlocked n '' MN0 ->
    NoRecvR_MQ (mserv_i (MN0 n)).
  Proof.
    intros.
    consider (deadlocked _ _).
    hsimpl in *.
    consider (exists L, lock_set '' MN0 L n /\ incl L x)
      by eauto using deadset_lock_set.
    consider (exists n1, lock_set '' MN0 [n1] n) by (eapply net_get_lock; eauto with LTS).
    unfold lock_set in *.
    eapply locked_M_NoRecvR; eauto with LTS.
    eattac.
  Qed.

  Hint Immediate deadlocked_M_NoRecvR : LTS.


  Lemma KIC_invariant_H_lock [MN0 MN1 : MNet] [na] :
    well_formed MN0 ->
    (forall n0 n1, lock MN0 n0 n1 -> lock (MN0 n0) = Some n1) ->
    (MN0 =(na)=> MN1) ->
    forall n0 n1, lock MN1 n0 n1 -> lock (MN1 n0) = Some n1.

  Proof.
    intros.
    assert (lock MN0 n0 n1 \/ ~ lock MN0 n0 n1) as [|] by eauto using well_formed_lock_dec.
    - assert (lock (MN0 n0) = Some n1) by auto.
      destruct (lock (MN1 n0)) as [n|] eqn:?.
      + enough (n = n1) by (subst; auto).
        assert (forall v, na <> NComm n0 n Q (MValP v)).
        {
          destruct na; intros ? ?; doubt.
          hsimpl in *.
          absurd (n0 <> n0); eauto using locked_M_no_send.
        }
        eauto using M_preserve_steady_lock, eq_sym with LTS.
      + consider (exists v, na = NTau n0 (MActP (Recv (n1, R) v))) by eauto using Rad_set_unlock with LTS.
        exfalso.
        assert (net_deinstr MN0 = MN1) by (eapply net_deinstr_act_skip; eauto; simpl; eauto).
        rewrite `(net_deinstr MN0 = _) in *.
        assert (lock_set MN1 [n1] n0) by eauto using lock_singleton with LTS.

        (* TODO no taus when locked *)
        destruct (NetMod.get n0 MN1) as [MQ0 M0 [I0 P0 O0]] eqn:?.
        destruct (NetMod.get n0 MN1) as [I0' P0' O0'] eqn:?.
        unfold lock, lock_set in *.
        unfold net_deinstr, deinstr in *.
        hsimpl in *.
        compat_hsimpl in *.
        kill H7. (* serv_lock *)
        assert (~ List.In (n1, R, v) I1) by (intros ?; eapply H11; eattac).
        hsimpl in *.
        eassert (MQ_s _ = [] /\ O0 = []) by eauto using app_eq_nil.
        compat_hsimpl in *.
        absurd (List.In (n1, R, v) ((I1 ++ [(n1, R, v)]) ++ MQ_r MQ)); attac.
    - consider (exists v, na = NComm n0 n1 Q (MValP v)) by eauto using SRPC_M_net_new_lock_query.
      (* TODO fix this disgrace *)
      kill H2. hsimpl in *.
      smash_eq n0 n1; compat_hsimpl in *; hsimpl in |- *; attac.
      all: unfold NetGet; attac.
  Qed.

  Lemma deadlocked_preserve_M_lock1 [na] [MN0 MN1 : MNet] n :
    well_formed MN0 ->
    (forall n0 n1, lock MN0 n0 n1 -> lock (MN0 n0) = Some n1) ->
    deadlocked n MN0 ->
    (MN0 =(na)=> MN1) ->
    lock (MN0 n) = lock (MN1 n).

  Proof.
    intros.

    assert (exists path, net_deinstr MN0 =[ path ]=> MN1) as [? ?] by eauto using transp_sound1.
    assert (deadlocked n MN1) by eauto with LTS.

    assert (exists m, lock MN0 n m) by eauto using deadlocked_M_get_lock with LTS.
    hsimpl in *.
    enough (lock MN1 n m).
    {
      replace (lock (MN0 n)) with (Some m) by eauto using eq_sym with LTS.
      replace (lock (MN1 n)) with (Some m) by eauto using eq_sym, KIC_invariant_H_lock with LTS.
      auto.
    }

    eauto with LTS.
  Qed.


  Lemma KIC_well_formed [MN] : KIC MN -> well_formed MN.
  Proof. intros; kill H. Qed.

  Hint Immediate KIC_well_formed : LTS.


  Lemma KIC_invariant_well_formed1 [MN0 MN1] [a] :
    (MN0 =(a)=> MN1) ->
    KIC MN0 ->
    well_formed MN1.

  Proof.
    intros.
    consider (exists ppath, net_deinstr MN0 =[ppath]=> MN1) by eauto using transp_sound1.
    eauto with LTS.
  Qed.

  Hint Resolve KIC_invariant_well_formed1 : LTS.


  Lemma KIC_lock_C [MN n0 n1] : KIC MN -> lock MN n0 n1 -> lock (MN n0) = Some n1.
  Proof.
    intros.
    consider (KIC MN).
  Qed.

  Hint Immediate KIC_lock_C : LTS.


  Lemma deadlocked_preserve_M_lock [mpath MN0 MN1 n] :
    KIC MN0 ->
    deadlocked n MN0 ->
    (MN0 =[mpath]=> MN1) ->
    lock (MN0 n) = lock (MN1 n).
  Proof.
    intros.
    assert (forall n0 n1, lock MN0 n0 n1 -> lock (MN0 n0) = Some n1) by (consider (KIC MN0); attac).
    assert (well_formed MN0) by eauto with LTS.
    clear H.

    generalize dependent MN0.
    induction mpath; intros.
    1: attac.

    hsimpl in *.
    transitivity '(lock (N1 n)).
    - eauto using deadlocked_preserve_M_lock1 with LTS.
    - consider (exists ppath, net_deinstr MN0 =[ppath]=> N1) by eauto using transp_sound1.
      assert (well_formed N1) by eauto with LTS.
      assert (deadlocked n N1) by eauto 2 with LTS.
      eauto using KIC_invariant_H_lock with LTS.
  Qed.


  Lemma deadlocked_vis_preserve_M_lock_set [na] [MN0 MN1 : MNet] [n L] :
    (forall m (v : Val), na <> recv (m, R) # v) ->
    (MN0 ~(n @ na)~> MN1) ->
    lock_set MN0 L n ->
    lock_set MN1 L n.

  Proof.
    intros.

    unfold lock_set, net_deinstr in *.
    ltac1:(autorewrite with LTS in * ).

    destruct (NetMod.get n MN0) as [MQ0 M0 [I0 P0 O0]] eqn:?.
    destruct (NetMod.get n MN1) as [MQ1 M1 [I1 P1 O1]] eqn:?.

    compat_hsimpl in *. compat_hsimpl in *.

    kill H1.
    consider (MQ_s MQ0 = [] /\ O0 = []) by auto using app_eq_nil.
    compat_hsimpl in *.

    consider (mserv MQ0 _ _ =(_)=> _); compat_hsimpl in *; attac 4; hsimpl in |- *;
      rewrite `(MQ_s _ = _) in *; attac.
    - destruct n0 as [? [|]].
      2: bs.
      assert (~ List.In (n1, R, v0) [(n0, Q, v)]) by (intros ?; attac).
      assert (~ List.In (n1, R, v) (I1 ++ MQ_r MQ0)) by iattac.
      iattac.
      rewrite app_assoc in *.
      apply in_app_or in H6 as [|]; bs.
    - rewrite <- app_assoc in *.
      bs.
    - kill TP; doubt.
      compat_hsimpl in *.
      assert (~ (In (n1, R, v0) (I0 ++ MQ_r MQ1))) by eauto.
      bs (In (n1, R, v0) I0).
  Qed.

  Lemma serv_lock_preserve_in_wait [a MQ0 M0 S0 MQ1 M1 S1 L m] :
    serv_lock L (mserv MQ0 M0 S0) ->
    serv_lock L (mserv MQ1 M1 S1) ->
    (mserv MQ0 M0 S0 =(a)=> mserv MQ1 M1 S1) ->
    List.In m (wait (next_state M0)) ->
    List.In m (wait (next_state M1)).

  Proof.
    intros.
    destruct_ma &a; kill H1; simpl; auto.
    - destruct t; simpl; hsimpl in *; destruct s; destruct lock0 as [n0|]; simpl; auto.
      smash_eq n n0; attac.
    - kill H.
      blast_cases; attac.
    - attac.
    - compat_hsimpl in *.
      blast_cases; attac.
      blast_cases; unfold NetGet; attac.
      remember wait0 as w.
      rewrite Heqw at 1.
      clear Heqw.
      induction wait0; attac.
  Qed.


  Lemma deadlocked_vis_preserve_in_wait [na] [MN0 MN1 : MNet] [n n'] :
    SRPC_net MN0 ->
    deadlocked n MN0 ->
    (forall m (v : Val), na <> recv (m, R) # v) ->
    (MN0 ~(n @ na)~> MN1) ->
    List.In n' (wait (MN0 n)) ->
    List.In n' (wait (MN1 n)).
  Proof.
    intros.
    consider (exists m, lock MN0 n m) by eauto using deadlocked_M_get_lock with LTS.
    apply lock_singleton in H4; eauto with LTS.

    assert (lock_set MN1 [m] n)
      by eauto using deadlocked_vis_preserve_M_lock_set.

    unfold lock_set in *.

    ltac1:(autounfold with LTS_get).

    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.
    destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.

    assert (serv_lock [m] (mserv MQ0 M0 S0)).
    {
      unfold net_deinstr in *.
      unfold NetGet in *.
      ltac1:(autorewrite with LTS in * ).
      attac.
    }

    assert (serv_lock [m] (mserv MQ1 M1 S1)).
    {
      unfold net_deinstr in *.
      ltac1:(autorewrite with LTS in * ).
      attac.
    }

    assert (mserv MQ0 M0 S0 =(na)=> mserv MQ1 M1 S1).
    {
      hsimpl in *. hsimpl in *.
      now rewrite <- `(NetMod.get n MN0 = _).
    }

    eapply serv_lock_preserve_in_wait.
    3: eauto.
    all: eauto.
    ltac1:(autounfold with LTS_get in * ).
    rewrite `(NetMod.get n MN0 = _) in *.
    attac.
  Qed.


  Lemma deadlocked_preserve_M_in_wait1 na (MN0 MN1 : MNet) n m :
    SRPC_net MN0 ->
    deadlocked n MN0 ->
    (MN0 =(na)=> MN1) ->
    List.In m (wait (MN0 n)) ->
    List.In m (wait (MN1 n)).

  Proof.
    intros.

    consider (exists m, lock MN0 n m) by eauto using deadlocked_M_get_lock with LTS.

    kill H1.
    - smash_eq n n0.
      + destruct a; doubt.
        eapply deadlocked_vis_preserve_in_wait; eauto; bs.
        eapply deadlocked_vis_preserve_in_wait; eauto; bs.
        eapply deadlocked_vis_preserve_in_wait; eauto; bs.
      + ltac1:(autounfold with LTS_get).
        replace (NetMod.get n MN1) with (NetMod.get n MN0); attac.
    - assert (List.In m ( wait (N0' n))).
      + smash_eq n n0.
        * eapply deadlocked_vis_preserve_in_wait; eauto. intros.
          destruct v; bs.
        * ltac1:(autounfold with LTS_get).
          replace (NetMod.get n N0') with (NetMod.get n MN0); attac.
      + smash_eq n n0.
        * hsimpl in *.
          smash_eq n n'; destruct v; ltac1:(autounfold with LTS_get in * ); attac.
          unfold NetGet; compat_hsimpl in *; attac.
        * ltac1:(autounfold with LTS_get in * ).
          hsimpl in *.
          hsimpl in |- *.
          smash_eq n n'; destruct v; compat_hsimpl in *; hsimpl in |- *; attac.
  Qed.


  Lemma deadlocked_preserve_M_in_wait mpath (MN0 MN1 : MNet) n m :
    well_formed MN0 ->
    deadlocked n MN0 ->
    (MN0 =[mpath]=> MN1) ->
    List.In m (wait (MN0 n)) ->
    List.In m (wait (MN1 n)).

  Proof.
    intros.

    generalize dependent MN0.
    induction mpath; intros.
    1: attac.

    hsimpl in *.
    assert (List.In m (wait (N1 n))).
    - eapply deadlocked_preserve_M_in_wait1; eauto with LTS.
    - consider (exists ppath, net_deinstr MN0 =[ppath]=> N1) by eauto using transp_sound1.
      assert (well_formed N1) by eauto with LTS.
      assert (deadlocked n N1) by eauto 2 with LTS.
      eauto with LTS.
  Qed.


  Lemma net_deinstr_act_or [MN0 MN1 : MNet] [ma] :
    (MN0 =(ma)=> MN1) ->
    net_deinstr MN0 = MN1 \/ exists a, net_deinstr MN0 =(a)=> MN1.

  Proof.
    clear.
    intros.
    destruct (MNAct_to_PNAct ma) eqn:?.
    - right. exists p. eauto using net_deinstr_act_do.
    - left. eauto using net_deinstr_act_skip.
  Qed.


  Lemma deadlocked_M_dep_invariant1 [MN0 MN1 : MNet] [n0 n1 a] :
    (MN0 =(a)=> MN1) ->
    deadlocked n0 MN0 ->
    trans_lock MN0 n0 n1 ->
    trans_lock MN1 n0 n1.

  Proof.
    intros.
    destruct (@net_deinstr_act_or MN0 MN1 a); auto.
    - rewrite <- `(net_deinstr MN0 = _). auto.
    - hsimpl in *. eauto using deadlocked_dep_invariant1.
  Qed.


  Lemma hot_of_hot [MN p n] : hot MN p n -> p = hot_of MN n.

  Proof.
    clear.
    intros.
    consider (hot _ p _).
    destruct p.
    attac.
  Qed.

  Lemma serv_lock_preserve_lock_id [a MQ0 s0 S0 MQ1 s1 S1 L] :
    serv_lock L (mserv MQ0 s0 S0) ->
    serv_lock L (mserv MQ1 s1 S1) ->
    (mserv MQ0 s0 S0 =(a)=> mserv MQ1 s1 S1) ->
    lock_id (next_state s0) = lock_id (next_state s1).

  Proof.
    intros.
    destruct_ma &a; kill H1; simpl; auto.
    - destruct t; simpl; hsimpl in *; destruct s; destruct lock0 as [n0|]; simpl; auto.
      smash_eq n n0; attac.
    - kill H.
      destruct S1.
      hsimpl in *.
      bs.
    - attac.
    - unfold NetGet in *; compat_hsimpl in *.
      blast_cases; eattac.
      rewrite next_state_Send_all. eauto.
  Qed.

  Lemma deadlocked_vis_preserve_M_lock_id [na MN0 MN1 n] :
    SRPC_net '' MN0 ->
    deadlocked n MN0 ->
    (forall m (v : Val), na <> recv (m, R) # v) ->
    (MN0 ~(n @ na)~> MN1) ->
    lock_id (MN0 n) = lock_id (MN1 n).

  Proof.
    intros.

    consider (exists m, lock MN0 n m) by eauto using deadlocked_M_get_lock with LTS.
    apply lock_singleton in H3; eauto with LTS.

    assert (lock_set MN1 [m] n)
      by eauto using deadlocked_vis_preserve_M_lock_set.

    unfold lock_set in *.

    ltac1:(autounfold with LTS_get).

    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.
    destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.

    assert (serv_lock [m] (mserv MQ0 M0 S0)).
    {
      unfold net_deinstr in *.
      ltac1:(autorewrite with LTS in * ).
      rewrite `(NetMod.get n MN0 = _) in H3.
      auto.
    }

    assert (serv_lock [m] (mserv MQ1 M1 S1)).
    {
      unfold net_deinstr in *.
      ltac1:(autorewrite with LTS in * ).
      rewrite `(NetMod.get n MN1 = _) in H4.
      auto.
    }

    eapply (serv_lock_preserve_lock_id
              `(serv_lock _ (mserv MQ0 M0 S0))
              `(serv_lock _ (mserv MQ1 M1 S1))).

    hsimpl in *. hsimpl in *.
    rewrite `(NetMod.get n MN0 = _) in *.

    eauto.
  Qed.


  Lemma deadlocked_preserve_M_lock_id1 [na MN0 MN1 n] :
    SRPC_net '' MN0 ->
    deadlocked n MN0 ->
    (MN0 =(na)=> MN1) ->
    lock_id (MN0 n) = lock_id (MN1 n).

  Proof.
    intros.

    consider (exists m, lock MN0 n m) by eauto using deadlocked_M_get_lock with LTS.

    consider (_ =(_)=> _).
    - smash_eq n n0.
      + destruct a; doubt.
        eapply deadlocked_vis_preserve_M_lock_id; eauto; bs.
        eapply deadlocked_vis_preserve_M_lock_id; eauto; bs.
        eapply deadlocked_vis_preserve_M_lock_id; eauto; bs.
      + ltac1:(autounfold with LTS_get).
        replace (NetMod.get n MN1) with (NetMod.get n MN0); attac.
    - transitivity '(lock_id (N0' n)).
      + smash_eq n n0.
        * eapply deadlocked_vis_preserve_M_lock_id; eauto. intros.
          destruct v; bs.
        * ltac1:(autounfold with LTS_get).
          replace (NetMod.get n N0') with (NetMod.get n MN0); attac.
      + smash_eq n n0.
        * hsimpl in *.
          smash_eq n n'; destruct v; ltac1:(autounfold with LTS_get in * ); compat_hsimpl in *; attac.
        * ltac1:(autounfold with LTS_get).
          smash_eq n n'; destruct v; compat_hsimpl in *; attac.
  Qed.


  Lemma deadlocked_preserve_M_lock_id [mpath MN0 MN1 n] :
    well_formed '' MN0 ->
    deadlocked n MN0 ->
    (MN0 =[mpath]=> MN1) ->
    lock_id (MN0 n) = lock_id (MN1 n).

  Proof.
    intros.

    generalize dependent MN0.
    induction mpath; intros.
    1: attac.

    hsimpl in *.
    transitivity '(lock_id (N1 n)).
    - eapply deadlocked_preserve_M_lock_id1; eauto with LTS.
    - consider (exists ppath, '' MN0 =[ppath]=> N1) by eauto using transp_sound1.
      assert (well_formed N1) by eauto with LTS.
      assert (deadlocked n N1) by eauto 2 with LTS.
      eauto with LTS.
  Qed.

  Lemma deadlocked_preserve_hot_probe1 [na MN0 MN1 p n] :
    SRPC_net '' MN0 ->
    deadlocked n MN0 ->
    (MN0 =(na)=> MN1) ->
    hot MN0 p n ->
    hot MN1 p n.

  Proof.
    intros.
    consider (hot _ p n).
    constructor; auto.
    now replace (lock_id (MN1 (init p))) with (lock_id (MN0 (init p))) by
      eauto using deadlocked_preserve_M_lock_id1 with LTS.
  Qed.


  Lemma deadlocked_preserve_hot_probe [mpath MN0 MN1 p n] :
    well_formed '' MN0 ->
    deadlocked n MN0 ->
    (MN0 =[mpath]=> MN1) ->
    hot MN0 p n ->
    hot MN1 p n.

  Proof.
    intros.

    generalize dependent MN0.
    induction mpath; intros.
    1: hsimpl in *; auto.

    hsimpl in *.
    assert (hot N1 p n).
    - eapply deadlocked_preserve_hot_probe1; eauto with LTS.
    - consider (exists ppath, '' MN0 =[ppath]=> N1) by eauto using transp_sound1.
      assert (well_formed N1) by eauto with LTS.
      assert (deadlocked n N1) by eauto 2 with LTS.
      eauto with LTS.
  Qed.

  Lemma deadlocked_preserve_hot_of1 [MN0 MN1 a m] :
    well_formed '' MN0 ->
    deadlocked m '' MN0 ->
    (MN0 =(a)=> MN1) ->
    hot_of MN0 m = hot_of MN1 m.

  Proof.
    intros.
    enough (hot MN1 (hot_of MN0 m) m) by auto using hot_of_hot.
    assert (hot MN0 (hot_of MN0 m) m) by auto using hot_hot_of.
    eauto using deadlocked_preserve_hot_probe1 with LTS.
  Qed.


  Lemma KIC_invariant_H_wait [MN0 MN1 : MNet] [a] [n0 n1] :
    KIC MN0 ->
    (MN0 =(a)=> MN1) ->
    lock MN1 n0 n1 ->
    NoRecvQ_from n0 (mserv_i (MN1 n1)) ->
    List.In n0 (wait (MN1 n1)).

  Proof.
    intros.
    assert (lock MN0 n0 n1 \/ ~ lock MN0 n0 n1) as [|] by eauto using well_formed_lock_dec with LTS.
    - assert (NoRecvQ_from n0 (mserv_i (MN0 n1)) \/ ~ NoRecvQ_from n0 (mserv_i (MN0 n1))) as [|] by eauto using NoRecvQ_from_dec.
      + assert (List.In n0 (wait (MN0 n1))) by (consider (KIC MN0); auto).
        assert (lock (MN0 n0) = Some n1) by (consider (KIC MN0); auto).
        (* clear - H1 H H5 H3 H2 H6 H4 H7 H0. *)
        consider (MN0 =(a)=> _).
        * hsimpl in *.
          ltac1:(autounfold with LTS_get in * ).
          destruct_ma &a0; doubt; hsimpl in *; eauto.
          -- smash_eq n n1; compat_hsimpl in *; attac.
          -- smash_eq n n1; compat_hsimpl in *; attac.
             simpl in *.
             blast_cases; attac.
          -- smash_eq n n1; compat_hsimpl in *; attac.
          -- smash_eq n n1; compat_hsimpl in *; attac.
             subst; simpl in *.
             unfold NetGet in *.
             blast_cases; attac.
             remember wait0 as w.
             rewrite Heqw at 1.
             clear Heqw.
             induction wait0; attac.
        * destruct v; hsimpl in *.
          -- ltac1:(autounfold with LTS_get in * ).
             smash_eq n' n n1; hsimpl in |- *; auto; hsimpl in *.
             all: try (rewrite `(NetMod.get n' MN0 = _) in * ).
             all: try (rewrite `(NetMod.get n MN0 = _) in * ).
             all: auto.
          -- smash_eq n n0.
             {
               exfalso.
               apply lock_singleton in H3; eauto with LTS.
               unfold lock_set in *.
               clear - H3 H7.
               unfold net_deinstr in *.
               ltac1:(autorewrite with LTS in * ).
               attac.
               rewrite `(NetMod.get n MN0 = _ ) in *.
               kill H3.
               blast_cases.
               bs.
             }
             ltac1:(autounfold with LTS_get in * ).
             hsimpl.
             smash_eq n n' n1; hsimpl in |- *; auto; doubt; compat_hsimpl in *; destruct &t; doubt.
             all: unfold NetGet in *.
             all: try (rewrite `(NetMod.get n MN0 = _) in * ).
             all: try (rewrite `(NetMod.get n' MN0 = _) in * ).
             all: auto.
             all: subst; hsimpl in *; compat_hsimpl in |- *; hsimpl in |- *; auto.
             1: auto using in_in_remove.
             smash_eq n0 n'. 2: apply in_in_remove; auto.
             clear - H1.
             exfalso.
             kill H1.
             hsimpl in *.
             unfold lock_set, net_deinstr in *.
             ltac1:(autorewrite with LTS in * ).
             kill H0.
             destruct P.
             hsimpl in *.
             eapply H3 with (v:=v); eattac.
      + assert (lock (MN0 n0) = Some n1) by (consider (KIC MN0); auto).
        assert (exists v, a = NTau n1 (MActP (Recv (n0, Q) v))) by eauto using net_TrRecvQ_pop.
        hsimpl in *.
        consider (_ =(_)=> _).
        hsimpl in *.
        hsimpl in *; hsimpl in |- *; hsimpl in |- *; auto.
        ltac1:(autounfold with LTS_get in * ).
        simpl in *; destruct lock0 eqn:?; subst; attac.
    - consider (exists v, a = NComm n0 n1 Q (MValP v)) by eauto using SRPC_M_net_new_lock_query with LTS.
      absurd (List.In (TrRecv (n0, Q) v) (mserv_i (MN1 n1))). 1: attac.
      kill H0. compat_hsimpl in *.
      unfold NetGet in *.
      attac.
  Qed.

  (* TODO to Locks *)
  Lemma deadlocked_trans_lock_loop [N n0] :
    well_formed N ->
    deadlocked n0 N ->
    exists n1, trans_lock N n0 n1 /\ trans_lock N n1 n1.

  Proof with eattac.
    intros BSRPC Hd.

    assert (forall n, AnySRPC_serv (NetMod.get n N)) as Hsrpc by eauto with LTS.

    consider (exists DS, List.In n0 DS /\ DeadSet DS N).
    hsimpl in *. (* TODO why? *)
    rename H0 into HDS.
    rename H into HIn.

    destruct (deadset_dep_set HDS HIn) as [L HL].

    assert (L <> []) as HLnil.
    {
      destruct L; doubt.
      destruct (deadset_lock_set HDS HIn) as [L' [HL' _]].
      consider (exists n1, lock_set N [n1] n0) by (eapply net_get_lock; eauto with LTS).
      unfold dep_set in HL.
      assert (lock N n0 n1) by eattac.
      assert (trans_lock N n0 n1) as HD' by attac.
      apply HL in HD'.
      bs.
    }

    specialize (deadset_dep_set_deadset HDS HL HLnil HIn) as HDSL.

    consider (exists (n1 : Name) (L' : Names), lock_chain N n0 L' n1 /\ incl L (n1 :: L')).
    {
      eapply longest_lock_chain; eauto with LTS.
    }

    enough (trans_lock N n1 n1) by eauto with LTS.

    enough (exists n2, List.In n2 (n1::L) /\ trans_lock N n1 n2) as [n2 [HIn1 HD1]].
    {
      kill HIn1.
      smash_eq n1 n2.
      eapply (lock_chain_split_in) with (n1:=n2) in H
          as (L0 & L1 & HEq' & HLc0 & HLc1).
      apply lock_chain_dep in HLc1.
      eauto with LTS.
      apply `(incl _ _) in H1.
      attac.
    }

    assert (List.In n1 L) as HIn2 by (apply HL; eapply lock_chain_dep; eauto).

    assert (exists n2, lock N n1 n2) as [n2 HL1].
    {
      apply (deadset_lock_set HDSL) in HIn2 as [L2 [HL2 _]].
      apply net_get_lock in HL2 as [n2 HL2]; eauto with LTS.
      exists n2.
      eattac.
    }

    exists n2; split; auto with LTS.

    enough (List.In n2 L) by attac.

    eapply deadset_in; eauto.
  Qed.


  Lemma sends_probe_extend_r [MQ0 MQ' M0 S0] [nc p] :
    sends_probe nc p (mserv MQ0 M0 S0) ->
    sends_probe nc p (mserv (MQ0 ++ MQ') M0 S0).

  Proof.
    intros.
    generalize dependent MQ0 S0 nc p.
    induction MQ'; intros; hsimpl in *; hsimpl in |- *.
    - attac.
    - replace (MQ0 ++ a :: MQ') with ((MQ0 ++ [a]) ++ MQ') by attac.
      apply IHMQ'.
      clear IHMQ'.
      generalize dependent a MQ0.
      induction M0; intros; attac.
      + kill H; rewrite <- app_assoc; eauto with LTS.
      + kill H; eauto with LTS.
  Qed.


  Lemma sends_probe_proc [MQ0 M0 S0 S0'] [nc p] :
    sends_probe nc p (mserv MQ0 M0 S0) ->
    sends_probe nc p (mserv MQ0 M0 S0').

  Proof.
    intros.
    ltac1:(dependent induction H); eauto with LTS.
  Qed.

  Lemma sends_probe_wait_s_l1 [MQ0 S0] [ss sl si sw n sd] [nc l t p] :
    sends_probe nc p (mserv MQ0 (MSend_all l t p (MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;wait:=sw|})) S0) ->
    sends_probe nc p (mserv MQ0 (MSend_all l t p (MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;wait:=n :: sw|})) S0).

  Proof.
    intros.
    induction l.
    - kill H; hsimpl in *; hsimpl in |- *.
      + econstructor 1; eattac.
      + econstructor 2; subst; kill H4; eattac.
    - destruct (NameTag_eq_dec nc (a, &t)).
      + subst. econstructor 3.
      + kill H.
        apply IHl in H1.
        econstructor 4; eattac.
  Qed.


  Lemma sends_probe_wait_l1 [MQ0 S0] [ss sl si sw n sd] [nc p] :
    sends_probe nc p (mserv MQ0 (MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;wait:=sw|}) S0) ->
    sends_probe nc p (mserv MQ0 (MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;wait:=n :: sw|}) S0).

  Proof.
    intros.
    kill H; hsimpl in *; hsimpl in |- *.
    - econstructor 1; eattac.
    - econstructor 2; subst; kill H4; eattac.
  Qed.


  Lemma sends_probe_wait_l [MQ0 S0] [ss sl si sw sw' sd] [nc p] :
    sends_probe nc p (mserv MQ0 (MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;wait:=sw|}) S0) ->
    sends_probe nc p (mserv MQ0 (MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;wait:=sw' ++ sw|}) S0).

  Proof.
    intros.
    induction sw'; eauto using sends_probe_wait_l1.
  Qed.


  Lemma sends_probe_skip1 [MQ0 n s S0] [nc t p] :
    sends_probe nc p (mserv MQ0 (s) S0) ->
    sends_probe nc p (mserv MQ0 (MSend (n, t) p s) S0).

  Proof.
    intros.
    destruct (NameTag_eq_dec nc (n, &t)); eattac.
  Qed.


  Lemma sends_probe_skip [MQ0 l s S0] [nc t p] :
    sends_probe nc p (mserv MQ0 (s) S0) ->
    sends_probe nc p (mserv MQ0 (MSend_all l t p s) S0).

  Proof.
    intros.
    induction l; eauto using sends_probe_skip1.
  Qed.


  Lemma sends_probe_skip_inv1 [MQ0 n s s' S0] [nc t p] :
    sends_probe nc p (mserv MQ0 (s) S0) ->
    sends_probe nc p (mserv MQ0 (MSend (n, t) p s') S0) ->
    sends_probe nc p (mserv MQ0 (MSend (n, t) p s) S0).

  Proof.
    intros.
    destruct (NameTag_eq_dec nc (n, &t)); eattac.
  Qed.


  Lemma sends_probe_skip_inv [MQ0 l s s' S0] [nc t p] :
    sends_probe nc p (mserv MQ0 (s) S0) ->
    sends_probe nc p (mserv MQ0 (MSend_all l t p s') S0) ->
    sends_probe nc p (mserv MQ0 (MSend_all l t p s) S0).

  Proof.
    intros.
    induction l; eauto.
    kill H0; eattac.
  Qed.


  Lemma sends_probe_skip_neq1 [MQ0 n s S0] [nc t p p'] :
    p <> p' ->
    sends_probe nc p (mserv MQ0 (s) S0) <->
      sends_probe nc p (mserv MQ0 (MSend (n, t) p' s) S0).

  Proof.
    eattac.
  Qed.


  Lemma sends_probe_skip_neq [MQ0 l s S0] [nc t p p'] :
    p <> p' ->
    sends_probe nc p (mserv MQ0 (s) S0) <->
      sends_probe nc p (mserv MQ0 (MSend_all l t p' s) S0).

  Proof.
    split; intros.
    - induction l; eattac.
    - induction l; eattac.
      kill H0;eattac.
  Qed.


  Hint Rewrite <- sends_probe_skip_neq1 sends_probe_skip_neq using spank : LTS_concl.
  Hint Resolve -> sends_probe_skip_neq1 sends_probe_skip_neq : LTS.


  Lemma sends_probe_wait_skip_l1 [MQ0 S0] [ss sl si sw n n' t sd] [p] :
    n <> n' ->
    sends_probe (n, t) p (mserv MQ0 (MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;wait:=n'::sw|}) S0) ->
    sends_probe (n, t) p (mserv MQ0 (MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;wait:=sw|}) S0).

  Proof.
    intros.

    kill H0.
    - simpl in *. subst.
      econstructor 1; eattac.
    - simpl in *; subst. kill H5; econstructor 2; eattac.
  Qed.


  Lemma sends_probe_wait_skip_l [MQ0 S0] [ss sl si sw sw' sd n t] [p] :
    ~ List.In n sw' ->
    sends_probe (n, t) p (mserv MQ0 (MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;wait:=sw' ++ sw|}) S0) ->
    sends_probe (n, t) p (mserv MQ0 (MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;wait:=sw|}) S0).

  Proof.
    intros.
    generalize dependent sw n.
    induction sw'; intros; hsimpl in *; eauto using sends_probe_wait_skip_l1.
  Qed.


  Lemma sends_probe_skip_s1 [MQ0 S0] [nc nc'] [p p'] [s] :
    nc <> nc' ->
    sends_probe nc p (mserv MQ0 (MSend nc' p' s) S0) <->
      sends_probe nc p (mserv MQ0 (s) S0).

  Proof.
    split; intros.
    - kill H0.
    - eattac.
  Qed.


  Lemma sends_probe_skip_s_in [MQ0 S0] [n t t'] [l p p'] [s] :
    ~ List.In n l ->
    sends_probe (n, t) p (mserv MQ0 (MSend_all l t' p' s) S0) <->
      sends_probe (n, t) p (mserv MQ0 (s) S0).

  Proof.
    split; intros.
    - induction l; attac.
      apply sends_probe_skip_s1 in H0; attac.
    - induction l; attac.
  Qed.

  Hint Rewrite -> sends_probe_skip_s1 sends_probe_skip_s_in using spank : LTS_concl.
  Hint Resolve <- sends_probe_skip_s1 sends_probe_skip_s_in : LTS.


  Lemma mserv_sends_probe_sent [MS0 MS1 : MServ] [ma : MAct] [nc p] :
    (MS0 =(ma)=> MS1) ->
    sends_probe nc p MS0 ->
    ~ sends_probe nc p MS1 ->
    ma = send nc (MValM p).

  Proof.
    intros.
    destruct_ma &ma; compat_hsimpl in *; doubt.
    6: destruct (NameTag_eq_dec nc (n, &t)); subst; auto.
    6: destruct (MProbe_eq_dec p v) as [?|HEqv]; subst; auto.
    all: exfalso; apply H1; clear H1; subst.
    all: eauto using sends_probe_extend_r, sends_probe_proc.
    - kill H0.
      + destruct MQ0; kill H7.
        * destruct s; simpl in *; subst.
          destruct p.
          eauto with LTS.
        * hsimpl in *.
          destruct s eqn:?; simpl in *; subst lock0.
          remember {| self := self0;
                     lock_id := lock_id0;
                     lock := Some n';
                     wait := n :: wait0;
                     alarm := alarm0
                   |} as s1.
          replace {| init := self0; index := lock_id0 |} with
            {| init := self s1; index := lock_id s1 |} by (subst; auto).

          assert (NoRecvR_from n' MQ0) by (intros ? ?; apply (H v1); eattac).
          destruct &t; smash_eq n0 n; destruct p; attac.
          smash_eq n0 n'; eattac.
          1: specialize (H v); bs.
          smash_eq n n'; attac.
          1: econstructor 1; eattac.
          specialize (H v); bs.
      + destruct MQ0; kill H7.

        smash_eq n n0.
        * destruct s eqn:?; simpl in *; subst lock0.
          remember {| self := self0;
                     lock_id := lock_id0;
                     lock := Some n';
                     wait := n :: wait0;
                     alarm := alarm0
                   |} as s1.
          replace {| init := self0; index := lock_id0 |} with
            {| init := self s1; index := lock_id s1 |} by (subst; auto).

          assert (NoRecvR_from n' MQ0) by (intros ? ?; apply (H v0); eattac).
          destruct &t; smash_eq n n'.
          3: specialize (H v); bs.
          econstructor 4; eattac.
          econstructor 2; eattac.
          econstructor 4; eattac.
          econstructor 2; eattac.
          hsimpl.
          econstructor 2; kill H4; eattac.

        * assert (List.In n0 (wait s) \/ (exists v0, List.In (TrRecv (n0, Q) v0) MQ0)) by (kill H4; eattac). clear H4.
          destruct s eqn:?; simpl in *; subst lock0.
          remember {| self := self0;
                     lock_id := lock_id0;
                     lock := Some n';
                     wait := n :: wait0;
                     alarm := alarm0
                   |} as s1.
          replace {| init := self0; index := lock_id0 |} with
            {| init := self s1; index := lock_id s1 |} by (subst; auto).

          assert (NoRecvR_from n' MQ0) by (intros ? ?; apply (H v0); eattac).
          destruct &t; smash_eq n n'.
          3: specialize (H v); bs.
          econstructor 4; eattac.
          econstructor 2; eattac. destruct `(_ \/ _); attac.
          econstructor 2; eattac.
          hsimpl.
          econstructor 2; eattac.
    - kill H0.
      all: destruct MQ0; hsimpl in *; bs.

    - destruct n.
      destruct s; destruct &t; simpl in *.
      + kill H0; hsimpl in *.
        * destruct MQ0; kill H7.
          hsimpl in *.
          econstructor 1; ieattac.
          specialize (H v0). bs.
        * destruct MQ0; kill H7.
          hsimpl in *.
          econstructor 2; destruct H4; ieattac.
          specialize (H v); bs.
          specialize (H v); bs.
      + destruct lock0 as [n0|].
        2: kill H0; bs.
        smash_eq n n0; hsimpl in |- *.
        * destruct p, msg; hsimpl in *.
          smash_eq init1 self0; hsimpl in *.
          -- destruct (PeanoNat.Nat.eqb lock_id0 index1); hsimpl in *.
             ++ {
                 kill H0; hsimpl in *.
                 -- destruct MQ0; kill H7; hsimpl in *; econstructor 1; ieattac.
                    specialize (H v0); bs.
                 -- destruct MQ0; kill H7; hsimpl in *; econstructor 2; kill H4; ieattac.
                    specialize (H v); bs.
                    specialize (H v); bs.
               }
             ++ {
                 kill H0; hsimpl in *.
                 -- destruct MQ0; kill H7; hsimpl in *; econstructor 1; ieattac.
                    specialize (H v0); bs.
                 -- destruct MQ0; kill H7; hsimpl in *; econstructor 2; kill H4; ieattac.
                    specialize (H v); bs.
                    specialize (H v); bs.
               }
          -- destruct nc.
             remember {|
                 self := self0;
                 lock_id := lock_id0;
                 lock := Some n;
                 wait := wait0;
                 alarm := alarm0
               |} as s0.

             destruct (MProbe_eq_dec {| init := init0; index := index0 |} {| init := init1; index := index1 |}).

             2: subst; apply sends_probe_skip_neq; attac.
             2: kill H0.
             2: destruct MQ0; kill H8; econstructor 1; ieattac.
             2: specialize (H v0); bs.
             2: destruct MQ0; kill H8; doubt; econstructor 2; kill H4; ieattac.
             2: specialize (H v); bs.
             2: specialize (H v); bs.

             hsimpl in e.

             generalize dependent s0.
             induction wait0; intros.
             {
               simpl in *.
               kill H0.
               ** destruct MQ0; kill H8; hsimpl in *.
                  econstructor 1; eattac.
               ** destruct MQ0; kill H8; hsimpl in *. 1: bs.
                  econstructor 2; ieattac.
                  specialize (H v0); bs.
             }
             destruct &t. 1: bs.

             smash_eq n0 a.
             1: econstructor 3.
             hsimpl in *.

             specialize IHwait0 with (s0:=
                           {|
                             self := self0;
                             lock_id := lock_id0;
                             lock := Some n;
                             wait := wait0;
                             alarm := alarm0|}).

             eapply sends_probe_wait_skip_l1 in H0. 2: iattac.

             specialize IHwait0 with (2:=eq_refl).

             eauto using sends_probe_wait_s_l1.

        * destruct nc.
          destruct &t. 1: kill H0.
          subst.
          destruct p; simpl in *; subst.
          kill H0; hsimpl in *.
          ++ destruct MQ0; kill H7; econstructor 1; ieattac.
             specialize (H v0); bs.
          ++ destruct MQ0; kill H7; econstructor 2; kill H4; ieattac.
             specialize (H v); bs.
             specialize (H v); bs.
  Qed.


  Lemma vis_sends_probe_sent [MN0 MN1 : MNet] [a] [n0 n1 n'] [t p] :
    (MN0 ~(n' @ a)~> MN1) ->
    sends_probe (n1, t) p (NetMod.get n0 MN0) ->
    ~ sends_probe (n1, t) p (NetMod.get n0 MN1) ->
    n' = n0 /\ a = send (n1, t) ^ p.

  Proof.
    intros.
    smash_eq n0 n'.
    - kill H.
      consider (a = send (n1, &t) ^ p) by (eapply mserv_sends_probe_sent; eattac).
    - replace (NetMod.get n0 MN1) with (NetMod.get n0 MN0) by eauto using NV_stay.
      bs.
  Qed.


  Lemma sends_probe_sent [MN0 MN1 : MNet] [a] [n0 n1] [t p] :
    (MN0 =(a)=> MN1) ->
    sends_probe (n1, t) p (NetMod.get n0 MN0) ->
    ~ sends_probe (n1, t) p (NetMod.get n0 MN1) ->
    a = NComm n0 n1 t ^ p.

  Proof.
    intros.
    kill H.
    - consider (_ /\ a0 = send (n1, &t) ^ p) by (eauto using vis_sends_probe_sent).
      bs.
    - destruct (sends_probe_dec (n1, &t) p (NetMod.get n0 N0')); eauto with LTS.
      + consider (_ /\ recv (n, t0) v = send (n1, &t) ^ p) by eauto using vis_sends_probe_sent.
        destruct v; bs.
      + consider (n = n0 /\ send (n', t0) v = send (n1, &t) ^ p) by eauto using vis_sends_probe_sent.
        destruct v; kill H5.
        auto.
  Qed.


  Lemma sends_probe_init_skip [MQ MQ' s S n n' v p] :
    NoRecvR_from n' MQ -> (* We won't unlock *)
    NoSends_MQ MQ -> (* We won't change the lock_id *)
    lock (next_state s) = Some n' -> (* We are locked *)
    init p = self (next_state s) -> index p = lock_id (next_state s) -> (* Our hot probe *)
    sends_probe (n, R)
      p
      (mserv
         (MQ ++ TrRecv (n, Q) v :: MQ') (* There is a query incoming... *)
         (s) (* We are ready to take it *)
         S
      ).

  Proof.
    intros.
    induction s.
    - econstructor 1; eattac.
    - assert (sends_probe (n, R) p
                (mserv (MQ ++ TrRecv (n, Q) v :: MQ') (s ) &S)) by eattac.
      destruct to.
      destruct (MProbe_eq_dec p msg); subst.
      + eauto using sends_probe_skip1.
      + econstructor 4; eattac.
  Qed.


  Lemma sends_probe_prop_skip [MQ MQ' s S n n' p] :
    NoRecvR_from n' MQ -> (* We won't unlock *)
    NoSends_MQ MQ -> (* We won't change the lock_id *)
    lock (next_state s) = Some n' -> (* We are locked *)
    init p <> self (next_state s) -> (* The probe is not ours *)
    List.In n (wait (next_state s)) \/ (exists v, List.In (TrRecv (n, Q) v) MQ) -> (* The receiver will be in wait *)
    sends_probe (n, R) p (mserv (MQ ++ EvRecv (n', R) p :: MQ') (s) S).

  Proof.
    intros.
    induction s.
    - econstructor 2; eattac.
    - assert (sends_probe (n, R) p
                (mserv (MQ ++ EvRecv (n', R) p :: MQ') (s ) &S)) by eattac.
      destruct to.
      destruct (MProbe_eq_dec p msg); subst.
      + eauto using sends_probe_skip1.
      + econstructor 4; eattac.
  Qed.


  Lemma sends_probe_prop_foreign [MN0 n0 n1 n2 p MQ] :
    KIC MN0 ->
    lock MN0 n0 n1 ->
    lock MN0 n1 n2 ->
    init p <> n1 ->
    (* List.In (EvRecv (n2, R) p) (mserv_i (MN0 n1)) -> *) (* TODO requires tighter KIC-wait *)
    mserv_i (MN0 n1) = MQ ++ [EvRecv (n2, R) p] ->
    sends_probe (n0, R) p (NetMod.get n1 MN0).

  Proof.
    intros.

    destruct (NetMod.get n1 MN0) as [MQ1 s1 S1] eqn:?.

    (* assert (mserv_i (MN0 n1) = MQ1) by (ltac1:(autounfold with LTS_get in * ); attac). *)
    (* rewrite `(mserv_i (MN0 n1) = _) in *.  clear H4. *)
    consider (MQ1 = mserv_i (MN0 n1)) by (ltac1:(autounfold with LTS_get in * ); attac).
    rewrite `(mserv_i (MN0 n1) = _) in *. clear H3.


    (* consider (exists MQ10 MQ11 : list Event, MQ1 = MQ10 ++ EvRecv (n2, R) p :: MQ11) by eauto using in_split. *)

    eapply sends_probe_prop_skip; eauto with LTS; subst.
    - enough (NoRecvR_MQ MQ) by eauto with LTS.
      enough (NoRecvR_MQ (mserv_i (MN0 n1))) by (ltac1:(autounfold with LTS_get in * ); attac).
      now eauto using locked_M_NoRecvR with LTS.

    - enough (no_sends_in n1 MN0) by (unfold no_sends_in, NoTrSend in *; attac).
      eauto using lock_M_no_sends_in.
    - assert (lock (MN0 n1) = Some n2) by eauto with LTS.
      ltac1:(autounfold with LTS_get in * ); attac.
    - enough (self (next_state s1) = n1) by (subst; eauto with LTS).
      enough (self (MN0 n1) = n1) by (ltac1:(autounfold with LTS_get in * ); attac 2).
      consider (KIC MN0). (* TODO to lemma... *)

    - consider (pq_client n0 (NetMod.get n1 '' MN0)) by eauto with LTS.
      + unfold net_deinstr in *.
        compat_hsimpl in *.

        assert ((exists v0, List.In (TrRecv (n0, Q) v0) MQ) \/ ~ (exists v0, List.In (TrRecv (n0, Q) v0) MQ)) as [|].
        {
          clear.
          induction MQ.
          right; ieattac.
          kill IHMQ; eattac.
          destruct a.
          - right; ieattac.
          - destruct (NameTag_eq_dec (n0, Q) n); subst.
            + left; ieattac.
            + right; ieattac.
          - right; ieattac.
        }
        1: eattac.

        left.
        simpl in *.
        enough (NoRecvQ_from n0 (MQ ++ [EvRecv (n2, R) p])).
        {
          consider (KIC MN0).
          specialize (H_wait_C n0 n1 ltac:(auto)).
          ltac1:(autounfold with LTS_get in * ).
          attac.
        }

        intros ? ?.
        consider (List.In (TrRecv (n0, Q) v0) MQ \/ List.In _ [EvRecv (n2, R) p])
          by (eauto using in_app_or).

        eattac.
      + enough (NoRecvQ_from n0 (MQ ++ [EvRecv (n2, R) p])).
        {
          consider (KIC MN0).
          specialize (H_wait_C n0 n1 ltac:(auto)).
          ltac1:(autounfold with LTS_get in * ).
          attac.
        }
        enough (NoRecvQ_from n0 MQ).
        {
          intros ? ?.
          consider (List.In (TrRecv (n0, Q) v) MQ \/ List.In _ [EvRecv (n2, R) p])
            by eauto using in_app_or.
          bs.
        }
        hsimpl in *.
        intros ? ?.

        unfold net_deinstr in *.
        compat_hsimpl in *.
        destruct S1 as [I1 P1 O1].

        enough (~ List.In (n0, Q, v) &I).
        {
          eattac. eapply H6.
          unfold deinstr in *.
          eattac.
        }

        assert (proc_client n0 P).
        {
          unfold deinstr in *.
          eattac.
        }
        assert (NetMod.get n1 '' MN0 = serv &I P &O).
        {
          rewrite <- `(_ = serv &I P &O).
          unfold net_deinstr, deinstr; hsimpl in *; hsimpl in *; attac.
        }
        eauto with LTS.

      + enough (NoRecvQ_from n0 (MQ ++ [EvRecv (n2, R) p])).
        {
          consider (KIC MN0).
          specialize (H_wait_C n0 n1 ltac:(auto)).
          ltac1:(autounfold with LTS_get in * ).
          attac.
        }
        enough (NoRecvQ_from n0 MQ).
        {
          intros ? ?.
          consider (List.In (TrRecv (n0, Q) v0) MQ \/ List.In _ [EvRecv (n2, R) p])
            by eauto using in_app_or.
          bs.
        }
        hsimpl in *.
        intros ? ?.

        unfold net_deinstr in *.
        compat_hsimpl in *.
        destruct S1 as [I1 P1 O1].

        enough (~ List.In (n0, Q, v0) &I).
        {
          eattac. eapply H6.
          unfold deinstr in *.
          eattac.
        }

        assert (List.In (n0, R, v) &O).
        {
          unfold deinstr in *.
          eattac.
        }
        assert (NetMod.get n1 '' MN0 = serv &I P &O).
        {
          rewrite <- `(_ = serv &I P &O).
          unfold net_deinstr, deinstr; hsimpl in *; hsimpl in *; attac.
        }
        eauto with LTS.
  Qed.


  Lemma probe_pass_on [MN0 MN1 : MNet] [n0 n1 n2] [p] :
    KIC MN0 ->
    lock MN0 n0 n1 ->
    lock MN0 n1 n2 ->
    init p <> n1 ->
    (MN0 =(NComm n2 n1 R ^ p)=> MN1) ->
    sends_probe (n0, R) p (NetMod.get n1 MN1).

  Proof.
    intros.

    (* TODO Merge with sends_probe_prop_foreign;
         instead of entire KIC, bring whatever you can and should click
     *)

    destruct (NetMod.get n1 MN1) as [MQ0 s0 S0] eqn:?.

    assert (well_formed '' MN1)
      by ((consider (exists ppath, '' MN0 =[ppath]=> '' MN1)
            by eauto using transp_sound with LTS); eauto with LTS).

    assert (lock MN1 n0 n1).
    {
      destruct (well_formed_lock_dec '' MN1 n0 n1); auto.
      assert (exists v, NComm n2 n1 R ^ p = NComm n1 n0 R (MValP v)) by eauto using SRPC_M_net_unlock_reply with LTS.
      hsimpl in *; bs.
    }
    assert (lock MN1 n1 n2).
    {
      destruct (well_formed_lock_dec '' MN1 n1 n2); auto.
      assert (exists v, NComm n2 n1 R ^ p = NComm n2 n1 R (MValP v)) by eauto using SRPC_M_net_unlock_reply with LTS.
      hsimpl in *; bs.
    }

    assert (NoRecvR_MQ (mserv_i (MN1 n1))) by eauto using locked_M_NoRecvR with LTS.

    assert (NoSends_MQ (mserv_i (MN1 n1))).
    {
      assert (no_sends_in n1 MN1) by eauto using lock_M_no_sends_in.  (* TODO hint resolve *)
      unfold no_sends_in, NoTrSend in *.
      unfold NetGet. destruct (NetMod.get n1 MN1) eqn:?; auto.
    }
    assert (lock (MN1 n1) = Some n2) by eauto using KIC_invariant_H_lock with LTS.
    assert (lock (MN1 n1) = Some n2) by eauto using KIC_invariant_H_lock with LTS.
    assert (pq_client n0 (NetMod.get n1 '' MN1)) by eauto with LTS.
    assert (wait (MN1 n1) = wait (MN0 n1)).
    {
      clear - H3. kill H3; hsimpl in *.
      ltac1:(autounfold with LTS_get in * ).
      smash_eq n1 n2; unfold NetGet in *; attac.
    }
    assert (NoRecvQ_from n0 (mserv_i (MN1 n1)) -> List.In n0 (wait (MN1 n1)))
      by eauto using KIC_invariant_H_wait with LTS.

    kill H3.
    hsimpl in *.
    hsimpl in |- *.
    simpl in *; hsimpl in *.

    assert (n1 = self (next_state s0)).
    {
      consider (KIC MN0).
      ltac1:(autounfold with LTS_get in * ).
      clear - H14 H15 H_self_C.
      specialize (H_self_C n1).
      smash_eq n1 n2; hsimpl in * |- ; eattac.
    }

    unfold NetGet in *.
    compat_hsimpl in *.
    eapply sends_probe_prop_skip; eauto with LTS; subst.
    unfold net_deinstr in *.
    compat_hsimpl in H17.
    destruct S0.
    hsimpl in H17.

    assert ((exists v0, List.In (TrRecv (n0, Q) v0) MQ) \/ ~ (exists v0, List.In (TrRecv (n0, Q) v0) MQ)) as [|].
    {
      clear.
      induction MQ.
      right; ieattac.
      kill IHMQ; eattac.
      destruct a.
      - right; ieattac.
      - destruct (NameTag_eq_dec (n0, Q) n); subst.
        + left; ieattac.
        + right; ieattac.
      - right; ieattac.
    }
    1: eattac.
    compat_hsimpl in *.
    blast_cases; eattac. unfold NetGet in *. attac.
    enough (NoRecvQ_from n0 (MQ ++ [EvRecv (n2, R) p])) by eauto.
    intros ? ?.
    apply in_app_or in H17 as [|].
    2: bs.
    eattac.
  Qed.


  Lemma KIC_invariant_H_alarm [MN0 MN1 : MNet] [a] [n0] :
    KIC MN0 ->
    (MN0 =(a)=> MN1) ->
    deadlocked n0 '' MN1 ->
    exists n1, trans_lock MN1 n0 n1 /\ ac n1 MN1.

  Proof.
    intros.
    have (well_formed '' MN0) by eauto with LTS.
    have (well_formed '' MN1) by eauto with LTS.
    consider (exists n0', trans_lock MN1 n0 n0' /\ trans_lock MN1 n0' n0')
      by re_have (eauto using deadlocked_trans_lock_loop with LTS).

    enough (exists n1, trans_lock MN1 n0' n1 /\ ac n1 MN1) by (hsimpl in *; exists n1; eattac).
    clear H1 n0 H4.
    rename n0' into n0.

    assert (trans_lock MN0 n0 n0 \/ ~ trans_lock MN0 n0 n0) as [|].
    {
      enough (forall n1, trans_lock MN1 n0 n1 -> trans_lock MN0 n0 n1 \/ ~ trans_lock MN0 n0 n1) by eauto.
      clear H5. (* trans_lock *)
      intros n1 ?.
      apply dep_lock_chain in H1 as [L [? ?]].
      generalize dependent n0.
      induction L; intros; hsimpl in *.
      - destruct (well_formed_lock_dec '' MN0 n0 n1); eauto with LTS.
        consider (exists v, a = NComm n0 n1 Q # v) by eauto using SRPC_M_net_new_lock_query with LTS.
        right; intros ?.
        consider (trans_lock MN0 n0 n1).
        smash_eq n2 n1.
        apply `(_ <> _).
        eauto using SRPC_M_net_no_immediate_relock, eq_sym with LTS.
      - specialize (IHL ltac:(auto) a0 ltac:(auto)) as [|].
        + destruct (well_formed_lock_dec '' MN0 n0 a0); eauto with LTS.
          consider (exists v, a = NComm n0 a0 Q # v) by eauto using SRPC_M_net_new_lock_query with LTS.
          right; intros ?.
          consider (trans_lock MN0 n0 n1).
          * assert (n1 = a0). eauto using SRPC_M_net_no_immediate_relock with LTS. bs.
          * assert (n2 = a0). eauto using SRPC_M_net_no_immediate_relock with LTS. bs.
        + destruct (well_formed_lock_dec '' MN0 n0 a0); eauto with LTS.
          * right; intros ?.
            eapply `(~ trans_lock _ _ _).
            consider (trans_lock MN0 n0 n1).
            -- assert (n1 = a0). eauto with LTS. eapply `(lock_uniq_type '' MN0); eauto. bs.
            -- assert (n2 = a0). eauto with LTS. eapply `(lock_uniq_type '' MN0); eauto. bs.
          * consider (exists v, a = NComm n0 a0 Q # v) by eauto using SRPC_M_net_new_lock_query with LTS.
            right; intros ?.
            consider (trans_lock MN0 n0 n1).
            -- assert (n1 = a0). eauto using SRPC_M_net_no_immediate_relock with LTS. bs.
            -- assert (n2 = a0). eauto using SRPC_M_net_no_immediate_relock with LTS. bs.
    }
    - consider (exists m, trans_lock MN0 n0 m /\ ac m MN0) by (consider (KIC MN0); auto).
      assert (deadlocked n0 '' MN0) by eauto using dep_self_deadlocked with LTS.
      assert (trans_lock MN1 n0 m) by eauto using deadlocked_M_dep_invariant1 with LTS.

      consider (ac m MN0).
      + exists m.
        split; eauto 2 with LTS.
        constructor 1.
        consider (KIC MN0).
        eauto using net_preserve_alarm.
      + assert (sends_probe (m0, R) (hot_of MN0 m) (NetMod.get m' MN1) \/ ~ sends_probe (m0, R) (hot_of MN0 m) (NetMod.get m' MN1))
          as [|] by eauto using sends_probe_dec.
        * exists m.
          split; auto.

          assert (hot_of MN0 m = hot_of MN1 m) by eauto 3 using deadlocked_preserve_hot_of1 with LTS.
          rewrite `(hot_of _ _ = _) in *.

          assert (deadlocked m '' MN0) by eauto 3 with LTS.
          assert (deadlocked m0 '' MN0) by (consider (m = m0 \/ _); eauto 3 with LTS).
          econstructor 2. 3: eauto.
          consider (m = m0 \/ trans_lock MN0 m m0) by attac > [left|right]; auto.
          -- eauto 3 using deadlocked_M_dep_invariant1 with LTS.
          -- consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound1; eauto 2 with LTS.
        * exists m.
          split; auto.

          consider (a = NComm m' m0 R ^ (hot_of MN0 m)) by eauto using sends_probe_sent with LTS.
          smash_eq m0 m.
          -- constructor 3 with (n':=m'); eauto.
             1: consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS; eauto 4 with LTS.

             clear - H0.
             kill H0. hsimpl in *.
             unfold hot_ev_of, hot_of in *.
             ltac1:(autounfold with LTS_get in * ).
             hsimpl in |- *.
             smash_eq m0 m'; compat_hsimpl in *.
             rewrite H; attac.
             attac.
          -- destruct `(m = m0 \/ trans_lock MN0 m m0).
             1: bs.

             assert (deadlocked m0 '' MN0) by eauto 3 with LTS.
             assert (deadlocked m '' MN0) by eauto 3 with LTS.
             assert (exists m'', trans_lock MN0 m m'' /\ lock MN0 m'' m0).
             {
               apply dep_lock_chain in H9. hsimpl in H9.
               ltac1:(rev_induction L); intros; hsimpl in *.
               - exists m.
                 split; auto.
                 eapply dep_reloop; re_have (eauto with LTS).
               - exists a; split; eauto.
                 eauto using lock_chain_dep.
             } (* TODO TO LEMMA *)

             assert (~ hot MN0 (hot_of MN0 m) m0) by (intros Hx; kill Hx).

             hsimpl in *.
             assert (sends_probe (m'', R) (hot_of MN0 m) (NetMod.get m0 MN1)) by eauto using probe_pass_on.

             assert (trans_lock MN1 m m'') by eauto 4 using deadlocked_M_dep_invariant1 with LTS.

             assert (lock MN1 m'' m0) by
               (consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound1;
                eauto 4 using deadlocked_lock_on_invariant with LTS
               ).
             assert (trans_lock MN1 m m0) by eauto 4 using deadlocked_M_dep_invariant1 with LTS.

             econstructor 2.
             3: replace (hot_of MN1 m) with (hot_of MN0 m) by eauto 3 using deadlocked_preserve_hot_of1 with LTS.
             3: eauto 4 with LTS.
             all: auto.
      + exists m.
        split; auto.

        assert (lock (MN0 m) = Some n') by eauto with LTS.
        assert (deadlocked m '' MN0) by eauto 3 with LTS.
        assert (lock MN1 m n')
          by (consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS; eauto 4 with LTS).
        assert (well_formed '' MN1)
          by (consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS; eauto 4 with LTS).

        assert (hot_ev_of MN1 n' m = hot_ev_of MN0 n' m).
        {
          unfold hot_ev_of.
          consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS.
          replace (hot_of MN1 m) with (hot_of MN0 m) by eauto using deadlocked_preserve_hot_of1, eq_sym with LTS.
          auto.
        }

        kill H0.
        * smash_eq m n.
          2: econstructor 3; eauto; unfold NetGet in *; replace (NetMod.get m MN1) with (NetMod.get m MN0) by eauto using NV_stay, eq_sym; rewrite `(hot_ev_of _ _ _ = _); eauto.

          apply in_split in H10. hsimpl in H10.

          unfold hot_ev_of, hot_of in *.
          ltac1:(autounfold with LTS_get in * ).

          destruct_ma &a0; doubt; compat_hsimpl in *.
          -- exfalso.
             absurd (no_sends_in m (NetMod.put m
                                      (mserv
                                         ((l1 ++
                                             EvRecv (n', R) {| init := m; index := lock_id (next_state M) |}
                                             :: l2) ++ [TrSend (n, &t) v]) M (serv I0 P2 O1)) MN0)).
             2: { eapply lock_M_no_sends_in; eattac. }

             intros Hx. clear - Hx.
             unfold no_sends_in, NoTrSend in *.
             blast_cases.
             hsimpl in *.
             apply Forall_app in Hx.
             apply Forall_app in Hx.
             attac.

          -- simpl in *.
             assert (self s = m).
             {
               clear - H Heqm0 H16.
               consider (KIC MN0).
               specialize (H_self_C m).
               ltac1:(autounfold with LTS_get in * ).
               rewrite `(NetMod.get m MN0 = _) in *.
               eattac.
             }
             destruct l1.
             1: { attac. }

             destruct s; attac.
             econstructor 3; eauto.
             unfold hot_ev_of, hot_of.
             ltac1:(autounfold with LTS_get in * ).
             ltac1:(autorewrite with LTS in * ).
             simpl.
             blast_cases; attac.

          -- exfalso.
             attac.
             destruct P0 as [I0 P0 O0].
             apply lock_singleton in H9; eauto with LTS.
             apply lock_singleton in H12; eauto with LTS.
             unfold lock_set, net_deinstr in *.
             attac.
             destruct P1 as [I1 P1 O1].
             kill H12.
             kill H9.
             hsimpl in *.
             unfold deinstr in *.
             attac.
             kill H18; attac.
             kill H9.
             apply `(~ In ((n', R), v) (I0 ++ MQ_r l1 ++ MQ_r l2)).
             destruct n as [? [|]]; attac.
             consider (_ /\ handle (n, Q) = None) by eauto. bs.
             consider (_ /\ handle (n, Q) = None) by eauto.
             consider (n' = n) by attac.
             attac.
          -- bs.
          -- simpl in *.
             assert (self s = m).
             {
               clear - H Heqm0 H16.
               consider (KIC MN0).
               specialize (H_self_C m).
               ltac1:(autounfold with LTS_get in * ).
               unfold NetGet in *. simpl in *.
               rewrite `(NetMod.get m MN0 = _) in *.
               eattac.
             }
             destruct l1.
             ++ econstructor 1.
                ltac1:(autorewrite with LTS in * ).
                hsimpl in *.
                unfold NetGet in *.
                hsimpl in |- *. rewrite PeanoNat.Nat.eqb_refl in *. attac.
             ++ kill H10.
                simpl in *.
                econstructor 3; eauto.
                unfold hot_ev_of, hot_of.
                ltac1:(autounfold with LTS_get in * ).
                ltac1:(autorewrite with LTS in * ).
                rewrite `(NetMod.get self0 MN0 = _) in *.
                blast_cases; compat_hsimpl in *; attac.
        * constructor 3 with (n':=n').
          1: auto.
          rewrite `(hot_ev_of _ _ _ = hot_ev_of _ _ _).
          clear - H10 H15 H16.
          hsimpl in *. hsimpl in *.
          unfold hot_ev_of, hot_of in *.
          ltac1:(autounfold with LTS_get in * ).
          all: smash_eq m n n'0; destruct v; hsimpl in *; hsimpl in |- *;
            try (rewrite `(NetMod.get m _ = _) in * );
            try (rewrite `(NetMod.get n _ = _) in * );
            try (rewrite `(NetMod.get n'0 _ = _) in * ); hsimpl in *; doubt.
          all: compat_hsimpl in *; eattac.

    - assert (deadlocked n0 '' MN1) by re_have (eauto using dep_self_deadlocked).
      consider (exists m0 m1 v, (n0 = m0 \/ trans_lock MN1 n0 m0) /\ a = NComm m0 m1 Q (MValP v)).
      {
        consider (exists (m0 m1 : Name) (v : Val),
                     a = NComm m0 m1 Q # v /\
                       (m0 = n0 \/ m0 <> n0 /\ trans_lock MN0 n0 m0 /\ trans_lock MN1 n0 m0) /\
                       (m1 = n0 \/ m1 <> n0 /\ trans_lock MN0 m1 n0 /\ trans_lock MN1 m1 n0))
          by re_have (eauto 2 using net_M_dep_close).
        do 2 (destruct `(_ \/ _)); eattac.
      }

      assert (lock MN1 m0 m1)
        by (consider (~ lock MN0 m0 m1 /\ lock MN1 m0 m1);
            eauto using SRPC_M_net_query_new_lock with LTS).

      exists m1.
      split.
      1: { consider (_ \/ _); eauto with LTS. }

      assert (trans_lock MN1 n0 m0) by
        (destruct `(n0 = m0 \/ trans_lock MN1 n0 m0); subst; eauto 4 using dep_reloop, dep_loop, trans_lock_seq1 with LTS).
      assert (forall n : Name, AnySRPC_serv (NetMod.get n '' MN1)) by re_have (eauto with LTS).
      assert (sends_probe (m0, R) (hot_of MN1 m1) (NetMod.get m1 MN1)).
      {
        assert (deadlocked m1 '' MN1) by eauto 4 using dep_self_deadlocked with LTS.
        destruct (NetMod.get m1 MN1) as [MQ1 s1 S1] eqn:?.
        consider (exists m2, lock MN1 m1 m2) by re_have (eauto 3 using deadlocked_M_get_lock with LTS).

        assert (NoRecvR_MQ (mserv_i (MN1 m1))) by re_have (eauto using deadlocked_M_NoRecvR with LTS).
        assert (NoSends_MQ (mserv_i (MN1 m1))).
        {
          assert (no_sends_in m1 MN1) by eauto using lock_M_no_sends_in.
          ltac1:(autounfold with LTS_get).
          unfold no_sends_in, NoTrSend in *.
          destruct (NetMod.get m1 MN1).
          auto.
        }
        assert (lock (next_state s1) = Some m2).
        {
          assert (lock (MN1 m1) = Some m2) by eauto using KIC_invariant_H_lock with LTS.
          ltac1:(autounfold with LTS_get in * ).
          rewrite `(NetMod.get m1 MN1 = _) in *.
          auto.
        }
        assert (m1 = self (next_state s1)); subst.
        {
          consider (m1 = self (MN0 m1)) by consider (KIC MN0).
          replace (self (MN0 m1)) with (self (MN1 m1)) by (consider (KIC MN0); eauto using net_preserve_self, eq_sym with LTS); auto.
          ltac1:(autounfold with LTS_get in * ).
          rewrite `(NetMod.get m1 MN1 = _).
          auto.
        }

        consider (exists MQ1', MQ1 = MQ1' ++ [TrRecv (m0, Q) v]) by (consider (_ =(_)=> _); compat_hsimpl in *; eattac).
        clear - H11 H12 H13 H14 Heqm. (* lock, 2x No____MQ, lock _ = Some _ *)

        unfold hot_of in *.
        ltac1:(autounfold with LTS_get in * ).
        rewrite `(NetMod.get (self (next_state s1)) MN1 = _) in *.
        clear Heqm.

        induction s1; simpl in *.
        1: eattac.

        destruct
          (NameTag_eq_dec to (m0, R)),
          (MProbe_eq_dec msg {| init := self (next_state s1); index := lock_id (next_state s1) |}); subst;
          eauto with LTS.
      }

      econstructor 2. 3: eauto. all: eauto.
      right.
      destruct `(n0 = m0 \/ trans_lock MN1 n0 m0); subst; eauto 4 using dep_reloop, dep_loop, trans_lock_seq1 with LTS.
  Qed.


  Theorem KIC_invariant : trans_invariant KIC always.

  Proof.
    unfold trans_invariant; intros. hsimpl in *.
    rename N0 into MN0.
    rename N1 into MN1.

    assert (well_formed '' MN0) by eauto with LTS.
    assert (well_formed '' MN1) by eauto with LTS.

    assert (forall n, self (MN1 n) = n) as H_self_C1.
    {
      intros.
      consider (KIC MN0).
      replace (self (MN1 n)) with (self (MN0 n)) by eauto using net_preserve_self with LTS.
      auto.
    }

    constructor; auto with LTS; intros.
    - eauto using KIC_invariant_H_lock with LTS.
    - eauto using KIC_invariant_H_wait with LTS.
    - eauto using KIC_invariant_H_alarm, dep_self_deadlocked with LTS.
  Qed.

  Hint Resolve KIC_invariant : LTS inv.
  Hint Extern 0 (KIC _) => solve_invariant : LTS.

  Definition detect_path DS := Forall (fun a : MNAct => exists n : Name, In n DS /\ Flushing_NAct n a).



  Lemma make_ready MN0 n :
    exists mpath MN1,
      (MN0 =[mpath]=> MN1)
      /\ Forall (Flushing_NAct n) mpath
      /\ ready_in n MN1
      /\ forall m MQ M S, NetMod.get m MN0 = mserv MQ M S ->
                    exists MQ' M', NetMod.get m MN1 = mserv (MQ ++ MQ') M' S
                              /\ (n <> m -> M' = M)
                              /\ MQ_Clear MQ'.

  Proof.
    intros.
    unfold ready_in, ready in *.
    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.

    remember ([] : list Event) as MQ0'.
    replace MQ0 with (MQ0 ++ MQ0') by attac.
    assert (MQ_Clear MQ0') by attac.
    clear HeqMQ0'.

    generalize dependent MN0 MQ0 MQ0'.

    induction M0; intros.
    1: exists [], MN0; eattac; exists []; eattac.

    assert (exists MN1 na MQ1',
               (MN0 =(na)=> MN1)
               /\ Flushing_NAct n na
               /\ MQ_Clear MQ0'
               /\ NetMod.get n MN1 = mserv (MQ0 ++ MQ1') M0 S0
               /\ (forall m MQ M S,
                     NetMod.get m MN0 = mserv MQ M S ->
                     exists MQ' M',
                       NetMod.get m MN1 = mserv (MQ ++ MQ') M' S
                       /\ (n <> m -> M' = M)
                       /\ MQ_Clear MQ')).
    {
      clear - Heqm H.
      destruct to as [n' t'].
      pose (NetMod.put n (mserv (MQ0 ++ MQ0') M0 S0) MN0) as MN1'.
      destruct (NetMod.get n' MN1') as [MQ M S] eqn:?.
      exists (NetMod.put n' (mserv (MQ ++ [EvRecv (n, t') msg]) M &S) MN1').
      exists (NComm n n' t' ^ msg).
      smash_eq n n'.
      - exists (MQ0' ++ [EvRecv (n, t') msg]).
        repeat split; compat_hsimpl in |- *; auto.
        + apply NT_Comm with (N0':=MN1'); subst MN1'; attac.
        + subst MN1'.
          rewrite app_assoc.
          eattac.
        + subst MN1'.
          intros.
          hsimpl.
          smash_eq n m; hsimpl in *.
          * exists [EvRecv (n, t') msg]. eexists; eattac.
          * eexists [], _. compat_hsimpl. eattac. (* TODO hsimpl doesn't rewrite app_nil_r? *)
      - exists MQ0'.
        repeat split; hsimpl in |- *; auto.
        + apply NT_Comm with (N0':=MN1'); subst MN1'; attac.
        + subst MN1'. eattac.
        + subst MN1'.
          intros.
          smash_eq_on m n n'; subst; hsimpl in *; hsimpl in |- *.
          * exists [], M0. eattac.
          * exists [EvRecv (n, t') msg], M. eattac.
          * eexists [], _; compat_hsimpl; eattac.
    }
    hsimpl in *.

    assert (exists (mpath : list MNAct) (MN2 : MNet),
               (MN1 =[ mpath ]=> MN2)
               /\ Forall (Flushing_NAct n) mpath
               /\ ready_in n MN2
               /\ (forall m MQ M S,
                      NetMod.get m MN1 = mserv MQ M S ->
                      exists MQ' M',
                        NetMod.get m MN2 = mserv (MQ ++ MQ') M' S
                        /\ (n <> m -> M' = M)
                        /\ MQ_Clear MQ')).
    {
      consider (exists MQ' M',
                   NetMod.get n MN1 = mserv ((MQ0 ++ MQ0') ++ MQ') M' S0
                   /\ (n <> n -> M' = (MSend to msg M0))
                   /\ MQ_Clear MQ').
      eapply IHM0 with (MQ0':=(MQ0' ++ MQ')); eattac.
    }
    compat_hsimpl in *.

    exists (na :: mpath), MN2.
    eattac.

    consider (exists MQ' M',
                 NetMod.get m MN1 = mserv (MQ ++ MQ') M' &S
                 /\ (n <> m -> M' = M)
                 /\ MQ_Clear MQ').

    consider (exists MQnet_deinstr Mnet_deinstr,
                 NetMod.get m MN2 = mserv ((MQ ++ MQ') ++ MQnet_deinstr) Mnet_deinstr &S
                 /\ (n <> m -> Mnet_deinstr = M')
                 /\ MQ_Clear MQnet_deinstr).

    exists (MQ' ++ MQnet_deinstr), Mnet_deinstr.
    smash_eq m n; hsimpl.
    - rewrite app_assoc; attac.
    - rewrite app_assoc; eattac.
      transitivity '(M'); auto.
  Qed.



  Lemma flush_one1 MN0 e MQ0 s S0 n :
    NetMod.get n MN0 = mserv (e :: MQ0) (MRecv s) S0 ->
    exists na MN1 MQ1' S1,
      (MN0 =(na)=> MN1)
      /\ Flushing_NAct n na
      /\ NetMod.get n MN1 = mserv (MQ0 ++ MQ1') (mon_handle e s) S1
      /\ MQ1' = match e with
                | TrSend (m, t) v => if NAME.eqb n m then [TrRecv (n, t) v] else []
                | _ => []
                end
      /\ forall m MQ M S,
        n <> m ->
        NetMod.get m MN0 = mserv MQ M S ->
        exists MQ', NetMod.get m MN1 = mserv (MQ ++ MQ') M S
                    /\ MQ' =
                         match e with
                         | TrSend (m', t) v => if NAME.eqb m' m then [TrRecv (n, t) v] else []
                         | _ => []
                         end.
  Proof.
    intros.

    pose (mon_handle e s) as M1.

    destruct e as [[m t]|[m t]|[m p]] > [smash_eq n m| |]; hsimpl in |- *.
    - pose (NetMod.put n (mserv MQ0 M1 S0) MN0) as MN0'.
      exists (NComm n n &t # v).
      exists (NetMod.put n (mserv (MQ0 ++ [TrRecv (n, &t) v]) M1 S0) MN0').
      exists [TrRecv (n, &t) v].
      exists S0.
      repeat split; intros; auto.
      + apply NT_Comm with (N0':=MN0'); subst MN0' M1; attac.
      + hsimpl in |- *. subst MN0' M1. auto.
      + smash_eq n m; hsimpl in *; doubt.
        subst MN0'.
        hsimpl in |- *.
        exists [].
        eattac.
    - pose (NetMod.put n (mserv MQ0 M1 S0) MN0) as MN0'.
      destruct (NetMod.get m MN0') as [MQm Mm Sm] eqn:?.
      exists (NComm n m &t # v).
      exists (NetMod.put m (mserv (MQm ++ [TrRecv (n, &t) v]) Mm Sm) MN0').
      exists [].
      exists S0.
      repeat split; intros; auto.
      + apply NT_Comm with (N0':=MN0'); subst MN0' M1; attac.
      + hsimpl in |- *. subst MN0' M1. attac.
      + subst MN0'.
        smash_eq_on m0 m n; subst; hsimpl in *; hsimpl in |- *; eexists; eattac.
    - destruct S0 as [I0 P0 O0].
      pose (NetMod.put n (mserv MQ0 M1 (serv (I0 ++ [(m, &t, v)]) P0 O0)) MN0) as MN0'.
      exists (NTau n (MActP (Recv (m, &t) v))).
      exists MN0'.
      exists [].
      exists (serv (I0 ++ [(m, &t, v)]) P0 O0).
      subst MN0' M1; attac.
      constructor. attac. constructor. rewrite H. attac.
      eexists. eattac.
    - pose (NetMod.put n (mserv MQ0 M1 S0) MN0) as MN0'.
      exists (NTau n (MActM Tau)).
      exists MN0'.
      exists [].
      exists S0.
      subst MN0' M1; attac.
      constructor. attac. constructor. rewrite H. attac.
      eexists. eattac.
  Qed.


  Lemma flush_ready_one1 MN0 e MQ0 M0 S0 n :
    NetMod.get n MN0 = mserv (e :: MQ0) M0 S0 ->
    exists mpath MN1 MQ1' M1 S1,
      (MN0 =[mpath]=> MN1)
      /\ Forall (Flushing_NAct n) mpath
      /\ NetMod.get n MN1 = mserv (MQ0 ++ MQ1') M1 S1
      /\ Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ1'
      /\ ((forall t v, e <> TrSend (n, t) v) -> MQ_Clear MQ1')
      /\ forall m MQ M S,
        n <> m ->
        NetMod.get m MN0 = mserv MQ M S ->
        exists MQ', NetMod.get m MN1 = mserv (MQ ++ MQ') M S
                    /\ Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ'
                    /\ ((forall t v, e <> TrSend (m, t) v) -> MQ_Clear MQ').

  Proof.
    intros.

    enough (exists mpath0 MN1,
               (MN0 =[mpath0]=> MN1)
               /\ Forall (Flushing_NAct n) mpath0
               /\ ready_in n MN1
               /\ forall m MQ M S,
                 NetMod.get m MN0 = mserv MQ M S ->
                 exists MQ' M', NetMod.get m MN1 = mserv (MQ ++ MQ') M' S
                                /\ (n <> m -> M' = M)
                                /\ (Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ')
                                /\ ((forall t v, e <> TrSend (m, t) v) -> MQ_Clear MQ')
           ) as Hx.
    {
      hsimpl in Hx.
      consider (exists MQ' M1, NetMod.get n MN1 = mserv ((e :: MQ0) ++ MQ') M1 S0 /\ (n <> n -> M1 = M0)
                               /\ (Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ')
                               /\ ((forall t v, e <> TrSend (n, t) v) -> MQ_Clear MQ')).
      unfold ready_in in *.

      hsimpl in *.

      specialize (flush_one1 MN1 e (MQ0 ++ MQ') s S0 n ltac:(auto)) as Hxx.
      hsimpl in Hxx.

      exists (mpath0 ++ [na]), MN2.
      destruct e as [[n0 t]|?|?] eqn:? > [smash_eq n n0 | |].
      1: (exists (MQ' ++ [TrRecv (n, &t) v])).
      2-4: (exists MQ').
      all: (exists (mon_handle e s ), S1).
      - rewrite app_assoc; attac.
        specialize (Hx2 m MQ M &S ltac:(auto)). hsimpl in Hx2.
        specialize (Hxx3 m (MQ ++ MQ'0) M' &S ltac:(auto) ltac:(auto)).
        hsimpl in Hxx2.
        exists MQ'0.
        replace M with M' by auto.
        eattac.
      - attac.
        specialize (Hx2 m MQ M &S ltac:(auto)). hsimpl in Hx2.
        specialize (Hxx3 m (MQ ++ MQ'0) M' &S ltac:(auto) ltac:(auto)).
        hsimpl in Hxx3.
        replace M with M' by auto.
        exists (MQ'0 ++ if NAME.eqb n0 m then [TrRecv (n, &t) v] else []).
        rewrite app_assoc. ieattac.
        smash_eq n0 m; hsimpl in |- *; attac.
        smash_eq n0 m; attac.
      - attac.
        specialize (Hx2 m MQ M &S ltac:(auto)). hsimpl in Hx2.
        specialize (Hxx3 m (MQ ++ MQ'0) M' &S ltac:(auto) ltac:(auto)).
        hsimpl in Hxx3.
        replace M with M' by auto.
        exists MQ'0.
        eattac.
      - attac.
        specialize (Hx2 m0 MQ M &S ltac:(auto)). hsimpl in Hx2.
        specialize (Hxx3 m0 (MQ ++ MQ'0) M' &S ltac:(auto) ltac:(auto)).
        hsimpl in Hxx3.
        replace M with M' by auto.
        exists MQ'0.
        eattac.
    }

    specialize (make_ready MN0 n) as ?.
    hsimpl in *.
    exists mpath, MN1.
    eattac.

    consider (exists (MQ' : list Event) M', NetMod.get m MN1 = mserv (MQ ++ MQ') M' &S /\ (n <> m -> M' = M) /\ MQ_Clear MQ').
    eexists MQ', M'.
    eattac.
  Qed.


  Lemma flush_one_w_sends MN0 n :
    exists mpath MN1,
      (MN0 =[mpath]=> MN1)
      /\ Forall (Flushing_NAct n) mpath
      /\ no_sends_in n MN1
      /\ forall m MQ M S,
        n <> m ->
        NetMod.get m MN0 = mserv MQ M S ->
        exists MQ', NetMod.get m MN1 = mserv (MQ ++ MQ') M S
                    /\ Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ'.

  Proof.
    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.

    remember ([] : list Event) as MQ0'.
    replace MQ0 with (MQ0 ++ MQ0') by attac.
    assert (Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ0') by attac.
    clear HeqMQ0'.

    generalize dependent MN0 MQ0' M0 S0.
    induction MQ0; intros.
    {
      unfold no_sends_in, NoTrSend, flushed_in, Flushed in *.
      exists [], MN0.
      hsimpl in *. hsimpl in |- *.
      eattac.
      exists []. eattac.
    }

    specialize (flush_ready_one1 MN0 a (MQ0 ++ MQ0') M0 S0 n ltac:(auto)) as ?.
    hsimpl in *.

    normalize_hyp @IHMQ0.
    specialize (IHMQ0 S1 M1 (MQ0' ++ MQ1') MN1).
    rewrite app_assoc in IHMQ0.
    specialize (IHMQ0 ltac:(attac) ltac:(attac)).
    hsimpl in IHMQ0.

    exists (mpath ++ mpath0), MN2.
    eattac.

    specialize (H5 m MQ M &S ltac:(auto) ltac:(auto)).
    hsimpl in H5.

    specialize (IHMQ3 m (MQ ++ MQ') M &S ltac:(auto) ltac:(auto)).
    hsimpl in IHMQ3.

    exists (MQ' ++ MQ'0).

    rewrite app_assoc; eattac.
  Qed.


  Lemma flush_one_wo_sends MN0 n :
    no_sends_in n MN0 ->
    exists mpath MN1,
      (MN0 =[mpath]=> MN1)
      /\ Forall (Flushing_NAct n) mpath
      /\ flushed_in n MN1
      /\ forall m MQ M S,
        n <> m ->
        NetMod.get m MN0 = mserv MQ M S ->
        exists MQ', NetMod.get m MN1 = mserv (MQ ++ MQ') M S
                    /\ MQ_Clear MQ'.

  Proof.
    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.

    remember ([] : list Event) as MQ0'.
    replace MQ0 with (MQ0 ++ MQ0') by attac.
    assert (MQ_Clear MQ0') by attac.
    clear HeqMQ0'.

    generalize dependent MN0 MQ0' M0 S0.
    induction MQ0; intros.
    {
      unfold no_sends_in, NoTrSend, flushed_in, Flushed in *.
      exists [], MN0.
      hsimpl in *. hsimpl in |- *.
      eattac.
      exists []. eattac.
    }

    specialize (flush_ready_one1 MN0 a (MQ0 ++ MQ0') M0 S0 n ltac:(auto)) as ?.
    hsimpl in *.

    normalize_hyp @IHMQ0.
    specialize (IHMQ0 S1 M1 (MQ0' ++ MQ1') MN1).

    assert (MQ_Clear (MQ0' ++ MQ1')).
    {
      enough (forall (t : Tag) v, a <> TrSend (n, t) v) by attac.
      intros.
      unfold no_sends_in, NoTrSend in *.
      rewrite Heqm in H0.
      destruct a; attac.
    }

    assert (no_sends_in n MN1) by (unfold no_sends_in, NoTrSend in *; attac).

    rewrite app_assoc in IHMQ0.
    specialize (IHMQ0 ltac:(attac)).
    specialize (IHMQ0 ltac:(attac)).
    specialize (IHMQ0 ltac:(attac)).
    hsimpl in *.

    exists (mpath ++ mpath0), MN2.
    eattac.

    specialize (H6 m MQ M &S ltac:(auto) ltac:(auto)).
    hsimpl in H6.

    specialize (IHMQ3 m (MQ ++ MQ') M &S ltac:(auto) ltac:(auto)).
    hsimpl in IHMQ3.

    assert (MQ_Clear (MQ' ++ MQ'0)).
    {
      enough (forall (t : Tag) v, a <> TrSend (m, t) v) by attac.
      intros.
      unfold no_sends_in, NoTrSend in *.
      rewrite Heqm in H0.
      destruct a; attac.
    }

    exists (MQ' ++ MQ'0).

    rewrite app_assoc; eattac.
  Qed.


  Lemma flush_one MN0 n :
    exists mpath MN1,
      (MN0 =[mpath]=> MN1)
      /\ Forall (Flushing_NAct n) mpath
      /\ no_sends_in n MN1
      /\ (no_sends_in n MN0 -> flushed_in n MN1)
      /\ forall m MQ M S,
        n <> m ->
        NetMod.get m MN0 = mserv MQ M S ->
        exists MQ', NetMod.get m MN1 = mserv (MQ ++ MQ') M S
                    /\ Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ'
                    /\ (no_sends_in n MN0 -> MQ_Clear MQ').

  Proof.
    assert (no_sends_in n MN0 \/ ~ no_sends_in n MN0) as [? | ?].
    {
      unfold no_sends_in, NoTrSend.
      destruct (NetMod.get n MN0) as [MQ0 _ _].
      induction MQ0; attac.
      destruct a.
      - right. eattac.
      - destruct IHMQ0. eattac. right. intros ?. eattac.
      - destruct IHMQ0. eattac. right. intros ?. eattac.
    }
    - specialize (flush_one_wo_sends MN0 n ltac:(auto)) as ?.
      hsimpl in *.
      exists mpath, MN1.
      eattac.
      consider (exists MQ', NetMod.get m MN1 = mserv (MQ ++ MQ') M &S /\ MQ_Clear MQ').
      eexists; eattac.
    - specialize (flush_one_w_sends MN0 n) as ?.
      hsimpl in *.
      exists mpath, MN1.
      eattac.
      consider (exists MQ' : list Event,
                   NetMod.get m MN1 = mserv (MQ ++ MQ') M &S /\
                     Forall (fun e : Event => match e with
                                              | TrSend _ _ => False
                                              | _ => True
                                              end) MQ').
      eexists; eattac.
  Qed.


  Lemma flush_one_until [MN0 : MNet] [n MQ00 MQ01] :
    mserv_i (MN0 n) = MQ00 ++ MQ01 ->
    exists MQ1' M1 S1 mpath MN1,
      (MN0 =[mpath]=> MN1)
      /\ Forall (Flushing_NAct n) mpath
      /\ NetMod.get n MN1 = mserv (MQ01 ++ MQ1') M1 S1
      /\ ready M1
      /\ Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ1'
      /\ (Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ00 -> MQ_Clear MQ1')
      /\ forall m MQ M S,
        n <> m ->
        NetMod.get m MN0 = mserv MQ M S ->
        exists MQ', NetMod.get m MN1 = mserv (MQ ++ MQ') M S
                    /\ Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ'
                    /\ (Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ00 -> MQ_Clear MQ').

  Proof.
    intros.
    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.
    subst.

    remember ([] : list Event) as MQ0'.
    replace MQ01 with (MQ01 ++ MQ0') by attac.
    assert (Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ0') by attac.
    clear HeqMQ0'.
    unfold NetGet in *.
    hsimpl in H.

    generalize dependent MN0 MQ0' M0 S0.
    induction MQ00; intros.
    {
      specialize (make_ready MN0 n) as ?.
      hsimpl in *.
      unfold NetGet in *.
      consider (exists (MQ1' : list Event) (M1 : MProc),
                   NetMod.get n MN1 = mserv ((MQ01 ++ MQ0') ++ MQ1') M1 S0 /\ (n <> n -> M1 = M0) /\ MQ_Clear MQ1').
      simpl in *.
      eapply H3 in Heqm. attac.
      exists MQ', M', S0.
      exists mpath, MN1.

      assert (ready M') by (unfold ready_in in *; attac).

      eattac.

      consider (exists (MQ' : list Event) (M' : MProc), NetMod.get m MN1 = mserv (MQ ++ MQ') M' &S /\ (n <> m -> M' = M) /\ MQ_Clear MQ').
      exists MQ'0.
      replace M with M' by auto.
      eattac.
    }

    specialize (flush_ready_one1 MN0 a (MQ00 ++ MQ01 ++ MQ0') M0 S0 n ltac:(auto)) as ?.
    hsimpl in H.

    normalize_hyp @IHMQ00.
    specialize (IHMQ00 S1 M1 (MQ0' ++ MQ1') MN1).
    repeat (rewrite app_assoc in * ).

    specialize (IHMQ00 ltac:(attac)).
    specialize (IHMQ00 ltac:(attac)).
    hsimpl in IHMQ00.

    exists (MQ1' ++ MQ1'0), (MRecv s ), S2.
    exists (mpath ++ mpath0), MN2.
    rewrite app_assoc; eattac.
    1: destruct a; attac.

    specialize (H5 m MQ M &S ltac:(auto) ltac:(auto)). hsimpl in H5.
    specialize (IHMQ06 m (MQ ++ MQ') M &S ltac:(auto) ltac:(auto)). hsimpl in IHMQ06.

    exists (MQ' ++ MQ'0).
    rewrite app_assoc; eattac.

    destruct a; attac.
  Qed.


  Lemma flush_one_In [MN0 : MNet] [n e] :
    List.In e (mserv_i (MN0 n)) ->
    exists MQ00 MQ01 MQ1' M1 S1 mpath MN1,
      (mserv_i (MN0 n)) = MQ00 ++ e :: MQ01
      /\ (MN0 =[mpath]=> MN1)
      /\ Forall (Flushing_NAct n) mpath
      /\ NetMod.get n MN1 = mserv (e :: MQ01 ++ MQ1') M1 S1
      /\ ready M1
      /\ Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ1'
      /\ (Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ00 -> MQ_Clear MQ1')
      /\ forall m MQ M S,
        n <> m ->
        NetMod.get m MN0 = mserv MQ M S ->
        exists MQ', NetMod.get m MN1 = mserv (MQ ++ MQ') M S
                    /\ Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ'
                    /\ (Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ00 -> MQ_Clear MQ').

  Proof.
    intros HIn.
    apply in_split in HIn as (MQ00 & MQ01 & ?).
    hsimpl in *.
    exists MQ00, MQ01.
    specialize (flush_one_until H) as ?.
    hsimpl in *.
    eexists _, _, _, _, _. eattac.
  Qed.


  Lemma detect_path_incl : forall DS0 DS1 mpath,
      incl DS0 DS1 ->
      detect_path DS0 mpath ->
      detect_path DS1 mpath.

  Proof.
    unfold detect_path.
    intros.
    induction mpath; attac.
  Qed.
  #[export] Hint Resolve detect_path_incl : LTS.

  Lemma detect_path_cons : forall DS n a mpath,
      In n DS ->
      Flushing_NAct n a ->
      detect_path DS mpath ->
      detect_path DS (a :: mpath).

  Proof.
    unfold detect_path.
    intros.
    induction mpath; attac.
  Qed.

  Lemma detect_path_app : forall DS mpath0 mpath1,
      detect_path DS mpath0 ->
      detect_path DS mpath1 ->
      detect_path DS (mpath0 ++ mpath1).

  Proof.
    unfold detect_path.
    intros.
    induction mpath0; attac.
  Qed.
  #[export] Hint Resolve detect_path_app detect_path_cons : LTS.

  Lemma detect_path1 : forall n mpath, Forall (Flushing_NAct n) mpath -> detect_path [n] mpath.

  Proof.
    intros.
    unfold detect_path.
    induction mpath; eattac.
  Qed.

  #[export] Hint Resolve detect_path1 : LTS.


  Lemma propagation_init [MN0 : MNet] [n n' m] [v ] :
    well_formed '' MN0 ->
    KIC MN0 ->
    deadlocked n '' MN0 ->
    lock MN0 n n' ->
    List.In (TrRecv (m, Q) v) (mserv_i (MN0 n)) ->
    exists MN1 mpath MQ,
      (MN0 =[mpath]=> MN1)
      /\ detect_path [n] mpath
      /\ mserv_i (MN1 m) = MQ ++ [hot_ev_of MN1 n n].

  Proof.
    intros.

    assert (exists mpath0 MN1 MQ1 s S1,
               (MN0 =[mpath0]=> MN1)
               /\ Forall (Flushing_NAct n) mpath0
               /\ NetMod.get n MN1 = mserv (TrRecv (m, Q) v :: MQ1) ((MRecv s)) S1
           ) as Hxx'.
    {
      specialize (flush_one_In ltac:(eauto)) as ?.
      hsimpl in *.
      exists mpath, MN1, (MQ01 ++ MQ1'), s, S1.
      attac.
    }
    hsimpl in Hxx'.

    assert (exists mpath1 MN2 M2 S2,
               (MN1 =[mpath1]=> MN2)
               /\ Forall (Flushing_NAct n) mpath1
               /\ NetMod.get n MN2 = mserv MQ1 (MSend (m, R) (hot_of MN2 n) M2) S2
           ) as Hx.
    {

      destruct S1 as [I1 P1 O1].
      pose (serv (I1 ++ [(m, Q, v)]) P1 O1) as S2.
      pose  {|self := self s
            ; lock_id := lock_id s
            ; lock := lock s
            ; wait := m :: wait s
            ; alarm := alarm s
            |} as s1.
      pose (NetMod.put n (mserv MQ1 (mon_handle (TrRecv (m, Q) v) s ) S2) MN1) as MN1'.

      exists [NTau n (MActP (Recv (m, Q) v))], MN1', (MRecv s1), S2.

      destruct s.
      subst MN1' s1 S2.

      assert (lock0 <> None).
      {
        consider (KIC MN1) by eauto with LTS.
        consider (exists path, '' MN0 =[path]=> '' MN1) by eauto using transp_sound with LTS.
        assert (lock MN1 n n') by eauto with LTS.
        specialize (H_lock_C n n' ltac:(auto)).
        ltac1:(autounfold with LTS_get in H_lock_C).
        rewrite `(NetMod.get n MN1 = _) in H_lock_C.
        simpl in *.
        bs.
      }
      assert (n = self0).
      {
        consider (KIC MN1) by eauto with LTS.
        specialize (H_self_C n).
        ltac1:(autounfold with LTS_get in H_self_C).
        rewrite `(NetMod.get n MN1 = _) in H_self_C.
        auto.
      }

      destruct lock0. 2: bs.
      subst.

      attac.
      - hsimpl in |- *.
        apply path_seq0.
        constructor. constructor. attac.
      - constructor; eattac.
      - unfold hot_of, NetGet.
        hsimpl in *.
        attac.
    }
    hsimpl in Hx.

    assert (exists MN3 MQ, (MN2 =(NComm n m R (MValM (hot_of MN2 n)))=> MN3) /\ mserv_i (MN3 m) = MQ ++ [hot_ev_of MN3 n n])
      as Hxx.
    {
      pose (NetMod.put n (mserv MQ1 (M2) S2) MN2) as MN2'.
      destruct (NetMod.get m MN2') as [MQm Mm Sm] eqn:?.
      exists (NetMod.put m (mserv (MQm ++ [hot_ev_of MN2 n n]) Mm Sm) MN2'), MQm.

      subst MN2'.
      split.
      - econstructor; eattac.
      - unfold NetGet, hot_ev_of, hot_of, NetGet.
        smash_eq n m; attac.
    }
    hsimpl in Hxx.

    exists MN3, (mpath0 ++ mpath1 ++ [(NComm n m R (MValM (hot_of MN2 n)))]).

    hsimpl in *.
    exists MQ.
    repeat split; eauto with LTS.
    eapply detect_path_app; eauto with LTS.
    eapply detect_path_app; eauto with LTS.
    eapply detect_path1; constructor; attac.
  Qed.


  Lemma sends_probe_send [MN0 : MNet] [n m p] :
    lock MN0 n m ->
    KIC MN0 ->
    deadlocked m '' MN0 ->
    sends_probe (n, R) p (NetMod.get m MN0) ->
    hot MN0 p (init p) ->
    exists MN1 mpath MQn',
      (MN0 =[mpath]=> MN1)
      /\ detect_path [m] mpath
      /\ ((alarm (MN1 m) = true /\ m = init p) \/ (mserv_i (MN1 n) = MQn' ++ [EvRecv (m, R) p])).

  Proof. (* TODO adjust hint cost!!! Use Cut!!! *)
    intros Himlazy.
    intros.
    assert (well_formed '' MN0) by eauto with LTS.
    destruct (NetMod.get m MN0) as [MQ c S] eqn:?.
    generalize dependent MN0 MQ n p.

    induction c; intros.
    - consider (sends_probe _ _ _).
      + consider (exists m', lock MN0 m m') by eauto using deadlocked_M_get_lock with LTS.
        consider (exists (MN1 : MNet) mpath MQ,
                     (MN0 =[mpath]=> MN1)
                     /\ detect_path [m] mpath
                     /\ mserv_i (MN1 n) = MQ ++ [hot_ev_of MN1 m m])
          by (eapply propagation_init; eauto;
              unfold NetGet in *; ltac1:(autounfold with LTS_get in * ); rewrite Heqm0; attac).

        assert (self state = m).
        {
          consider (KIC MN0).
          specialize (H_self_C m).
          clear - H_self_C Heqm0.
          ltac1:(autounfold with LTS_get in * ); attac.
        }
        assert (hot MN1 p (init p))
          by (destruct p; simpl in *; subst; eauto 3 using deadlocked_preserve_hot_probe  with LTS).
        assert (p = hot_of MN1 m)
          by (destruct p; simpl in *; subst; auto using hot_of_hot).

        exists MN1, mpath, MQ.
        unfold hot_ev_of in *.
        attac.

      + assert (mserv_i (MN0 m) = MQ0 ++ EvRecv (n', R) p :: MQ') as Hget0
            by (clear - Heqm0; ltac1:(autounfold with LTS_get in * ); eattac).

        specialize (flush_one_until Hget0) as (MQ1' & M1 & S1 & mpath0 & MN1 & ?).
        hsimpl in *. clear Hget_0.
        assert (MQ_Clear MQ1') by auto. clear H11 H12. (* NoSends, _ -> MQ_clear MQ1' *)

        assert (lock_id (MN0 m) = lock_id (MN1 m)) by eauto using deadlocked_preserve_M_lock_id with LTS.
        assert (lock (MN0 m) = lock (MN1 m)) by eauto using deadlocked_preserve_M_lock with LTS.
        assert (self (MN1 m) = m) by consider (KIC MN1).

        assert (List.In n (wait (MN1 m))).
        {
          destruct `(List.In n (wait state) \/ _).
          - eapply deadlocked_preserve_M_in_wait; eauto with LTS.
            ltac1:(autounfold with LTS_get).
            rewrite `(NetMod.get m MN0 = _).
            auto.
          - hsimpl in H8.

            assert (lock MN1 n m) by
              (consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS;
               eauto 10 with LTS).
            enough (NoRecvQ_from n (mserv_i (MN1 m))) by (consider (KIC MN1)).
            enough (NoRecvQ_from n MQ').
            {
              ltac1:(autounfold with LTS_get in * ).
              rewrite `(NetMod.get m MN1 = _).
              intros ? Hx.
              kill Hx.
              apply in_app_or in H18 as [|].
              1: specialize (H17 v0); bs.
              attac.
              (* clear - H17 H10. *)
              unfold MQ_Clear in *.
              eapply Forall_forall in H13; eauto. eauto.
            }

            clear - Heqm0 H8 H.
            intros ? ?.
            destruct (NetMod.get m '' MN0) as [I0 P0 O0] eqn:?.
            assert (exists I00 I01, I0 = I00 ++ I01 /\ List.In (n, Q, v) I00 /\ List.In (n, Q, v0) I01).
            {
              unfold net_deinstr, deinstr in *.
              compat_hsimpl in *.
              destruct S.
              hsimpl in *.
              assert (List.In (n, Q, v) (MQ_r MQ0)) by eauto with LTS.
              assert (List.In (n, Q, v0) (MQ_r MQ')) by eauto with LTS.
              exists (serv_i0 ++ MQ_r MQ0), (MQ_r MQ'). eattac.
            }

            hsimpl in *.

            consider (well_formed '' MN0).
            specialize (H_wf_SRPC m) as [srpc Hsrpc].
            destruct Hsrpc.
            hsimpl in *.

            consider (exists v' I00', Deq (n, Q) v' I00 I00') by eauto using In_Deq.

            assert (Deq (n, Q) v' (I00 ++ I01) (I00' ++ I01)) by eauto with LTS.

            absurd (List.In (n, Q, v0) (I00' ++ I01)); attac.
        }

        pose (NetMod.put m (mserv (MQ' ++ MQ1') (mon_handle (EvRecv (n', R) p) s) S1) MN1) as MN2.
        assert (exists na, (MN1 =(na)=> MN2) /\ Flushing_NAct m na).
        {
          eexists (NTau m (MActM Tau)).
          subst MN2.
          clear - H10. (* get m *)
          split.
          constructor; attac. (* TODO why constructor? *)
          attac.
        }

        (* TODO abstract out *)
        assert (hot MN1 p (init p)).
        {
          split; auto.
          consider (hot MN0 p _).
          destruct p. simpl in *.
          clear - Heqm0 H14 H9 H11 H19. (* get m, forall, of_lock_id, index0 = *)
          smash_eq m init0; hsimpl in *.
          unfold hot in *.
          ltac1:(autounfold with LTS_get in * ).
          destruct (NetMod.get init0 MN0) as [MQi Mi Si] eqn:?.
          specialize (H14 init0 MQi Mi Si ltac:(auto) ltac:(auto)).
          attac.
        }

        destruct s, p. simpl in *.
        assert (lock0 = Some n').
        {
          ltac1:(autounfold with LTS_get in * ).
          rewrite `(NetMod.get m MN0 = _) in *.
          rewrite `(NetMod.get m MN1 = _) in *.
          hsimpl in *.
          auto.
        } subst.

        assert (self0 = m).
        {
          ltac1:(autounfold with LTS_get in * ).
          rewrite `(NetMod.get m MN1 = _) in *.
          now hsimpl in *.
        } subst.

        assert (List.In n (wait0)).
        {
          ltac1:(autounfold with LTS_get in * ).
          rewrite `(NetMod.get m MN1 = _) in *.
          now hsimpl in *.
        } subst.

        hsimpl in *.

        smash_eq m init0.
        * destruct (PeanoNat.Nat.eq_dec lock_id0 index0).
          -- subst.
             exists MN2, (mpath0 ++ [na]), [].
             unfold NetGet.
             subst MN2.
             compat_hsimpl in *.
             ltac1:(replace (index0 =? index0) with true in * by auto using eq_sym, PeanoNat.Nat.eqb_refl).
             compat_hsimpl.
             attac.
          -- exfalso.
             unfold hot, NetGet in *.
             hsimpl in *.
             bs.

        * enough (exists MN3 mpath1 MQn',
                     (MN2 =[ mpath1 ]=> MN3)
                     /\ detect_path [m] mpath1
                     /\ mserv_i (MN3 n) = MQn' ++ [EvRecv (m, R) {| init := init0; index := index0 |}]).
          {
            hsimpl in *.

            exists MN3, (mpath0 ++ [na] ++ mpath1), MQn'.
            ltac1:(autounfold with LTS_get in * ).
            destruct (NetMod.get n MN3) as [MQn3 Mn3 Sn3] eqn:?.
            destruct (NetMod.get n MN0) as [MQn0 Mn0 Sn0] eqn:?.
            subst.

            eattac.
          }

          subst MN2.
          unfold NetGet.
          simpl in *.

          hsimpl in *.
          ltac1:(replace (NAME.eqb init0 m) with false in * by eauto using eq_sym, NAME_H.neq_neqb_inv).
          hsimpl in |- *.

          clear - H17 H19. (* trans, List.In n wait0 *)
          remember ((MRecv
                       {|
                         self := m;
                         lock_id := lock_id0;
                         lock := Some n';
                         wait := wait0;
                         alarm := alarm0
                       |})) as M.

          change  Que.Channel.Name with Mon.Proc.Que.Channel.Name in *.
          change  Conf.NAME.t' with Mon.Proc.Que.Channel.Name in *.
          rewrite <- HeqM in *.
          clear HeqM.

          remember {| init := init0; index := index0 |} as p.
          clear Heqp.
          remember (MQ' ++ MQ1') as MQ''. clear HeqMQ'' MQ'. rename MQ'' into MQ'.
          clear - wait0 H19.
          generalize dependent MN1 MQ'.
          induction wait0; intros.
          1: bs.
          simpl in *.

          assert (exists MQ3 MN2 MQn',
                     (NetMod.put m (mserv MQ' (MSend_all (a :: wait0) R p M ) S1) MN1
                      =(NComm m a R ^ p)=>
                        (NetMod.put m (mserv MQ3 (MSend_all wait0 R p M ) S1) MN2)
                     )
                     /\ (mserv_i ((NetMod.put m (mserv MQ3 (MSend_all wait0 R p M ) S1) MN2) a)) = MQn' ++ [EvRecv (m, R) p]
                 ).
          {
            smash_eq m a.
            - exists (MQ' ++ [EvRecv (m, R) p]), (NetMod.put m (mserv MQ' (MSend_all wait0 R p M ) S1) MN1), MQ'.
              split.
              eapply NTrans_Comm_eq_inv; eattac. eattac.
              unfold NetGet. attac.

            - destruct (NetMod.get a MN1) as [MQa Ma Sa] eqn:?.
              pose (mserv MQ' (MSend_all wait0 R p M ) S1) as MSm.
              pose (mserv (MQa ++ [EvRecv (m, R) p]) Ma Sa) as MSa.

              exists MQ'.
              exists (NetMod.put a MSa MN1).
              exists MQa.
              split.
              eapply NTrans_Comm_neq_inv. eattac.
              exists MSm, MSa.
              rewrite NetMod.put_put_neq; subst MSm MSa; compat_hsimpl; eattac.
              ltac1:(autounfold with LTS_get).
              eattac.
          }
          hsimpl in *.

          smash_eq n a.
          {
            eexists (NetMod.put m
                       (mserv MQ3 (MSend_all wait0 R p M ) S1) MN2) ,_,MQn'.
            unfold NetGet in *.
            repeat split.
            eattac.
            2: eattac.
            simpl.
            apply detect_path1.
            attac.
          }

          destruct `(a = n \/ List.In n wait0); doubt.

          specialize (IHwait0 ltac:(auto) MQ3 ((NetMod.put m (mserv MQ3 (MSend_all wait0 R p M ) S1) MN2))).
          hsimpl in IHwait0.

          exists MN3, (NComm m a R ^ p :: mpath1).
          eexists.
          repeat split.
          eattac.
          2: eattac.
          eapply detect_path_cons; attac.

    - destruct to as [to t'].
      assert (exists MN1, MN0 =(NComm m to t' (MValM msg))=> MN1) as [MN1 ?].
      {
        assert (exists MS1, NetMod.get m MN0 =(send (to, t') (MValM msg))=> MS1)
          as [MS ?] by eattac.
        eauto using send_comm_available.
      }
      assert (deadlocked m '' MN1).
      {
        consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS.
        eauto with LTS.
      }
      assert (exists MQ1, NetMod.get m MN1 = mserv (MQ ++ MQ1) (c ) &S) as [MQ1 ?].
      {
        kill H4; hsimpl in *.
        smash_eq m to.
        - exists [EvRecv (m, t') msg]. destruct M; attac.
        - exists []. destruct M1; attac.
      }

      consider (sends_probe (n, R) p (mserv MQ (MSend (to, t') msg c ) &S)).
      + eexists MN1, [NComm m to R ^ msg].
        have (MN0 =( NComm m to R ^ msg )=> MN1).
        kill H4. hsimpl in *.
        unfold NetGet.
        exists MQ0.
        hsimpl in |- *.
        repeat split.
        3: attac.
        2: apply detect_path1; constructor; attac.
        eattac.
      + have (well_formed '' MN1) by eauto with LTS.

        assert (sends_probe (n, R) p (mserv (MQ ++ MQ1) (c ) &S))
          by auto using sends_probe_extend_r with LTS.

        assert (hot MN1 p (init p)).
        {
          split; auto.
          destruct p.
          smash_eq m init0; hsimpl in *; hsimpl in |- *.
          - assert (lock_id (MN0 m) = lock_id (MN1 m))
              by eauto using deadlocked_preserve_M_lock_id with LTS.
            rewrite <- `(lock_id (MN0 m) = _).
            unfold hot in *.
            ltac1:(autounfold with LTS_get in * ).
            rewrite `(NetMod.get m MN0 = _) in *.
            hsimpl in *.
            auto.
          - unfold hot in *.
            ltac1:(autounfold with LTS_get in * ).
            smash_eq init0 to.
            + hsimpl in *.
              auto.
            + enough (NetMod.get init0 MN0 = NetMod.get init0 MN1) as Hx by (rewrite <- Hx; attac).
              eapply act_particip_stay; eauto.
              simpl; attac.
        }

        consider (exists (MN2 : MNet) (mpath : list MNAct) MQn',
                     (MN1 =[ mpath ]=> MN2)
                     /\ detect_path [m] mpath
                     /\ ((alarm (MN2 m) = true /\ m = init p)
                         \/ mserv_i (MN2 n) = MQn' ++ [EvRecv (m, R) p])
                 ) by
          re_have (
              consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound1;
              apply IHc with (MQ:=MQ ++ MQ1); eauto 15 with LTS
            ).

        eexists MN2, _, MQn'.

        repeat split.
        3: eattac.
        eattac.
        simpl.
        eapply detect_path_cons; eattac.
  Qed.


  Lemma detection_finito [MN0 : MNet] [n m] :
    KIC MN0 ->
    deadlocked n '' MN0 ->
    lock MN0 n m ->
    List.In (hot_ev_of MN0 m n) (mserv_i (MN0 n)) ->
    exists MN1 mpath,
      (MN0 =[mpath]=> MN1)
      /\ detect_path [n] mpath
      /\ alarm (MN1 n) = true.

  Proof.
    intros.
    assert (well_formed '' MN0) by eauto with LTS.
    assert (lock (MN0 n) = Some m) by eauto with LTS.

    assert (exists mpath0 MN1 MQ1 s S1,
               (MN0 =[mpath0]=> MN1)
               /\ detect_path [n] mpath0
               /\ NetMod.get n MN1 = mserv (hot_ev_of MN0 m n :: MQ1) ((MRecv s)) S1
           ).
    {
      specialize (flush_one_In ltac:(eauto)) as ?.
      hsimpl in *.
      exists mpath, MN1, (MQ01 ++ MQ1'), s, S1.
      attac.
    }
    hsimpl in *.

    enough (exists na MN2, (MN1 =(na)=> MN2) /\ Flushing_NAct n na /\ alarm (MN2 n) = true)
      by (hsimpl in *; exists MN2, (mpath0 ++ [na]); eattac).

    exists (NTau n (MActM Tau)).
    eexists.

    assert (lock (MN1 n) = Some m).
    {
      consider (KIC MN1).
      apply H_lock_C.
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound.
      eauto with LTS.
    }

    assert (hot_ev_of MN1 m n = hot_ev_of MN0 m n).
    {
      unfold hot_ev_of, hot_of in *.
      replace (lock_id (MN1 n)) with (lock_id (MN0 n)); auto.
      eauto using deadlocked_preserve_M_lock_id with LTS.
    }
    rewrite <- `(hot_ev_of MN1 m n = hot_ev_of MN0 m n) in *.

    assert (self (MN1 n) = n) by consider (KIC MN1).

    split.
    - ltac1:(autounfold with LTS_get in * ). hsimpl in |- *.
      constructor. constructor. constructor.
      destruct s.
      rewrite `(NetMod.get n MN1 = _). constructor.
      constructor.
    - unfold hot_of in *.
      ltac1:(autounfold with LTS_get in * ). hsimpl in |- *.
      destruct s.
      rewrite `(NetMod.get n MN1 = _) in *.
      simpl in *.
      subst.
      hsimpl in |- *.
      rewrite (PeanoNat.Nat.eqb_refl).
      attac.
  Qed.


  (** If you receive a hot probe, you either propagate or alarm  *)
  Lemma in_sends_probe [MN0 n' n m p MQ] :
    KIC MN0 ->
    lock MN0 n' n ->
    lock MN0 n m ->
    deadlocked m '' MN0 ->
    hot MN0 p (init p) ->
    mserv_i (MN0 n) = MQ ++ [EvRecv (m, R) p] ->
    exists MN1 mpath, (MN0 =[mpath]=> MN1)
                 /\ detect_path [n] mpath
                 /\ ((alarm (MN1 n) = true /\ n = init p) \/ sends_probe (n', R) p (NetMod.get n MN1)).

  Proof.
    intros.
    assert (well_formed '' MN0) by eauto with LTS.

    destruct p.
    smash_eq n init0.
    2: exists MN0, []; attac; eauto using sends_probe_prop_foreign.

    simpl in *.
    consider (exists MN1 mpath0, (MN0 =[mpath0]=> MN1) /\ detect_path [n] mpath0 /\ alarm (MN1 n) = true).
    {
      eapply detection_finito; eauto 15 with LTS.
      unfold hot_ev_of.
      replace (hot_of MN0 n) with {| init := n; index := index0 |} by eauto using hot_of_hot.
      rewrite `(mserv_i (_ _) = _). attac.
    }

    exists MN1, mpath0.
    eattac.
  Qed.


  Lemma deadlocked_lock_chain_invariant1 [N0 N1 : PNet] [L] [n0 n1 : Name] [a] :
    (N0 =(a)=> N1) ->
    deadlocked n0 N0 ->
    lock_chain N0 n0 L n1 ->
    lock_chain N1 n0 L n1.

  Proof.
    intros.
    have (deadlocked n0 N1).
    enough (lock_chain N1 n0 L n1) by attac.
    hsimpl in *.
    generalize dependent N0 N1 n0 n1 L.
    induction L; intros; hsimpl in *; eauto with LTS.

    constructor; eauto with LTS.

    have (deadlocked a0 N1).

    normalize_hyp @IHL.
    specialize (IHL n1 a0 N1 N0).
    apply IHL; eauto with LTS.
  Qed.

  (* Hint Resolve  deadlocked_lock_chain_invariant1 | 0 : LTS. *)


  Lemma deadlocked_lock_chain_invariant [N0 N1 : PNet] [L] [n0 n1 : Name] [mpath] :
    (N0 =[mpath]=> N1) ->
    deadlocked n0 N0 ->
    lock_chain N0 n0 L n1 ->
    lock_chain N1 n0 L n1.

  Proof.
    generalize dependent N0.
    induction mpath; intros; hsimpl in *. 1: attac.
    assert (trans_lock N2 n0 n1) by attac.
    eapply (IHmpath N2); eauto using deadlocked_lock_chain_invariant1 with LTS.
  Qed.

  #[export] Hint Resolve deadlocked_lock_chain_invariant | 0 : LTS.


  Lemma propagation1 [MN0 n' n m p] :
    KIC MN0 ->
    lock MN0 n' n ->
    lock MN0 n m ->
    deadlocked m '' MN0 ->
    sends_probe (n, R) p (NetMod.get m MN0) ->
    hot MN0 p (init p) ->
    deadlocked (init p) '' MN0 ->
    exists MN1 mpath,
      (MN0 =[mpath]=> MN1)
      /\ detect_path [n; m] mpath
      /\ (  (alarm (MN1 n) = true /\ n = init p)
         \/ (alarm (MN1 m) = true /\ m = init p)
         \/ sends_probe (n', R) p (NetMod.get n MN1)).
  Proof.
    intros.
    assert (well_formed '' MN0) by eauto with LTS.

    consider (exists MN1 mpath0 MQn',
                 (MN0 =[mpath0]=> MN1)
                 /\ detect_path [m] mpath0
                 /\ ((alarm (MN1 m) = true /\ m = init p) \/ (mserv_i (MN1 n) = MQn' ++ [EvRecv (m, R) p])))
      by eauto using sends_probe_send.

    destruct `((alarm (MN1 m) = true /\ _) \/ mserv_i (MN1 n) = MQn' ++ [EvRecv (m, R) p]) as [|].
    1: eattac.

    consider ( exists MN2 mpath1, (MN1 =[mpath1]=> MN2)
                             /\ detect_path [n] mpath1
                             /\ ((alarm (MN2 n) = true /\ n = init p) \/ sends_probe (n', R) p (NetMod.get n MN2))).
    {
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound.
      assert (deadlocked n '' MN0) by (eauto using deadlocked_dep' with LTS).
      assert (deadlocked n' '' MN0) by eauto using deadlocked_dep' with LTS.
      assert (lock MN1 n m) by eauto 3 with LTS.
      eapply in_sends_probe; eauto 5 using deadlocked_preserve_hot_probe with LTS.
    }

    destruct `((alarm (MN2 n) = true /\ _) \/ sends_probe (n', R) p (NetMod.get n MN2)) as [|].

    all: exists MN2, (mpath0 ++ mpath1); repeat split > [eattac| |eattac].
    all: eapply detect_path_app; eattac.
  Qed.


  Lemma propagation [MN0 : MNet] [n m m' p] [DS] :
    KIC MN0 ->
    DeadSet DS '' MN0 ->
    trans_lock MN0 n m ->
    lock MN0 m m' ->
    In n DS ->
    sends_probe (m, R) p (NetMod.get m' MN0) ->
    hot MN0 p n ->
    In (init p) DS ->
    exists MN1 mpath n',
      (MN0 =[mpath]=> MN1)
      /\ detect_path DS mpath
      /\ ((alarm (MN1 n') = true /\ n' = init p) \/ (lock MN1 n n' /\ sends_probe (n, R) p (NetMod.get n' MN1))).

  Proof.
    intros.

    assert (well_formed '' MN0) by eauto with LTS.
    assert (deadlocked n '' MN0) as Hn by (exists DS; eattac).
    assert (deadlocked m '' MN0) as Hm by (eattac).
    assert (deadlocked m' '' MN0) as Hm' by (eattac).
    assert (deadlocked (init p) '' MN0) as Hip by (exists DS; attac).
    apply dep_lock_chain in H1.
    hsimpl in *.
    clear H8. (* ~List.In m L *)

    generalize dependent n m m' MN0.
    ltac1:(rev_induction L); intros; hsimpl in *.
    {
      assert (n = init p) by consider (hot MN0 p n).
      specialize (@propagation1 MN0 n m m' p) as HP.
      specialize (HP ltac:(auto)).
      specialize (HP ltac:(auto)).
      specialize (HP ltac:(auto)).
      specialize (HP ltac:(auto)).
      specialize (HP ltac:(auto)).
      specialize (HP ltac:(subst;auto)).
      specialize (HP ltac:(subst;auto)).
      hsimpl in HP.
      destruct `((alarm (MN1 m) = true /\ m = init p) \/
                   (alarm (MN1 m') = true /\ m' = init p) \/ sends_probe (n, R) p (NetMod.get m MN1)
        ) as [|[|]].

      - exists MN1, mpath, m.
        repeat split > [eattac | | eattac].
        eapply detect_path_incl > [| eattac]; ieattac.
        destruct `(_ \/ _); eattac.
      - exists MN1, mpath, m'.
        repeat split > [eattac | | eattac].
        eapply detect_path_incl > [| eattac]; ieattac.
        destruct `(_ \/ _); subst; eauto.
        eapply deadset_in; eauto.

      - assert (lock MN1 n m).
        {
          consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS.
          assert (deadlocked m '' MN0) by eauto using deadlocked_dep' with LTS.
          assert (deadlocked n '' MN0) by eauto using deadlocked_dep' with LTS.
          eauto 13 with LTS.
        }
        exists MN1, mpath, m.
        repeat split; auto.
        eapply detect_path_incl > [| eattac]; ieattac.
        destruct `(_ \/ _); subst; eauto using deadset_in.
    }

    assert (n = init p) by consider (hot MN0 p n).

    consider (exists MN1 mpath0,
                 (MN0 =[mpath0]=> MN1)
                 /\ _
                 /\ ((alarm (MN1 m) = true /\ m = init p) \/ (alarm (MN1 m') = true /\ m' = init p) \/ sends_probe (a, R) p (NetMod.get m MN1))
             ) by (subst; auto 2 using propagation1).
    destruct `((alarm (MN1 m) = true /\ m = init p) \/ (alarm (MN1 m') = true /\ m' = init p) \/ sends_probe (a, R) p (NetMod.get m MN1))
      as [|[|]].

    1: {
      eexists MN1, mpath0, _.
      repeat split > [eattac | | eattac].
      eapply detect_path_incl > [| eattac].
      ieattac.
      destruct `(_ \/ _); subst; eauto using deadset_in.
    }
    1: {
      eexists MN1, mpath0, _.
      repeat split > [eattac | | eattac].
      eapply detect_path_incl > [| eattac].
      ieattac.
      destruct `(_ \/ _); subst; eauto using deadset_in.
      eauto using deadset_dep_in with LTS.
    }

    assert (deadlocked m '' MN0) by eauto with LTS.

    assert (well_formed '' MN1).
    {
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS.
      eauto with LTS.
    }
    assert (KIC MN1) by eauto with LTS.
    assert (hot MN1 p (init p)).
    {
      unfold hot in *.
      rewrite <- `(n = init p) in *.
      assert (lock_id (MN0 n) = lock_id (MN1 n)) by
        eauto using deadlocked_preserve_M_lock_id with LTS.
      rewrite <- `(lock_id (MN0 n) = lock_id (MN1 n)).
      auto.
    }
    assert (deadlocked m '' MN1).
    {
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS.
      eauto 2 with LTS.
    }
    assert (lock MN1 a m).
    {
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS.
      assert (deadlocked m' '' MN0) by eauto using deadlocked_dep' with LTS.
      assert (deadlocked m '' MN0) by eauto using deadlocked_dep' with LTS.
      assert (deadlocked a '' MN0) by eauto using deadlocked_dep' with LTS.
      eauto using deadlocked_lock_on' with LTS.
    }
    assert (lock_chain '' MN1 n l a).
    {
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS.
      assert (deadlocked m' '' MN0) by eauto using deadlocked_dep' with LTS.
      assert (deadlocked m '' MN0) by eauto using deadlocked_dep' with LTS.
      assert (deadlocked a '' MN0) by eauto using deadlocked_dep' with LTS.
      eapply deadlocked_lock_chain_invariant. eauto with LTS.
      eapply deadlocked_dep'; eauto with LTS.
      eauto.
    }

    assert (deadlocked (init p) '' MN1).
    {
      subst.
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS.
      assert (deadlocked m' '' MN0) by eauto using deadlocked_dep' with LTS.
      assert (deadlocked m '' MN0) by eauto using deadlocked_dep' with LTS.
      assert (deadlocked a '' MN0) by eauto using deadlocked_dep' with LTS.
      eapply deadlocked_dep'; eauto with LTS.
    }

    assert (hot MN1 p n).
    {
      subst.
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS.
    }

    assert (In m DS).
    {
      eapply deadset_dep_in. eauto. eapply H6. subst. eauto 3 with LTS.
    }

    assert (DeadSet DS '' MN1).
    {
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS.
      eauto with LTS.
    }

    specialize H with(MN0:=MN1)(m':=m)(m:=a)(n:=n).
    specialize (H ltac:(auto)).
    specialize (H ltac:(auto)).
    specialize (H ltac:(eauto)).
    specialize (H ltac:(auto)).
    specialize (H ltac:(auto)).
    specialize (H ltac:(auto)).
    specialize (H ltac:(auto)).
    specialize (H ltac:(eauto with LTS)).
    specialize (H ltac:(subst; auto)).
    specialize (H ltac:(subst; auto)).
    specialize (H ltac:(eauto 13 using deadlocked_preserve_hot_probe with LTS)).
    specialize (H ltac:(exists DS; eauto 3 using deadset_dep_in with LTS)).
    hsimpl in H.

    exists MN2, (mpath0 ++ mpath), n'; repeat split > [eattac | | eattac].
    assert (In a DS) by eauto 3 using deadset_dep_in with LTS.
    eapply detect_path_incl with (DS0:=(a::DS)). eattac.
    eapply detect_path_app. 2: eattac.
    eapply detect_path_incl. 2: eattac.
    intros ? ?.
    destruct `(_ \/ _). 1: eattac.
    destruct `(_ \/ _); subst.
    assert (In a0 DS) by eauto 3 using deadset_dep_in with LTS.
    attac.
    bs.
  Qed.


  Lemma propagation_finito [MN0 : MNet] [n m m' p] [DS] :
    KIC MN0 ->
    DeadSet DS '' MN0 ->
    trans_lock MN0 n m ->
    lock MN0 m m' ->
    In n DS ->
    hot MN0 p n ->
    sends_probe (m, R) p (NetMod.get m' MN0)  ->
    exists mpath MN1,
      (MN0 =[mpath]=> MN1)
      /\ detect_path DS mpath
      /\ alarm (MN1 n) = true.
  (* TODO does propagation_init need lock assumption? *)
  Proof.
    intros.
    assert (well_formed '' MN0) by eauto with LTS.

    consider (exists MN1 mpath0 n',
                 (MN0 =[mpath0]=> MN1)
                 /\ detect_path DS mpath0
                 /\ ((alarm (MN1 n') = true /\ n' = init p) \/ (lock MN1 n n' /\ sends_probe (n, R) p (NetMod.get n' MN1)))).
    {
      consider (hot MN0 p n).
      eapply propagation; eauto 3 with LTS.
      attac.
    }

    destruct `((alarm (MN1 n') = true /\ n' = init p) \/ lock MN1 n n' /\ sends_probe (n, R) p (NetMod.get n' MN1)) as [|[? ?]].
    1: { consider (hot _ _ _); eattac. }

    consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound.

    have (well_formed '' MN1) by eauto with LTS.
    have (KIC MN1) by auto with LTS.
    have (deadlocked n '' MN0) by (exists DS; eauto with LTS).
    have (deadlocked m '' MN0) by (exists DS; eauto using deadset_dep_in with LTS).
    have (deadlocked m' '' MN0) by (exists DS; eauto using deadset_in with LTS).
    assert (hot MN1 p (init p)).
    {
      consider (hot MN0 p n).
      constructor; auto.
      replace (lock_id (MN0 (init p))) with  (lock_id (MN1 (init p)))
        by re_have eauto using eq_sym, deadlocked_preserve_M_lock_id with LTS.
      ltac1:(autounfold with LTS_get in * ); auto.
    }

    consider (exists MN2 mpath1 MQn',
                 (MN1 =[mpath1]=> MN2)
                 /\ detect_path [n'] mpath1
                 /\ ((alarm (MN2 n') = true /\ n' = init p) \/ (mserv_i (MN2 n) = MQn' ++ [EvRecv (n', R) p]))).
    {
      eapply sends_probe_send; re_have eauto with LTS.
    }

    destruct `((alarm (MN2 n') = true /\ n' = init p) \/ mserv_i (MN2 n) = MQn' ++ [EvRecv (n', R) p]).
    1: { exists (mpath0 ++ mpath1), MN2; repeat split > [eattac | | eattac].
         assert (In n' DS). assert (DeadSet DS '' MN1) by eauto 3 with LTS. eauto 4 using deadset_in with LTS.
         eapply detect_path_app; eauto with LTS. eapply detect_path_incl; eauto; ieattac.
    }

    consider (exists ppath, '' MN1 =[ppath]=> '' MN2) by eauto using transp_sound.

    have (well_formed '' MN2) by eauto with LTS.
    have (KIC MN2) by auto with LTS.
    assert (deadlocked n '' MN2).
    {
      assert ('' MN0 =[ppath ++ ppath0]=> '' MN2) by eauto with LTS.
      re_have eauto 4 with LTS.
    }
    assert (hot MN2 p (init p)).
    {
      consider (n = init p) by (consider (hot MN0 p n)).
      consider (hot MN1 p (init p)).
      have (deadlocked (init p) '' MN1).
      constructor; auto.
      replace (lock_id (MN2 (init p))) with  (lock_id (MN1 (init p)))
        by re_have eauto using eq_sym, deadlocked_preserve_M_lock_id with LTS.
      ltac1:(autounfold with LTS_get in * ); auto.
    }
    assert  (List.In (hot_ev_of MN2 n' n) (mserv_i (MN2 n))).
    {
      unfold hot_ev_of.
      assert (p = hot_of MN2 n).
      {
        consider (hot MN2 p (init p)).
        consider (hot MN0 p n).
        destruct p; simpl in *.
        unfold hot_of.
        ltac1:(autounfold with LTS_get in * ).
        f_equal.
        auto.
      }  (* todo disgrace *)
      rewrite <- `(p = _).
      rewrite `(mserv_i (_ _) = _).
      auto with datatypes.
    }
    have (List.In (hot_ev_of MN2 n' n) (mserv_i (MN2 n))) by (unfold hot_ev_of; eauto with LTS).

    consider (exists MN3 mpath2, (MN2 =[mpath2]=> MN3) /\ detect_path _ _ /\ alarm (MN3 n) = true)
      by re_have (eauto using detection_finito with LTS).

    exists (mpath0 ++ mpath1 ++ mpath2), MN3.
    repeat split > [eattac | | eattac].
    repeat (eapply detect_path_app); eauto.
    assert (In n' DS). assert (DeadSet DS '' MN1) by eauto 3 with LTS. eauto 4 using deadset_in with LTS.
    eapply detect_path_incl; eauto; ieattac.
    eapply detect_path_incl; eauto; ieattac.
  Qed.


  (* TODO better name xd *)
  Lemma mserv_Q_lock_sound [MN m n v] :
    well_formed '' MN ->
    List.In (TrRecv (m, Q) v) (mserv_i (MN n)) ->
    lock MN m n.
  Proof.
    intros.
    consider (well_formed '' MN).
    enough (pq_client m (NetMod.get n '' MN)); attac.
    unfold net_deinstr, NetGet in *.
    destruct (NetMod.get n MN) as [MQ M S] eqn:?.
    hsimpl in |- *.
    destruct ((deinstr (NetMod.get n MN))) eqn:?.
    econstructor 1; attac.
    eapply deinstr_In_recv. eauto.
    rewrite Heqm0 in *.
    eauto.
  Qed.


  Lemma propagation_init' [MN0 : MNet] [n n' m] [v ] [DS] :
    KIC MN0 ->
    DeadSet DS '' MN0 ->
    In n DS ->
    lock MN0 n n' ->
    List.In (TrRecv (m, Q) v) (mserv_i (MN0 n)) ->
    exists MN1 mpath,
      (MN0 =[mpath]=> MN1)
      /\ detect_path DS mpath
      /\ sends_probe (m, R) (hot_of MN1 n) (NetMod.get n MN1).

  Proof.
    intros.
    assert (well_formed '' MN0) by eauto with LTS.

    assert (exists mpath0 MN1 MQ1 s S1,
               (MN0 =[mpath0]=> MN1)
               /\ detect_path DS mpath0
               /\ NetMod.get n MN1 = mserv (TrRecv (m, Q) v :: MQ1) ((MRecv s)) S1
           ) as Hxx'.
    {
      specialize (flush_one_In ltac:(eauto)) as ?.
      hsimpl in *.
      exists mpath, MN1, (MQ01 ++ MQ1'), s, S1.
      repeat split > [attac | | attac].
      apply detect_path_incl with (DS0:=[n]).
      ieattac.
      eattac.
    }
    hsimpl in Hxx'.

    assert (exists mpath1 MN2 M2 S2,
               (MN1 =[mpath1]=> MN2)
               /\ detect_path DS mpath1
               /\ NetMod.get n MN2 = mserv MQ1 (MSend (m, R) (hot_of MN2 n) M2) S2
           ) as Hx.
    {

      destruct S1 as [I1 P1 O1].
      pose (serv (I1 ++ [(m, Q, v)]) P1 O1) as S2.
      pose  {|self := self s
            ; lock_id := lock_id s
            ; lock := lock s
            ; wait := m :: wait s
            ; alarm := alarm s
            |} as s1.
      pose (NetMod.put n (mserv MQ1 (mon_handle (TrRecv (m, Q) v) s ) S2) MN1) as MN1'.

      exists [NTau n (MActP (Recv (m, Q) v))], MN1', (MRecv s1), S2.

      destruct s.
      subst MN1' s1 S2.

      assert (lock0 <> None).
      {
        consider (KIC MN1) by eauto with LTS.
        consider (exists path, '' MN0 =[path]=> '' MN1) by eauto using transp_sound with LTS.
        assert (DeadSet DS '' MN1) by eauto with LTS.
        assert (deadlocked n '' MN0) by (exists DS; eauto with LTS).
        assert (lock MN1 n n') by eauto with LTS.
        specialize (H_lock_C n n' ltac:(auto)).
        ltac1:(autounfold with LTS_get in H_lock_C).
        rewrite `(NetMod.get n MN1 = _) in H_lock_C.
        simpl in *.
        bs.
      }
      assert (n = self0).
      {
        consider (KIC MN1) by eauto with LTS.
        specialize (H_self_C n).
        ltac1:(autounfold with LTS_get in H_self_C).
        rewrite `(NetMod.get n MN1 = _) in H_self_C.
        auto.
      }

      destruct lock0. 2: bs.
      subst.

      repeat split > [attac | | attac].
      - hsimpl in |- *.
        eapply path_seq0.
        constructor. constructor.
        constructor. hrewrite NetMod.get.
        attac.
      - eapply detect_path_incl with (DS0:=[self0]). ieattac.
        eapply detect_path1. constructor; attac.
      - unfold hot_of, NetGet.
        hsimpl in *.
        attac.
    }
    hsimpl in Hx.

    exists MN2, (mpath0 ++ mpath1).
    repeat split > [eattac | | eattac].
    - eapply detect_path_app; auto.
    - rewrite `(NetMod.get n MN2 = _).
      constructor.
  Qed.


  Lemma propagation_init_finito [MN0 : MNet] [n m] [v] DS :
    KIC MN0 ->
    DeadSet DS MN0 ->
    trans_lock MN0 n m ->
    In n DS ->
    List.In (TrRecv (m, Q) v) (mserv_i (MN0 n)) ->
    exists MN1 mpath,
      (MN0 =[mpath]=> MN1)
      /\ detect_path DS mpath
      /\ (exists n', trans_lock MN0 n n' /\ alarm (MN1 n') = true).

  Proof.
    intros.
    assert (well_formed '' MN0) by eauto with LTS.

    assert (lock MN0 m n) by eauto using mserv_Q_lock_sound.
    assert (trans_lock MN0 n n) by eauto with LTS.
    assert (deadlocked n '' MN0) by (exists DS; eauto 2 with LTS).

    consider (exists MN1 mpath0,
                 (MN0 =[mpath0]=> MN1)
                 /\ detect_path DS mpath0
                 /\ sends_probe (m, R) (hot_of MN1 n) (NetMod.get n MN1))
      by (consider (trans_lock MN0 n n) by eauto using propagation_init'; eauto using propagation_init').

    consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound.
    have (well_formed '' MN1) by eauto with LTS.
    have (KIC MN1) by auto with LTS.

    assert (deadlocked n '' MN1) by auto with LTS.
    assert (lock MN1 m n) by eauto with LTS.
    assert (trans_lock MN1 n n) by eauto with LTS.
    assert (trans_lock MN1 n m) by eauto with LTS.

    consider (exists mpath1 MN2, (MN1 =[mpath1]=> MN2) /\ _ /\ alarm (MN2 n) = true)
      by eauto using propagation_finito, hot_hot_of with LTS.

    exists MN2, (mpath0 ++ mpath1).
    eattac.
  Qed.


  Lemma locked_deinstr :
    forall (MN0 MN1 : MNet) a n,
      SRPC_net MN0 ->
      deadlocked n MN0 ->
      Flushing_NAct n a ->
      (MN0 =(a)=> MN1) ->
      net_deinstr MN0 = net_deinstr MN1.

  Proof.
    intros.

    consider (exists n', lock MN0 n n')
      by (eapply deadlocked_M_get_lock; eattac).

    destruct a; consider (Flushing_NAct _ _).
    - destruct m; doubt.
      + destruct p; doubt.
        unfold net_deinstr in *.
        apply NetMod.extensionality.
        intros.
        repeat (rewrite NetMod.get_map in * ).
        consider (_ =(_)=> _).
        hsimpl in *.
        smash_eq n n1; attac.
        unfold deinstr.
        attac.
        compat_hsimpl in *; attac.
        repeat (rewrite <- app_assoc). attac.
      + destruct p; doubt.
      + destruct a; doubt.
        unfold net_deinstr in *.
        apply NetMod.extensionality.
        intros.
        repeat (rewrite NetMod.get_map in * ).
        consider (_ =(_)=> _).
        hsimpl in *.
        smash_eq n n0; attac.
        unfold deinstr.
        attac.
    - apply net_deinstr_act in H2.
      hsimpl in *.
      destruct p; doubt; attac.
      enough (n <> n) by bs.
      eapply lock_no_send; eauto.
  Qed.


  Lemma locked_deinstrs :
    forall MN0 MN1 mpath DS,
      well_formed '' MN0 ->
      DeadSet DS '' MN0 ->
      Forall (fun a => exists n, In n DS /\ Flushing_NAct n a) mpath ->
      (MN0 =[mpath]=> MN1) ->
      net_deinstr MN0 = net_deinstr MN1.

  Proof.
    intros.
    generalize dependent MN0.
    induction mpath; attac.
    rename N1 into MN0'.
    transitivity '(net_deinstr MN0').
    - eapply locked_deinstr; eauto with LTS.
      exists DS; eattac.
    - apply net_deinstr_act in H2.
      destruct (MNAct_to_PNAct a); eattac.
      hrewrite ('' MN0) in *.
      eapply IHmpath; eauto with LTS.
  Qed.


  Lemma locked_flushed :
    forall MN0 MN1 a n,
      SRPC_net '' MN0 ->
      deadlocked n '' MN0 ->
      Flushing_NAct n a ->
      (MN0 =(a)=> MN1) ->
      flushed MN0 ->
      flushed MN1.

  Proof.
    intros.

    unfold flushed, flushed_in, Flushed in *.
    intros.
    specialize (H3 n) as Hx.
    specialize (H3 n0) as Hx0.
    destruct (NetMod.get n0 MN0) as [MQ0 M0 S0] eqn:?.
    destruct (NetMod.get n0 MN1) as [MQ1 M1 S1] eqn:?.
    destruct a; kill H1.
    + smash_eq n0 n.
        * consider (_ =(_)=> _); hsimpl in *.
          destruct m; attac.
          -- destruct p; doubt.
             unfold net_deinstr, deinstr, ready_in, ready, apply_instr, instr_for, NetGet in *.
             compat_hsimpl in *; attac.
          -- destruct a; doubt.
             unfold net_deinstr, deinstr, ready_in, ready, apply_instr, instr_for, NetGet in *.
             compat_hsimpl in *; attac.
        * assert (NetMod.get n0 MN0 = NetMod.get n0 MN1) by eattac.
          unfold ready_in, ready, apply_instr, instr_for, NetGet in *.
          attac.
      + smash_eq n0 n.
        * consider (_ =(_)=> _); hsimpl in *.
          unfold net_deinstr, deinstr, ready_in, ready, apply_instr, instr_for, NetGet in *.
          destruct p; compat_hsimpl in *; doubt.
          smash_eq n0 n2; blast_cases; attac.
        * smash_eq n0 n2.
          -- consider (_ =(_)=> _).
             assert (NetMod.get n0 MN0 = NetMod.get n0 N0') by eauto using eq_sym, NV_stay.
             hsimpl in *.
             unfold ready_in, ready, apply_instr, instr_for, NetGet in *.
             rewrite <- `(NetMod.get n0 _ = _) in *.
             hsimpl in *.
             hsimpl in *.
             blast_cases; attac.
          -- assert (NetMod.get n0 MN0 = NetMod.get n0 MN1) by eattac.
             unfold ready_in, ready, apply_instr, instr_for, NetGet in *.
             attac.
  Qed.


  Lemma locked_flusheds :
    forall MN0 MN1 mpath DS,
      well_formed '' MN0 ->
      DeadSet DS '' MN0 ->
      Forall (fun a => exists n, In n DS /\ Flushing_NAct n a) mpath ->
      (MN0 =[mpath]=> MN1) ->
      flushed MN0 ->
      flushed MN1.

  Proof.
    intros.
    generalize dependent MN0.
    induction mpath; attac.
    assert (flushed N1); eauto using locked_flushed with LTS.
    - eapply locked_flushed; eauto with LTS.
      exists DS; eattac.
    - apply net_deinstr_act in H2.
      destruct (MNAct_to_PNAct a); eattac.
      hrewrite ('' MN0) in *.
      eapply IHmpath; eauto with LTS.
  Qed.


  Lemma to_instr : forall chans MN0,
      (forall n, not (In n chans) -> ready_in n MN0) ->
      flushed MN0 ->
      exists mnpath i1,
        (MN0 =[mnpath]=> apply_instr i1 MN0).

  Proof.
    intros.
    destruct (@flushed_ready chans MN0 ltac:(auto) ltac:(auto)) as (mpath & MN1 & ?).
    hsimpl in *.
    destruct (@flushed_ready_instr MN1 ltac:(auto) ltac:(auto)) as [i ?].
    exists mpath, i.
    hrewrite ('' MN0).
    rewrite <- `(MN1 = _).
    auto.
  Qed.

  Lemma KIC_AnySRPC_pq_instr [I : instr] [N] : KIC (I N) ->
                                               forall n, AnySRPC_serv (NetMod.get n N).
  Proof.
    intros ?.
    consider (KIC _); attac.
  Qed.

  #[export] Hint Immediate KIC_AnySRPC_pq_instr : LTS.

  Lemma net_preserve_alarm_path
    : forall mpath (MN0 MN1 : MNet) (n : Transp.Net.NAME.t'),
      KIC MN0 -> MN0 =[ mpath ]=> MN1 -> alarm (MN0 n) = true -> alarm (MN1 n) = true.

  Proof.
    induction mpath; attac.
    eapply IHmpath with (MN0:=N1); eauto 3 using net_preserve_alarm with LTS.
  Qed.

  Lemma KIC_instr_well_formed : forall (i : instr) N, KIC (i N) -> well_formed N.
  Proof.
    intros.
    consider (KIC _); hsimpl in *; auto.
  Qed.
  #[export] Hint Immediate KIC_instr_well_formed : LTS.


  Lemma ac_to_alarm [MN0 : MNet] [n] :
    KIC MN0 ->
    ac n MN0 ->
    trans_lock MN0 n n ->
    exists DS mpath MN1, (MN0 =[mpath]=> MN1) /\ DeadSet DS MN0 /\ detect_path DS mpath /\ alarm (MN1 n) = true.

  Proof.
    intros.

    assert (deadlocked n '' MN0) as [DS [? ?]] by eauto using dep_self_deadlocked with LTS.

    exists DS.

    destruct (alarm (MN0 n)) eqn:?.
    1: { exists [], MN0. unfold detect_path; eattac. }

    consider (ac n MN0).
    - consider (n = m \/ trans_lock MN0 n m).
      + consider (exists mpath MN1, (MN0 =[ mpath ]=> MN1) /\ detect_path DS mpath /\ alarm (MN1 m) = true)
          by eauto using propagation_finito, hot_hot_of with LTS.
        exists mpath, MN1. split; eauto with LTS.
      + consider (exists mpath MN1, (MN0 =[ mpath ]=> MN1) /\ detect_path DS mpath /\ alarm (MN1 n) = true)
          by eauto using propagation_finito, hot_hot_of with LTS.
        exists mpath, MN1. split; eauto with LTS.

    - assert (deadlocked n '' MN0) by (exists DS; eauto).
      consider (exists MN1 mpath, (MN0 =[mpath]=> MN1) /\ detect_path [n] mpath /\ alarm (MN1 n) = true)
        by eauto using detection_finito with LTS.
      exists mpath, MN1.
      repeat (split; eauto).
      eapply detect_path_incl; eauto.
      ieattac.
  Qed.


  Lemma ac_to_alarm_instr [MN0 : MNet] [n] :
    KIC MN0 ->
    ac n MN0 ->
    trans_lock MN0 n n ->
    flushed MN0 ->
    ready_net MN0 ->
    exists mpath (i0 : instr), (MN0 =[mpath]=> i0 MN0) /\ alarm (i0 MN0 n) = true.

  Proof.
    intros.

    consider (exists DS mpath0 MN1,
                 (MN0 =[ mpath0 ]=> MN1)
                 /\ DeadSet DS MN0
                 /\ detect_path DS mpath0
                 /\  alarm (MN1 n) = true
             ) by eauto using ac_to_alarm with LTS.

    consider (exists mpath1 (i1 : instr), (MN1 =[mpath1]=> i1 MN1)).
    {
      assert (flushed MN1).
      {
        assert (flushed MN0) by eauto using apply_instr_flushed.
        assert (well_formed '' MN0) by eauto 10 with LTS.
        eauto using locked_flusheds.
      }
      assert (forall n'', not (In n'' (path_particip mpath0)) -> ready_in n'' MN1).
      {
        intros.
        assert (ready_in n'' MN0) by eauto.
        unfold ready_in in *.
        replace (NetMod.get n'' MN1) with (NetMod.get n'' MN0) by eauto using path_particip_stay.
        blast_cases.
        eauto using apply_instr_ready.
      }
      eauto using to_instr.
    }

    replace (net_deinstr MN0) with (net_deinstr MN1)
      by (symmetry; eapply locked_deinstrs; eauto with LTS).

    exists (mpath0 ++ mpath1), i1.

    assert (KIC MN1) by eauto with LTS.
    eauto using net_preserve_alarm_path, deadset_dep_in with LTS.
  Qed.


  Theorem detection_completeness : forall (i0 : instr) N0 MN1 mpath0 DS,
      KIC (i0 N0) ->
      (i0 N0 =[ mpath0 ]=> MN1) ->
      DeadSet DS MN1 ->
      exists mpath1 MN2 n, (MN1 =[ mpath1 ]=> MN2) /\ In n DS /\ alarm (MN2 n) = true.

  Proof.
    intros.
    assert (KIC MN1) by eauto with LTS.
    consider (exists n, In n DS /\ trans_lock MN1 n n) by (eauto 8 using deadset_dep_self with LTS).
    consider (exists n', trans_lock MN1 n n' /\ ac n' MN1) by (consider (KIC MN1); attac).
    assert (trans_lock MN1 n' n') by (eauto using dep_reloop with LTS).
    consider (exists DS mpath1 MN2, (MN1 =[ mpath1 ]=> MN2) /\ DeadSet DS MN1 /\ _ /\  alarm (MN2 n') = true)
      by eauto using ac_to_alarm with LTS.

    exists mpath1, MN2, n'.
    now eauto with LTS.
  Qed.


  Corollary find_detection  : forall (i0 : instr) (N0 N1 : PNet) path (DS : Names),
      KIC (i0 N0) ->
      (N0 =[ path ]=> N1) ->
      DeadSet DS N1 ->
      exists mpath (i1 : instr) n,
        (i0 N0 =[ mpath ]=> i1 N1)
        /\ In n DS
        /\ alarm (i1 N1 n) = true.

  Proof.
    intros.
    consider (exists mpath0 (i1 : instr), i0 N0 =[ mpath0 ]=> i1 N1)
      by eauto using transp_complete.
    consider (exists n, In n DS /\ trans_lock N1 n n)
      by (eapply deadset_dep_self; eauto with LTS).
    consider (exists n', trans_lock (i1 N1) n n' /\ ac n' (i1 N1))
      by (consider (KIC (i1 N1)); attac).
    assert (trans_lock (i1 N1) n' n')
      by (hsimpl; eauto using dep_reloop with LTS).

    consider (exists mpath1 (i2 : instr), (i1 N1 =[ mpath1 ]=> i2 _) /\ alarm (i2 _ n') = true)
      by eauto using ac_to_alarm_instr, apply_instr_flushed, apply_instr_ready_net with LTS.

    exists (mpath0 ++ mpath1), i2, n'.
    now eauto using net_preserve_alarm_path with LTS.
  Qed.
End COMPL_F.

Module Type COMPL(Conf : DETECT_CONF) := Conf <+ DETECT_PARAMS(Conf) <+ COMPL_F.

(* TODO
End of deadlocked_vis_preserve_in_wait --- candidate for bidirectional hints?

 *)
