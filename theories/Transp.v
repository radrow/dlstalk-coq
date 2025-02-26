From Ltac2 Require Import Ltac2.

From Ltac2 Require Import Std.

From Ltac2 Require Fresh.
From Ltac2 Require Import Control.
From Ltac2 Require Import Message.
From Ltac2 Require Import Std.
From Ltac2 Require Import Printf.
From Ltac2 Require Import Notations.

Close Scope nat.

From Coq Require Import Lists.List.
Import ListNotations.


From DlStalk Require Import Tactics.
From DlStalk Require Import Lemmas.
From DlStalk Require Import ModelData.
From DlStalk Require Import LTS.
From DlStalk Require Import Que.
From DlStalk Require Import Model.
From DlStalk Require Import Network.


Module Type TRANSP_CONF.
  Include MON_CONF.
  Include NET_CONF.
End TRANSP_CONF.

Module Type TRANSP_PARAMS(Conf : TRANSP_CONF).
  Declare Module Export Mon : MON(Conf).
  Declare Module Export Net : NET(Conf) with Module Channel := Channel.
End TRANSP_PARAMS.

Module Type TRANSP_F(Import Conf : TRANSP_CONF)(Import Params : TRANSP_PARAMS(Conf)).

  (** Not-monitored network *)
  Notation PNet := (NetMod.t PQued).
  (** Monitored network *)
  Notation MNet := (NetMod.t MQued).

  Lemma pq_I_net_inv' : forall I P O n [N : PNet], (* TODO prime' is due to a name clash in SRPCNet.v *)
      NetMod.get n N = pq I P O ->
      pq_I (NetMod.get n N) = I.
  Proof. intros. rewrite H. attac. Qed.

  Lemma pq_P_net_inv' : forall I P O n N,
      NetMod.get n N = pq I P O ->
      pq_P (NetMod.get n N) = P.
  Proof. intros. rewrite H. attac. Qed.

  Lemma pq_O_net_inv' : forall I P O n N,
      NetMod.get n N = pq I P O ->
      pq_O (NetMod.get n N) = O.
  Proof. intros. rewrite H. attac. Qed.

  #[export] Hint Rewrite -> pq_I_net_inv' pq_P_net_inv' pq_O_net_inv' using spank : LTS LTS_concl.
  #[export] Hint Resolve pq_I_net_inv' pq_P_net_inv' pq_O_net_inv' : LTS LTS_concl.


  Lemma mq_MQ_net_inv : forall MQ M S n [N : MNet],
      NetMod.get n N = mq MQ M S ->
      mq_MQ (NetMod.get n N) = MQ.
  Proof. intros. rewrite H. attac. Qed.

  Lemma mq_M_net_inv : forall MQ M S n [N : MNet],
      NetMod.get n N = mq MQ M S ->
      mq_M (NetMod.get n N) = M.
  Proof. intros. rewrite H. attac. Qed.

  Lemma mq_S_net_inv : forall MQ M S n [N : MNet],
      NetMod.get n N = mq MQ M S ->
      mq_S (NetMod.get n N) = S.
  Proof. intros. rewrite H. attac. Qed.

  #[export] Hint Rewrite -> mq_MQ_net_inv mq_M_net_inv mq_S_net_inv using spank : LTS LTS_concl.
  #[export] Hint Resolve mq_MQ_net_inv mq_M_net_inv mq_S_net_inv : LTS LTS_concl.


  Definition PNAct := @NAct PAct gen_Act_PAct.

  Definition MNAct := @NAct MAct gen_Act_MAct.

  #[export] Hint Transparent PNAct MNAct : LTS typeclass_instances.


  Lemma PNet_trans_simpl_inv a n N I P O S :
    NetMod.get n N = pq I P O ->
    (NetMod.get n N =(a)=> S) <-> (pq I P O =(a)=> S).
  Proof. split; intros; rewrite H in *; auto. Qed.

  Lemma MNet_trans_simpl_inv a n N MQ M S MS :
    NetMod.get n N = mq MQ M S ->
    (NetMod.get n N =(a)=> MS) <-> (mq MQ M S =(a)=> MS).
  Proof. split; intros; rewrite H in *; auto. Qed.

  #[export] Hint Rewrite -> @PNet_trans_simpl_inv @MNet_trans_simpl_inv using spank : LTS_concl.


  Definition MNAct_to_PNAct (ma : MNAct) : option PNAct :=
    match ma with
    | NComm n m t (MValP v) => Some (@NComm PAct _ n m t v)
    | NTau n (MActP Tau) => Some (NTau n Tau)
    | _ => None
    end.

  Definition PNAct_to_MNAct (a : PNAct) : MNAct :=
    match a with
    | NComm n m t v => @NComm MAct _ n m t (MValP v)
    | NTau n a => NTau n (MActP Tau)
    end.


  Fixpoint MNPath_to_PNPath (mpath : list MNAct) : list PNAct :=
    match mpath with
    | [] => []
    | ma :: mpath' =>
        match MNAct_to_PNAct ma with
        | None => MNPath_to_PNPath mpath'
        | Some a => a :: MNPath_to_PNPath mpath'
        end
    end.


  Lemma MNPath_to_PNPath_app mpath0 mpath1 :
    MNPath_to_PNPath (mpath0 ++ mpath1) = MNPath_to_PNPath mpath0 ++ MNPath_to_PNPath mpath1.

  Proof.
    generalize dependent mpath1.
    induction mpath0; attac.
    destruct (MNAct_to_PNAct a) eqn:?; attac.
  Qed.

  #[export] Hint Rewrite -> MNPath_to_PNPath_app using assumption : LTS LTS_concl.


  Definition mon_assg := Name -> (MQ_clear * Mon_ready).

  Definition net_instr_n (I : mon_assg) (n : Name) (S : PQued) :=
    let (MQ, M) := I n in
    instr MQ M S.


  (** Instrumentation of all processes in a network *)
  Definition net_instr (I : mon_assg) (N : PNet) : MNet :=
    NetMod.map (net_instr_n I) N.

  #[export] Hint Transparent net_instr_n net_instr : LTS.


  (** Deinstrumentation of all processes *)
  Definition net_deinstr (N : MNet) : PNet :=
    NetMod.map (fun n S => deinstr S) N.

  #[export] Hint Transparent net_deinstr : LTS.

  #[reversible=no] Coercion net_deinstr : MNet >-> PNet.

  Notation "'' MN" := (net_deinstr MN) (at level 1).


  (** Network instrumentation is an injection *)
  Lemma net_instr_inj : forall [I] [N0 N1], net_instr I N0 = net_instr I N1 -> N0 = N1.

  Proof.
    intros.
    apply NetMod.extensionality.
    intros.
    unfold net_instr in H.
    unfold net_instr_n in H.

    assert (let (MQ, M) := &I n in instr MQ M (NetMod.get n N0) = let (MQ, M) := &I n in instr MQ M (NetMod.get n N1)).
    - rewrite <- (@NetMod.get_map PQued MQued
                    (fun (n : Name) (S : PQued) => let (MQ, M) := &I n in instr MQ M S)
        ).
      rewrite <- H.
      rewrite -> (@NetMod.get_map PQued MQued
                    (fun (n : Name) (S : PQued) => let (MQ, M) := &I n in instr MQ M S)
        ).
      destruct (&I n) as [MQ M].
      reflexivity.
    - destruct (&I n) as [MQ M].
      apply (@instr_inj MQ M).
      assumption.
  Qed.


  (** Deinstrumentation is inversion of instrumentation *)
  Lemma net_deinstr_instr : forall I N,
      net_deinstr (net_instr I N) = N.

  Proof.
    intros.
    unfold net_deinstr.
    unfold net_instr.
    unfold net_instr_n.
    apply NetMod.extensionality.
    intros.
    do 2 (rewrite NetMod.get_map).
    destruct (&I n).
    rewrite deinstr_instr.
    reflexivity.
  Qed.

  #[export] Hint Immediate net_deinstr_instr : LTS.
  #[export] Hint Rewrite -> net_deinstr_instr using spank : LTS LTS_concl.


  (** NV-transitions preserve instr (almost). *)
  Lemma NV_invariant : forall [n : Name] [a : MAct] [I0] [N0 : PNet] [MN1 : MNet],
      (net_instr I0 N0) ~(n@a)~> MN1 ->
      MN1 = NetMod.put n (NetMod.get n MN1) (net_instr I0 N0).

  Proof. eattac. Qed.


  (** NV-receives of monitor stuff preserve instr *)
  Lemma recvm_invariant_instr : forall [n n' : Name] [t0 v I0] [N0 : PNet] [MN1 : MNet],
      NVTrans n (MActM (Recv (n', t0) v)) (net_instr I0 N0) MN1 ->
      exists I1,
        MN1 = net_instr I1 N0.

  Proof with (eauto with LTS).
    intros.
    kill H.

    unfold net_instr in *.
    unfold net_instr_n in *.
    unfold instr in *.
    rewrite NetMod.get_map in H0.
    destruct (I0 n) as [[MQ0 MQ0_C] [M0 M0_R]].
    simpl in *.
    kill H0.

    unshelve epose (
        fun n0 => if NAME.eqb n0 n
               then
                 ( exist _ (MQ0 ++ [EvRecv (n', t0) v]) _,
                   exist _ M0 _
                 ) : (MQ_clear * Mon_ready)
               else I0 n0
      )
      as I1; destruct (I0 n); simpl in *...
    attac.
    exists I1.
    apply NetMod.extensionality.
    intros.
    subst I1.

    rewrite NetMod.get_map.
    smash_eq n n0; attac.
  Qed.


  (** Every process is always ready to receive. *)
  Lemma recv_available : forall (n n' : Name) t0 v (N0 : MNet),
    exists N1, NVTrans n (recv (n', t0) v) N0 N1.

  Proof.
    intros.
    remember (NetMod.get n N0) as M0.

    assert (exists M1, M0 =(recv (n', t0) v)=> M1) as [M1 TM]
        by (destruct M0 as [MQ0 P0]; destruct v; eattac).
    eattac.
  Qed.


  (** If a process can send, then it can in any network. *)
  Lemma send_available : forall [n n' : Name] [t v S] [N0 : MNet],
      (NetMod.get n N0 =(send (n', t) v)=> S) ->
      exists N1, NVTrans n (send (n', t) v) N0 N1 /\ S = NetMod.get n N1.

  Proof.
    intros.
    apply NT_Vis in H.
    exists (NetMod.put n &S N0).
    eattac.
  Qed.


  (** Every process is always ready to receive. *)
  Lemma send_comm_available : forall [n n' : Name] [t0 v S] [N0 : MNet],
      (NetMod.get n N0 =(send (n', t0) v)=> S) ->
      exists N1, (N0 =(NComm n n' t0 v)=> N1).

  Proof.
    intros.
    specialize (send_available H) as (N1 & NVT0 & HGet).
    specialize (recv_available n' n t0 v N1) as (N2 & NVT1).
    eattac.
  Qed.


  (** Every process is always ready to receive. *)
  Lemma recv_available_p : forall (n n' : Name) t0 v (N0 : PNet),
    exists N1, NVTrans n (recv (n', t0) v) N0 N1.

  Proof.
    intros.
    remember (NetMod.get n N0) as M0.

    assert (exists M1, M0 =(recv (n', t0) v)=> M1) as [M1 TM]
        by (destruct M0 as [MQ0 P0]; eattac).
    have (M0 =( recv (n', t0) v )=> M1).
    eattac.
  Qed.


  (** If a process can send, then it can in any network. *)
  Lemma send_available_p : forall [n n' : Name] [t0 v S] [N0 : PNet],
      (NetMod.get n N0 =(send (n', t0) v)=> S) ->
      exists N1, NVTrans n (send (n', t0) v) N0 N1
                 /\ S = NetMod.get n N1.

  Proof.
    intros.
    apply NT_Vis in H.
    exists (NetMod.put n &S N0).
    split; auto.
    rewrite NetMod.get_put_eq.
    reflexivity.
  Qed.


  (** Every process is always ready to receive. *)
  Lemma send_comm_available_p : forall [n n' : Name] [t0 v S] [N0 : PNet],
      (NetMod.get n N0 =(send (n', t0) v)=> S) ->
      exists N1,
        (N0 =(NComm n n' t0 v)=> N1).

  Proof.
    intros.
    specialize (send_available_p H) as (N1 & NVT0 & HGet).
    specialize (recv_available_p n' n t0 v N1) as (N2 & NVT1).
    exists N2.
    econstructor; eauto with LTS.
  Qed.


  Definition NoTrSend (MS : MQued) : Prop :=
    match MS with (mq MQ _ _) => NoSends_MQ MQ end.

  Definition no_sends_in n N := NoTrSend (NetMod.get n N).

  Definition no_sends (N : MNet) := forall n, no_sends_in n N.

  Lemma no_sends_in_NoSendsMQ [n MN MQ M S] :
    NetMod.get n MN = mq MQ M S ->
    no_sends_in n MN ->
    NoSends_MQ MQ.

  Proof. unfold no_sends_in, NoTrSend. attac. Qed.

  #[export] Hint Resolve no_sends_in_NoSendsMQ : LTS.


  Definition Flushed (MS : MQued) : Prop :=
    match MS with (mq MQ _ _) => MQ_Clear MQ end.

  Definition flushed_in n N := Flushed (NetMod.get n N).

  Definition flushed (N : MNet) := forall n, flushed_in n N.

  Definition Flushing_NAct (n : Name) (a : MNAct) : Prop :=
    match a with
    | NComm n0 n1 t v => n0 = n
    | NTau n' a => n' = n /\ Flushing_act a /\ ia a
    end.


  Lemma flushed_in_MQ_Clear [n MN MQ M S] :
    NetMod.get n MN = mq MQ M S ->
    flushed_in n MN ->
    MQ_Clear MQ.

  Proof. unfold flushed_in, Flushed. attac. Qed.

  #[export] Hint Resolve flushed_in_MQ_Clear : LTS.


  Definition get_I N n := match NetMod.get n N with pq i _ _ => i end.
  Definition get_P N n := match NetMod.get n N with pq _ p _ => p end.
  Definition get_O N n := match NetMod.get n N with pq _ _ o => o end.
  Definition get_MQ N n := match NetMod.get n N with mq MQ _ _ => MQ end.
  Definition get_M N n := match NetMod.get n N with mq _ M _ => M end.
  Definition get_Mc N n := state (get_M N n).
  Definition get_H N n := handle (get_M N n).

  #[export] Hint Unfold get_I get_P get_O get_MQ get_M get_Mc get_H : LTS_get.
  #[export] Hint Transparent get_I get_P get_O get_MQ get_M get_Mc get_H : LTS.


  Lemma net_vis_preserve_handle [a MN0 MN1 n n'] :
    (MN0 ~(n' @ a)~> MN1) ->
    handle (get_M MN0 n) = handle (get_M MN1 n).

  Proof.
    intros.
    unfold get_M.
    smash_eq n n'.
    2: replace (NetMod.get n MN0) with (NetMod.get n MN1) by eauto using NV_stay, eq_sym; auto.

    destruct (NetMod.get n MN0) eqn:?.
    destruct (NetMod.get n MN1) eqn:?.
    eapply mq_preserve_handle.
    hsimpl in *. hsimpl in *.
    rewrite `(NetMod.get n MN0 = _) in *.
    eauto.
  Qed.


  Lemma net_preserve_handle [na MN0 MN1 n] :
    (MN0 =(na)=> MN1) ->
    handle (get_M MN0 n) = handle (get_M MN1 n).

  Proof.
    intros.
    consider (_ =(_)=> _).
    - eauto using net_vis_preserve_handle.
    - transitivity '(handle (get_M N0' n)).
      eauto using net_vis_preserve_handle.
      eauto using net_vis_preserve_handle.
  Qed.


  Lemma Clear_NoSends_MQ : forall MQ, MQ_Clear MQ -> NoSends_MQ MQ.
  Proof. induction MQ; attac. Qed.

  #[export] Hint Immediate Clear_NoSends_MQ  : LTS.

  Lemma flushed_in_NoSends_MQ : forall MN n, flushed_in n MN -> NoSends_MQ (get_MQ MN n).
  Proof. unfold flushed_in, get_MQ. intros. destruct (NetMod.get n MN); attac. Qed.

  #[export] Hint Immediate flushed_in_NoSends_MQ  : LTS.


  Definition ready_in n N :=
    ready_q (NetMod.get n N).

  Definition ready_net N := forall n, ready_in n N.


  Lemma net_instr_clear : forall I N MQ M S n,
      NetMod.get n (net_instr I N) = mq MQ M S ->
      MQ_Clear MQ.

  Proof.
    intros.
    unfold net_instr, net_instr_n, instr in *; hsimpl in *.
    destruct (&I n).
    attac.
  Qed.

  Lemma net_instr_ready : forall I N MQ M S n,
      NetMod.get n (net_instr I N) = mq MQ M S ->
      ready M.

  Proof.
    intros.
    unfold net_instr, net_instr_n, instr in *; hsimpl in *.
    destruct (&I n).
    destruct `(Mon_ready).
    attac.
  Qed.

  Hint Resolve net_instr_clear net_instr_ready : LTS.

  Lemma flush_act_available : forall [n : Name] a S [N0 : MNet],
      (NetMod.get n N0 =(a)=> S) ->
      Flushing_act a ->
      (forall t0 v, a <> send (n, t0) v) ->
      (
        exists na N1,
          (N0 =(na)=> N1)
          /\ NetMod.get n N1 = S
          /\ (forall m, no_sends_in m N0 -> no_sends_in m N1)
          /\ (forall m, no_sends_in n N0 -> flushed_in m N0 -> flushed_in m N1)
          /\ (forall m, not (ready_in n N0) -> [a] >:~ [] -> ready_in m N0 -> ready_in m N1)
          /\ (flushed N0 -> net_deinstr N0 = net_deinstr N1)
      ).

  Proof using Type with (eauto with LTS).
    intros * T HF HNoself.
    destruct a; hsimpl in *; hsimpl in |- *.
    - exists (NTau n (MActP p)).
      exists (NetMod.put n &S N0).
      hsimpl in *.
      unfold no_sends_in, NoTrSend, flushed_in, flushed, Flushed, net_deinstr, ready_in in *.

      eattac.
      + destruct p; doubt.
        hsimpl in *.
        smash_eq n m; attac.

      + destruct p; doubt.
        hsimpl in *.
        smash_eq n m; attac.
      + destruct p; doubt.
        specialize (H n).
        hsimpl in *.
        bs (MQ_Clear (TrRecv n0 v :: MQ)) by attac.

    - destruct p; attac.
      + destruct n0 as [n0 t0].
        smash_eq n n0.
        1: specialize (HNoself t0 (MValP v)); bs.

        remember (mq MQ {| handle := h; state := h (TrSend (n0, t0) v) s |} P) as S.

        assert (exists N0', NetMod.get n N0' = &S /\ NVTrans n (send (n0, t0) (MValP v)) N0 N0')
          as (N0' & HeqN0 & NT0)
            by (exists (NetMod.put n &S N0); eattac).

        destruct (recv_available n0 n t0 (MValP v) N0') as (N0'' & NT0').
        exists (NComm n n0 t0 # v), N0''; attac.

        all: unfold no_sends_in, NoTrSend, flushed_in, flushed, Flushed, net_deinstr, ready_in in *.
        * hsimpl in *.
          smash_eq n n0 m; attac.

        * hsimpl in *. attac.
        * hsimpl in *. hsimpl in *.
          assert (flushed_in n N0) by auto.
          unfold flushed_in, Flushed in *.
          hsimpl in *. bs.
    - destruct a; attac.
      + destruct n0 as [n0 t0].

        smash_eq n n0.
        1: now (specialize (HNoself t0 (MValM v)); bs).

        assert (exists N1 : MNet, N0 =( NComm n n0 t0 ^ v)=> N1) as [N1 na]
          by (eapply send_comm_available; rewrite `(NetMod.get n N0 = _); eattac).
        eexists _, _.
        split. 1: eauto.

        consider (N0 =(_)=> _).
        hsimpl in *.
        consider (M2 = M1) by (destruct M1, M2; eattac).

        all: unfold no_sends_in, NoTrSend, flushed_in, flushed, Flushed, net_deinstr, ready_in, ready_q in *.

        all: hsimpl in *; attac.

        1,2,3: smash_eq n n0 m; hsimpl in *; attac.

        apply NetMod.extensionality.
        intros.
        hsimpl in |- *.
        unfold deinstr.
        smash_eq n n0 n1; attac.

      + exists (NTau n (MActM Tau)).
        exists (NetMod.put n (mq MQ {| handle := h; state := h (EvRecv n0 msg) s |} P) N0).
        eattac.
        1: econstructor; eattac.

        all: unfold no_sends_in, NoTrSend, flushed_in, flushed, Flushed, net_deinstr, ready_in, ready_q in *.

        1,2: smash_eq n m; ltac1:(autorewrite with LTS ); attac.
        all: eattac.

        apply NetMod.extensionality.
        intros.
        hsimpl in |- *.
        unfold deinstr.
        smash_eq n n1; attac.
  Qed.


  Lemma flush_act_available_self : forall [n : Name] t0 v [MQ M S] [N0 : MNet],
      (NetMod.get n N0 =(send (n, t0) v)=> mq MQ M S) ->
      (
        exists na N1 MQ',
          (N0 =(na)=> N1)
          /\ NetMod.get n N1 = mq (MQ ++ MQ') M S
          /\  (forall m, no_sends_in m N0 -> no_sends_in m N1)
          /\  (forall m, flushed_in m N0 -> flushed_in m N1)
          /\ (forall m, not (ready_in n N0) -> [send (n, t0) v] >:~ [] -> ready_in m N0 -> ready_in m N1)
          /\ (flushed N0 -> net_deinstr N0 = net_deinstr N1)
          /\ Forall (fun t0 => match t0 with
                           | TrSend _ _ => False
                           | TrRecv _ _ => not (no_sends_in n N0)
                           | _ => True
                           end
              ) MQ'
      ).

  Proof.
    intros *. intros T.

    specialize (send_comm_available T) as (N1 & TN).

    destruct v; (eexists _, _).
    1: (exists [EvRecv (n, t0) (m)]); rename m into msg.
    2: (exists [TrRecv (n, t0) v]) .
    all: split > [ltac1:(eassumption)|]; repeat split; intros.
    all: unfold no_sends_in, NoTrSend, flushed_in, flushed, Flushed, net_deinstr, ready_in, ready_q in *.
    all: kill TN.
    - hsimpl in *.
      consider (M2 = M3) by (destruct M3, M2; attac).
      attac.
    - hsimpl in *.
      smash_eq n m; attac.
    - hsimpl in *.
      smash_eq n m; eattac.
    - hsimpl in *.
      smash_eq n m; eattac.
    - hsimpl in *.
      consider (M3 = M2) by (destruct M3, M2; attac).
      hsimpl in *.
      assert (forall MQ nc m M S, deinstr (mq (MQ ++ [EvRecv nc m]) M S) = deinstr (mq MQ M S)) as Hreduce.
      {
        clear.
        intros.
        destruct S.
        hsimpl in |- *.
        attac.
      } (* TODO lemma? *)

      unfold deinstr in Hreduce.
      specialize (Hreduce MQ0 (n, t0) msg M0 (pq l p l0)).
      hsimpl.
      rewrite <- (Hreduce); auto. clear Hreduce.
      unfold deinstr.
      assert (MQ_Clear MQ0) as MQ1_Clear.
      {
        specialize (H n).
        unfold flushed_in in *.
        attac.
      }

      apply NetMod.extensionality.
      intros.
      smash_eq n n0; attac; attac.

    - hsimpl in *.
      hsimpl in *.
      assert (M3 = M0) by (destruct M3, M0; attac).
      attac.
    - hsimpl in *.
      attac.
    - hsimpl in *.
      smash_eq n m; ltac1:(autorewrite with LTS ); eattac.
    - hsimpl in *.
      smash_eq n m; ltac1:(autorewrite with LTS ); attac.
    - hsimpl in *.
      bs.
    - hsimpl in *.
      specialize (H n).
      unfold flushed_in, Flushed in *.
      attac.
    - hsimpl in *; attac.
  Qed.


  Lemma send_self_dec : forall a n, (forall t0 (v : Payload), a <> send (n, t0) v) \/ exists t0 (v : Payload), a = send (n, t0) v.

  Proof.
    intros.
    destruct_ma &a; simpl.
    all: try (solve [left; intros t0 v0; destruct v0; eattac]); smash_eq n n0; eattac.
    - right. eexists t, (MValP v). eattac.
    - left; intros t0 v0; destruct v0; bs.
    - right. eexists t, (MValM v). eattac.
    - left; intros t0 v0; destruct v0; bs.
  Qed.


  Lemma flush_exists : forall MQ0 M0 I0 P O,
    exists mpath M1 I1,
      (mq MQ0 M0 (pq I0 P O) =[ mpath ]=> instr (exist _ [] (Forall_nil _)) M1 (pq (I0 ++ I1) P O))
      /\ Forall Flushing_act mpath.

  Proof.
    intros.
    exists (mk_flush_path MQ0 M0).
    unfold instr.
    simpl.
    unshelve eexists (exist _ (flush_M MQ0 M0) (flush_M_ready _ _)).
    exists (MQ_r MQ0).
    simpl.
    replace (pq (I0 ++ MQ_r MQ0) P &O) with (flush_S MQ0 (pq I0 P &O)) by attac.
    split; eauto using flush_go, flush_path_Flushing.
  Qed.


  Lemma flush_send_one : forall n MN0,
      True ->
      exists nmpath MN1,
        (MN0 =[ nmpath ]=> MN1)
        /\ (forall m, (n = m \/ no_sends_in m MN0) -> no_sends_in m MN1) /\ True.

  Proof.
    intros * _.

    destruct (NetMod.get n MN0) as [MQ0 M0 [I0 P0 O0]] eqn:Hn.

    destruct (flush_exists MQ0 M0 I0 P0 O0)
      as (mpath & M1 & I1 & TM & HF).

    remember (pq I0 P0 O0) as S0. clear HeqS0.
    remember (pq (I0 ++ I1) P0 O0) as S1. clear HeqS1 I0 I1 P0 O0.
    remember (mq MQ0 M0 S0) as MS0. clear HeqMS0.

    remember (instr (exist _ [] _) M1 S1) as MS1.
    assert (NoTrSend MS1) as HNoSend1 by attac.

    unfold instr in HeqMS1. simpl in HeqMS1.

    remember [] as MQ1. clear HeqMQ1.

    generalize dependent MS1.
    generalize dependent MQ1.
    generalize dependent MS0.
    generalize dependent MN0.

    induction mpath; intros.
    1: eexists _, _; eattac; kill H; unfold no_sends_in, NoTrSend; kill TM.
    1: rewrite `(NetMod.get m _ = _); auto.

    hsimpl in *.
    destruct (send_self_dec a n); intros.
    - apply flush_act_available in TM
          as (na & MN0' & TN0 & HEq & HPreserve0 & _); auto.

      normalize_hyp @IHmpath.
      edestruct IHmpath as (nmpath & MN1 & TN1 & HPreserve1); eauto.

      exists (na :: nmpath).
      exists MN1.
      attac.

      destruct H0; eattac.

    - strip_exists @H; subst.
      destruct N1 as [MQ0' M0' S0'].
      eapply flush_act_available_self in TM
          as (na & MN0' & MQ' & TN0 & HEq & HPreserveNS0 & HPreserveF0 & _ & _ & HNS1); auto.
      assert (NoTrSend (mq (MQ1 ++ MQ') (proj1_sig M1) S1)) as HNS1'.
      {
        apply Forall_app; split; auto.
        unshelve eapply (Forall_impl _ _ HNS1).
        destruct a; auto.
      }

      apply (Flushing_cont MQ') in TM0; auto.

      normalize_hyp @IHmpath.
      edestruct IHmpath as (nmpath & MN1 & TN1 & HPreserve1); eauto.

      exists (na :: nmpath).
      exists MN1.
      attac.

      destruct H; eattac.
  Qed.

  Ltac guess v H :=
    repeat match type of H with
      | forall x : ?T, _ =>
          match type of T with
          | Prop =>
              (let H' := fresh "H'" in
               assert (H' : T); [
                   solve [ eauto 6 ]
                 | specialize (H H'); clear H' ])
              || fail 1
          | _ =>
              specialize (H v)
              || let x := fresh "x" in
              evar (x : T);
              let x' := eval unfold x in x in
                clear x; specialize (H x')
          end
      end.


  Lemma flush_nosend_one : forall n MN0,
      no_sends MN0 ->
      exists nmpath MN1,
        (MN0 =[ nmpath ]=> MN1)
        /\ (forall m, (n = m \/ flushed_in m MN0) -> flushed_in m MN1)
        /\ no_sends MN1.
  Proof.
    intros *. intros HNS0.

    destruct (NetMod.get n MN0) as [MQ0 M0 [I0 P0 O0]] eqn:Hn.

    destruct (flush_exists MQ0 M0 I0 P0 O0)
      as (mpath & M1 & I1 & TM & HF).

    remember (pq I0 P0 O0) as S0. clear HeqS0.
    remember (pq (I0 ++ I1) P0 O0) as S1. clear HeqS1 I0 I1 P0 O0.
    remember (mq MQ0 M0 S0) as MS0. clear HeqMS0.

    eremember (instr (exist _ [] _) M1 S1) as MS1; eauto.
    assert (Flushed MS1) as HNoSend1. subst. constructor.

    unfold instr in HeqMS1. simpl in HeqMS1.

    remember [] as MQ1. clear HeqMQ1.

    generalize dependent MS1.
    generalize dependent MQ1.
    generalize dependent MS0.
    generalize dependent MN0.

    induction mpath; intros.
    kill TM. exists [], MN0. repeat split; auto. constructor. intros.
    destruct H; subst. unfold flushed_in.
    rewrite H1.
    assumption. assumption.

    kill HF.
    rename H0 into HF_a.
    rename H into HF_mpath.

    kill TM.
    rename N1 into MS0'.
    rename T0 into TM0.
    rename T1 into TM1.

    destruct MS0' as [MQ0' M0' S0'].

    destruct (send_self_dec a n).
    - replace ( MTrans a (NetMod.get n MN0) (mq MQ0' M0' S0'))
        with  ((NetMod.get n MN0) =(a)=> mq MQ0' M0' S0')
        in TM0; auto.

      apply flush_act_available in TM0
          as (na & MN0' & TN0 & HEq & HPreserveNS0 & HPreserveF0 & _); auto.

      assert (no_sends MN0') as HNS0'.
      unfold no_sends. intros. apply HPreserveNS0. apply HNS0.

      ltac1:(guess MN0' IHmpath).
      destruct IHmpath as (nmpath & MN1 & TN1 & HPreserve1 & HNS1); auto.

      exists (na :: nmpath).
      exists MN1.

      repeat split; auto.
      apply (path_seq1 TN0 TN1).

      intros.
      destruct (NAME.eq_dec m n); subst; destruct H0; try (congruence); subst...
      + apply HPreserve1.
        left; reflexivity.
      + apply HPreserve1.
        left; reflexivity.
      + unfold flushed_in in *.
        apply HPreserve1.
        right.
        apply HPreserveF0.
        apply HNS0.
        assumption.

    - destruct H as [t0 [v Hn]].
      kill Hn.

      eapply flush_act_available_self in TM0
          as (na & MN0' & MQ' & TN0 & HEq & HPreserveNS0 & HPreserveF0 & _ & _ & HNS0''); auto.


      apply (Flushing_cont MQ') in TM1; auto.

      assert (no_sends MN0') as HNS0'.
      unfold no_sends. intros. apply HPreserveNS0. apply HNS0.

      assert (Flushed (mq (MQ1 ++ MQ') (proj1_sig M1) S1)) as HF1'.
      { apply Forall_app; split; auto.
        unshelve eapply (Forall_impl _ _ HNS0'').
        intros. simpl in *. destruct a; auto.
        bs.
      }

      ltac1:(guess MN0' IHmpath).
      destruct IHmpath as (nmpath & MN1 & TN1 & HPreserve1 & HNS1); auto.

      exists (na :: nmpath).
      exists MN1.

      repeat split; auto.
      apply (path_seq1 TN0 TN1).

      intros.
      kill H; auto.
  Qed.


  Lemma ready_in_dec : forall n N,
      ready_in n N \/ not (ready_in n N).

  Proof.
    intros.
    unfold ready_in in *.
    destruct (NetMod.get n N).
    unfold ready_q.
    unfold ready.
    destruct m.
    destruct state0.
    - left.
      eattac.
    - right.
      unfold not.
      intros.
      eattac.
  Qed.

  Lemma ready_exists : forall MQ M0 S,
    exists mpath M1,
      (mq MQ M0 S =[mpath]=> mq MQ M1 S)
      /\ Forall Flushing_act mpath
      /\ ready M1
      /\ mpath >:~ [].

  Proof with eattac.
    intros.
    generalize dependent MQ.
    destruct M0.
    induction state0; intros.
    - exists [], {|handle:=handle0;state:=MRecv state0|}...
    - specialize (IHstate0 MQ).
      edestruct IHstate0 as (mpath & M1 & TM & HF & HR & HC).
      exists (MActM (Send to msg) :: mpath), M1...
  Qed.

  #[export] Hint Resolve ready_exists : LTS.


  Lemma ready_exists_q : forall MS0,
    exists mpath MS1,
      (MS0 =[mpath]=> MS1)
      /\ Forall Flushing_act mpath
      /\ ready_q MS1
      /\ mpath >:~ [].

  Proof with (eauto with LTS).
    intros MS0.
    destruct MS0 as [MQ0 M0 S0].
    destruct (ready_exists MQ0 M0 S0) as (mpath & M1 & TM & HF & HR' & HC)...
    eexists...
  Qed.

  Theorem path_corr_split1 : forall ma mpath ppath,
      (ma :: mpath) >:~ ppath <->
        exists ppath0 ppath1,
          ppath = ppath0 ++ ppath1
          /\ [ma] >:~ ppath0
          /\ mpath >:~ ppath1.

  Proof.
    split.
    - intros * HC.
      apply path_corr_split.
      auto.
    - intros. hsimpl in *.
      replace (ma::mpath) with ([ma] ++ mpath) by auto.
      destruct_ma ma; attac.
  Qed.
  Theorem path_corr_split_nil1 : forall [ma mpath],
      (ma :: mpath) >:~ [] ->
      [ma] >:~ [] /\ mpath >:~ [].

  Proof.
    intros.
    apply path_corr_split1 in H as (ppath0 & ppath1 & HEq & HC0 & HC1).
    apply eq_sym in HEq.
    apply app_eq_nil in HEq as [HEq0 HEq1].
    subst.
    split; auto.
  Qed.

  Lemma flushed_ready_one : forall MNm1 n MN0,
      (net_deinstr MNm1 = net_deinstr MN0 /\ flushed MN0) ->
      exists nmpath MN1,
        (MN0 =[ nmpath ]=> MN1)
        /\ (forall m, (n = m \/ ready_in m MN0) -> ready_in m MN1)
        /\ (net_deinstr MNm1 = net_deinstr MN1 /\ flushed MN1).

  Proof with (auto with LTS).
    intros.
    destruct H as (HND0 & HFN0).

    destruct (ready_in_dec n MN0).
    exists [], MN0. repeat split... intros.
    destruct H0... subst...
    rename H into HR0_not.

    destruct (ready_exists_q (NetMod.get n MN0))
      as (mpath & MS1 & TM & HF & HR & HC).

    generalize dependent MS1.
    generalize dependent MN0.
    generalize dependent MNm1.
    induction mpath; intros.
    1: kill TM...

    kill TM.
    rename T0 into TM0.
    rename T1 into TM1.
    rename N1 into MS0'.

    kill HF.
    rename H into HF_a.
    rename H0 into HF_mpath.

    apply path_corr_split_nil1 in HC as [HC_a HC_mpath].

    assert ((forall t0 v, a <> send (n, t0) v) \/ exists t0 v, a = send (n, t0) v).
    {
      destruct a; try (destruct p); simpl; try (left; intros; simpl; destruct v0; discriminate);
        try (left; intros; simpl; destruct v; discriminate).
      destruct a; try (destruct p); simpl; try (left; intros; simpl; destruct v0; discriminate);
        try (left; intros; simpl; destruct v; discriminate).
      destruct n0 as [n0 t].
      destruct (NAME.eq_dec n0 n); subst.
      (right; exists t, (MValM v); simpl; auto).
      (left; intros; simpl; destruct v0). bs. bs.
    }

    destruct H.
    - apply flush_act_available in TM0
          as (na & MN0' & TN0 & HEq & HPreserveNS0 & HPreserveF0 & HPreserveR0 & HND0'); auto.

      specialize (HND0' HFN0).

      specialize (HFN0 n) as HF0.

      assert (no_sends_in n MN0) as HNS0.
      unfold no_sends_in.  unfold flushed_in in HF0. unfold Flushed in HF0.
      destruct (NetMod.get n MN0).
      unshelve eapply (Forall_impl _ _ HF0).
      intros. simpl in *. destruct a0; auto.

      specialize (HPreserveF0 n ltac:(attac) HF0) as HF0'.

      assert (flushed MN0') as HFN0'.
      unfold flushed. intros. apply HPreserveF0...

      destruct (ready_in_dec n MN0').
      exists [na], MN0'. repeat split; eauto with LTS.
      intros. destruct H1; subst...
      rewrite HND0. assumption.
      rename H0 into HR0'_not.

      rewrite <- HEq in TM1.

      specialize (IHmpath HF_mpath HC_mpath _ _ HND0' HFN0' HR0'_not _ TM1 HR)
        as (nmpath & MN1 & TN1 & HPreserveR1 & HND1 & HF1).

      exists (na :: nmpath), MN1.
      repeat split; eauto with LTS.
      intros.
      kill H0; subst...
      rewrite HND0...

    - destruct H as [t0 [v Hn]].
      kill Hn.

      replace ( MTrans _ _ _)
        with  ((NetMod.get n MN0) =(send (n, t0) v)=> MS0')
        in TM0; auto.
      destruct (MS0') as [MQ0' M0' S0'].
      destruct (MS1) as [MQ1 M1 S1].

      eapply flush_act_available_self in TM0
          as (na & MN0' & MQ' & TN0 & HEq & HPreserveNS0 & HPreserveF0 & HPreserveR0 & HND0' & HNS0''); auto.

      specialize (HND0' HFN0).

      apply (Flushing_cont MQ') in TM1; auto.

      specialize (HFN0 n) as HF0.

      assert (no_sends_in n MN0) as HNS0.
      unfold no_sends_in.  unfold flushed_in in HF0. unfold Flushed in HF0.
      destruct (NetMod.get n MN0).
      unshelve eapply (Forall_impl _ _ HF0).
      intros. simpl in *. destruct a; auto.

      specialize (HPreserveF0 n HF0) as HF0'.

      assert (flushed MN0') as HFN0'.
      unfold flushed. intros. apply HPreserveF0...

      destruct (ready_in_dec n MN0').
      exists [na], MN0'. repeat split; eauto with LTS.
      intros. destruct H0; subst...
      rewrite HND0...
      rename H into HR0'_not.

      rewrite <- HEq in TM1.

      specialize (IHmpath HF_mpath HC_mpath _ _ HND0' HFN0' HR0'_not _ TM1 HR)
        as (nmpath & MN1 & TN1 & HPreserveR1 & HND1 & HF1).

      exists (na :: nmpath), MN1.
      repeat split; eauto with LTS.
      intros.
      kill H; subst...
      rewrite HND0...
  Qed.


  Theorem semi_flush : forall [chans] MN0,
      (forall n, not (In n chans) -> no_sends_in n MN0) ->
      True ->
      exists nmpath MN1,
        (MN0 =[nmpath]=> MN1)
        /\ no_sends MN1
        /\ True.

  Proof.
    intros chans.
    apply net_induction.
    apply flush_send_one.
  Qed.


  Lemma flush_nosend' : forall [chans] MN0,
      (forall n, not (In n chans) -> flushed_in n MN0) ->
      no_sends MN0 ->
      exists nmpath MN1,
        (MN0 =[nmpath]=> MN1)
        /\ flushed MN1
        /\ no_sends MN1.

  Proof.
    intros chans.
    apply net_induction.
    apply flush_nosend_one.
  Qed.


  Lemma flushed_ready : forall [chans] MN0,
      (forall n, not (In n chans) -> ready_in n MN0) ->
      (net_deinstr MN0 = net_deinstr MN0 /\ flushed MN0) ->
      exists nmpath MN1,
        (MN0 =[nmpath]=> MN1)
        /\ ready_net MN1
        /\ (net_deinstr MN0 = net_deinstr MN1 /\ flushed MN1).

  Proof.
    intros chans.
    intros MN0.
    specialize (flushed_ready_one MN0) as HI.
    apply (net_induction HI).
  Qed.


  Lemma flushed_ready_instr : forall [MN],
      flushed MN ->
      ready_net MN ->
      exists I, MN = net_instr I (net_deinstr MN).

  Proof.
    intros MN HF HR.

    unfold flushed in HF.
    unfold ready_net in HR.
    unfold flushed_in in HF.
    unfold ready_in in HR.

    unfold net_instr.
    unfold net_instr_n.

    assert (forall n, {MS : MQued | NetMod.get n MN = MS  /\
                                      match MS with
                                      | mq MQ M _ =>
                                          MQ_Clear MQ /\ ready M
                                      end
           }).
    {
      intros.
      destruct (NetMod.get n MN) as [MQ M S] eqn:HI.
      unshelve eapply (exist _ (mq MQ M &S) _). repeat split.
      specialize (HF n). rewrite HI in HF. apply HF.
      specialize (HR n). rewrite HI in HR. apply HR.
    }

    unshelve eexists (fun n => match (H n) with
                               | exist _ MQ P => _
                               end

      ).
    destruct P.
    destruct MQ.
    destruct H1.
    constructor.
    apply (exist _ l H1).  apply (exist _ m H2).

    assert ((NetMod.init (fun n => match NetMod.get n MN with
                                   | mq _ _ s => s
                                   end
            )) = net_deinstr MN).
    {
      unfold net_deinstr.
      apply NetMod.extensionality.
      intros.
      rewrite NetMod.init_get.
      rewrite NetMod.get_map.
      unfold deinstr.
      specialize (H n).
      destruct H as [MS [HEq HMatch]].
      subst.
      destruct (NetMod.get n MN).
      destruct HMatch as (HClear & HReady).
      destruct p.
      eattac.
    }

    rewrite <- H0.

    apply NetMod.extensionality; intros.
    repeat (rewrite NetMod.get_map).
    rewrite NetMod.init_get.
    destruct (H n).
    destruct a.
    destruct x.
    rewrite e.
    destruct y.
    unfold instr.
    simpl.
    reflexivity.
  Qed.


  Lemma flushed_in_no_sends : forall [n N],
      flushed_in n N -> no_sends_in n N.

  Proof.
    intros n N HF.
    unfold no_sends_in. unfold flushed_in in HF.
    unfold NoTrSend. unfold Flushed in HF.
    destruct (NetMod.get n N).
    attac.
  Qed.

  #[export] Hint Immediate flushed_in_no_sends : LTS.


  (* Why do I have to do it? *)
  Lemma not_in_app_inv : forall [A] (a : A) l0 l1,
      not (In a (l0 ++ l1)) ->
      not (In a l0) /\ not (In a l1).

  Proof.
    intros.
    unfold not in *.
    split; intros.
    - apply H. clear H.
      induction l0.
      + inversion H0.
      + kill H0.
        * now left.
        * right.
          apply IHl0.
          assumption.
    - apply H. clear H.
      induction l0.
      + simpl.
        assumption.
      + simpl.
        right.
        assumption.
  Qed.


  (** Any network can be led to a freshly instrumented state. *)
  Theorem Net_flush_exists : forall [chans] (MN0 : MNet),
      (forall n, not (In n chans) -> flushed_in n MN0) ->
      (forall n, not (In n chans) -> ready_in n MN0) ->
      exists mnpath I1 (N1 : PNet),
        (MN0 =[ mnpath ]=> net_instr I1 N1).

  Proof.
    intros chans MN0 HF0 HRd0. intros.

    assert (forall n, not (In n chans) -> no_sends_in n MN0) as HS0.
    intros.
    specialize (HF0 n H). clear H.
    apply flushed_in_no_sends. assumption.

    destruct (semi_flush MN0 HS0) as (mnpath0 & MN1 & T0 & HSN0 & HRN0); auto.

    assert ((forall n, not (In n (path_particip mnpath0 ++ chans)) -> flushed_in n MN1)) as HF1.
    {
      intros.
      apply not_in_app_inv in H as (NI_part & NI_chans).
      specialize (path_particip_stay NI_part T0) as HS.
      unfold flushed_in.

      rewrite <- HS.
      apply HF0. apply NI_chans.
    }

    destruct (flush_nosend' MN1 HF1 HSN0)
      as (mnpath1 & MN2 & T1 & HFN2 & HNS2).


    assert ((forall n, not (In n (path_particip mnpath0 ++ path_particip mnpath1 ++ chans)) -> ready_in n MN2)) as HRd2.
    {
      intros.
      apply not_in_app_inv in H as (NI_part0 & H).
      apply not_in_app_inv in H as (NI_part1 & NI_chans).
      specialize (path_particip_stay NI_part0 T0) as ?.
      specialize (path_particip_stay NI_part1 T1) as ?.
      unfold ready_in. rewrite <- H0. rewrite <- H.
      apply HRd0. apply NI_chans.
    }

    destruct (flushed_ready MN2 HRd2 (conj eq_refl HFN2))
      as (mnpath2 & MN3 & T2 & HRd3 & HND3 & HF3).

    destruct (flushed_ready_instr HF3 HRd3)
      as (I & Eq).

    exists (mnpath0 ++ mnpath1 ++ mnpath2).
    exists &I, (net_deinstr MN3).

    hrewrite MN3 in * |- .
    eauto with LTS.
  Qed.


  Lemma Net_corr_extraction : forall [MN0 MN1 : MNet] [mnpath],
      (MN0 =[ mnpath ]=> MN1) ->
      forall n,
      exists mpath ppath,
        Path_of n mnpath mpath
        /\ (NetMod.get n (net_deinstr MN0) =[ ppath ]=> NetMod.get n (net_deinstr MN1))
        /\ mpath >:~ ppath.

  Proof.
    intros *.
    intros TN n.

    destruct (path_of_exists n mnpath) as (mpath & HPo).
    specialize (path_of_ptrans HPo TN) as TM.

    unfold net_deinstr.
    do 2 (rewrite NetMod.get_map).
    assert (deinstr (NetMod.get n MN0) =[ MPath_to_PPath mpath ]=>
              deinstr (NetMod.get n MN1)
              ).
    {
      destruct (NetMod.get n MN0) as [MQ0 M0 [I0 P0 O0]].
      destruct (NetMod.get n MN1) as [MQ1 M1 [I1 P1 O1]].
      eauto using corr_extraction.
    }

    exists mpath, (MPath_to_PPath mpath).
    repeat split; auto.
  Qed.


  Lemma Net_Vis_corr_psend : forall [n n' : Name] [t0 v] [MN0 MN1 : MNet],
      (NVTrans n (MActP (Send (n', t0) v)) MN0 MN1) ->
      net_deinstr MN0 = net_deinstr MN1.

  Proof.
    intros *. intros T.

    kill T.
    kill H.

    unfold net_deinstr in *.
    rewrite NetMod.put_map in *.
    kill TP.

    assert (deinstr (mq MQ M (pq &I P ((n', t0, v) :: &O))) = deinstr (NetMod.get n MN0))
      by (rewrite <- H2; reflexivity).

    clear H2.
    simpl in *.
    do 2 (hsimpl). rewrite <- app_assoc. simpl.

    (* This line is mandatory. `Set Printing All` helps here. *)
    (* Set Printing All. *)
    unfold NChan in *.
    rewrite H.

    unfold deinstr.

    rewrite <- (NetMod.put_map (fun _ S =>
                                 match S with
                                 | mq _ _ _ => _
                                 end
      )).
    rewrite NetMod.put_get_eq.
    reflexivity.
  Qed.


  Lemma Net_Vis_corr_precv : forall [n n' : Name] [t0 v] [MN0 MN1 : MNet],
      (NVTrans n (MActP (Recv (n', t0) v)) MN0 MN1) ->
      net_deinstr MN0 = net_deinstr MN1.

  Proof.
    intros *. intros T.

    kill T.
    kill H.

    unfold net_deinstr in *.
    rewrite NetMod.put_map in *.

    assert (deinstr (mq MQ M1 S1) = NetMod.get n (NetMod.map (fun _ S => deinstr S) MN0)).

    simpl in *.

    kill TP.
    kill HEnq.

    rewrite NetMod.get_map.
    rewrite <- H3.
    simpl.

    rewrite <- app_assoc. simpl.
    reflexivity.

    rewrite H.
    rewrite NetMod.put_get_eq.
    reflexivity.
  Qed.


  Lemma Net_Vis_corr_ptau : forall [n : Name] [MN0 MN1 : MNet],
      (NVTrans n (MActP Tau) MN0 MN1) ->
      (NVTrans n Tau (net_deinstr MN0) (net_deinstr MN1)).

  Proof.
    intros *. intros T.

    kill T.
    kill H.

    unfold net_deinstr.
    rewrite NetMod.put_map.
    constructor.
    rewrite NetMod.get_map.
    rewrite <- H0. clear H0.
    simpl. clear MN0 n.
    destruct S0.
    destruct S1.
    kill TP; eattac.
  Qed.


  Lemma Net_Vis_corr_send : forall [n n' : Name] [t0 v] [MN0 MN1 : MNet],
      (NVTrans n (MActT (Send (n', t0) v)) MN0 MN1) ->
      (NVTrans n (Send (n', t0) v) (net_deinstr MN0) (net_deinstr MN1)).

  Proof.
    intros *. intro T.
    kill T.
    kill H.

    unfold net_deinstr.
    rewrite NetMod.put_map.
    constructor.
    rewrite NetMod.get_map.
    rewrite <- H3. clear H3.
    simpl. clear MN0 n.
    destruct S0; eattac.
  Qed.


  Lemma Net_Vis_corr_recv : forall [n n' : Name] [t0 v] [MN0 MN1 : MNet],
      (NVTrans n (MActT (Recv (n', t0) v)) MN0 MN1) ->
      (NVTrans n (Recv (n', t0) v) (net_deinstr MN0) (net_deinstr MN1)).

  Proof.
    intros *. intro T.
    kill T.
    kill H.

    unfold net_deinstr.
    rewrite NetMod.put_map.
    constructor.
    rewrite NetMod.get_map.
    rewrite <- H2. clear H2.
    simpl.
    clear MN0 n.

    destruct S0; hsimpl; eattac.
  Qed.


  Lemma Net_Vis_corr_tau : forall [n : Name] [MN0 MN1 : MNet],
      (NVTrans n (MActT Tau) MN0 MN1) ->
      net_deinstr MN0 = net_deinstr MN1.

  Proof.
    intros.
    kill H.
    kill H0.
  Qed.


  Lemma Net_Vis_corr_mon : forall [n : Name] [ma] [MN0 MN1 : MNet],
      (NVTrans n (MActM ma) MN0 MN1) ->
      net_deinstr MN0 = net_deinstr MN1.

  Proof.
    intros.
    kill H.

    unfold net_deinstr in *.
    rewrite NetMod.put_map in *.
    destruct S as [MQ M S].

    assert (deinstr (mq MQ M &S) = NetMod.get n (NetMod.map (fun _ S => deinstr S) MN0)).

    simpl in *.

    rewrite NetMod.get_map.
    unfold deinstr.

    destruct (NetMod.get n MN0).
    destruct S.
    destruct p.
    kill H0; hsimpl; eattac.

    (* TODO GOAL EXPLOSION EXAMPLE: himpl in H *)
    rewrite H.
    rewrite NetMod.put_get_eq.
    reflexivity.
  Qed.

  #[export] Hint Immediate
    Net_Vis_corr_mon
    Net_Vis_corr_tau
    Net_Vis_corr_recv
    Net_Vis_corr_send
    Net_Vis_corr_ptau
    Net_Vis_corr_precv
    Net_Vis_corr_psend : LTS.


  Lemma Net_path_corr1 : forall [ma] [MN0 MN1 : MNet],
      (MN0 =(ma)=> MN1) ->
      exists pnpath,
        (net_deinstr MN0 =[pnpath]=> net_deinstr MN1).

  Proof with (eauto with LTS).
    intros.

    kill H.
    - destruct a; try (destruct p); try (destruct n0 as [n0 t0]); try (contradiction).
      + apply Net_Vis_corr_psend in H1.
        rewrite H1.
        exists []...
      + apply Net_Vis_corr_precv in H1.
        rewrite H1.
        exists []...
      + apply Net_Vis_corr_ptau in H1.
        eexists [NTau _ _].
        apply path_seq0.
        constructor.
        * kill H1.
          apply eq_refl.
        * apply H1.
      + kill H1.
        kill H.
      + destruct a; kill H0.
        apply Net_Vis_corr_mon in H1.
        rewrite H1.
        exists []...
    - destruct v.
      + apply Net_Vis_corr_mon in H0.
        apply Net_Vis_corr_mon in H1.
        rewrite H0.
        rewrite H1.
        exists []...
      + apply Net_Vis_corr_send in H0.
        apply Net_Vis_corr_recv in H1.
        eexists [NComm _ _ _ _]...
  Qed.


  Lemma net_deinstr_act [MN0 MN1 : MNet] [na] :
    (MN0 =(na)=> MN1) ->
    match MNAct_to_PNAct na with
    | Some a => net_deinstr MN0 =(a)=> net_deinstr MN1
    | None => net_deinstr MN0 = net_deinstr MN1
    end.

  Proof.
    intros.
    kill H.
    - destruct_ma &a; doubt; simpl; eattac.
    - destruct v.
      + hsimpl in *; hsimpl in |- *.
        apply NetMod.extensionality; intros.
        unfold net_deinstr in *; simpl in *.
        hsimpl in |- *.
        smash_eq_on n0 n n'; subst; hsimpl in *; hsimpl in |- *; auto.
        all: unfold deinstr in *; destruct P; hsimpl; attac.
      + simpl in *.
        enough (exists N, net_deinstr MN0 ~( n @ Send (n', &t) v )~> N /\ N ~( n' @ Recv (n, &t) v )~> net_deinstr MN1).
        {
          destruct H as [N [? ?]].
          econstructor; eauto.
        }
        kill H0.
        unfold net_deinstr in *; simpl in *.
        hsimpl in |- *.
        kill H.
        destruct S0 as [I P O].
        exists (NetMod.put n (pq (&I ++ MQ_r MQ) P (MQ_s MQ ++ &O)) (net_deinstr MN0)).
        split.
        * constructor.
          unfold net_deinstr, deinstr in *.
          attac.
        * unfold net_deinstr, deinstr in *.
          hsimpl in *. hsimpl in |- *.
          constructor.
          destruct P0 as [I0 P0 O0].
          smash_eq n' n; hsimpl; attac.
  Qed.

  #[export] Hint Immediate net_deinstr_act : LTS.


  Lemma net_deinstr_act_do [MN0 MN1] [ma a] :
    MNAct_to_PNAct ma = Some a ->
    (MN0 =(ma)=> MN1) ->
    (net_deinstr MN0 =(a)=> net_deinstr MN1).
  Proof.
    intros.
    specialize (net_deinstr_act `(MN0 =(_)=> _)) as ?.
    rewrite `(_ = Some _) in *.
    auto.
  Qed.


  Lemma net_deinstr_act_skip [MN0 MN1] [ma] :
    MNAct_to_PNAct ma = None ->
    (MN0 =(ma)=> MN1) ->
    net_deinstr MN0 = net_deinstr MN1.
  Proof.
    intros.
    specialize (net_deinstr_act `(MN0 =(_)=> _)) as ?.
    rewrite `(_ = None) in *.
    auto.
  Qed.

  #[export] Hint Resolve net_deinstr_act_do net_deinstr_act_skip : LTS.


  (** Process path is replicable under deinstrumentation *)
  Theorem Net_path_corr : forall [mnpath] [MN0 MN1 : MNet],
      (MN0 =[ mnpath ]=> MN1) ->
      exists pnpath,
        (net_deinstr MN0 =[pnpath]=> net_deinstr MN1).

  Proof.
    induction mnpath; intros.
    kill H.
    exists []. constructor.

    kill H.
    rename T0 into TNM0.
    rename T1 into TNM1.
    rename N1 into MN0'.

    destruct (Net_path_corr1 TNM0) as (pnpath0 & TN0).
    apply (IHmnpath) in TNM1 as (pnpath1 & TN1).

    exists (pnpath0 ++ pnpath1).
    eauto with LTS.
  Qed.


  (** Soundness of network transparency *)
  Theorem Net_Transp_soundness : forall {mnpath0} {I0} {N0 : PNet} {MN1 : MNet},
      (net_instr I0 N0 =[ mnpath0 ]=> MN1) ->
      exists mnpath1 pnpath I2 N2,
        (MN1 =[ mnpath1 ]=> net_instr I2 N2)
        /\ (N0 =[ pnpath ]=> N2).

  Proof.
    intros *.
    intros NTM0.

    assert (forall n, not (In n (path_particip mnpath0)) -> flushed_in n MN1) as HF1.
    {
      intros.
      specialize (path_particip_stay H NTM0) as ?.
      unfold flushed_in. rewrite <- H0.
      unfold net_instr in *.
      rewrite NetMod.get_map in *.
      rewrite H0.
      unfold Flushed.
      unfold net_instr_n in *.
      destruct (I0 n).
      rewrite <- H0.
      simpl.
      destruct m.
      simpl. auto.
    }

    assert (forall n : Name, ~ In n (path_particip mnpath0) -> ready_in n MN1) as HRd1.
    {
      intros.
      specialize (path_particip_stay H NTM0) as ?.
      unfold ready_in. rewrite <- H0.
      unfold net_instr in *.
      rewrite NetMod.get_map in *.
      rewrite H0.
      unfold ready_q.
      unfold net_instr_n in *.
      destruct (I0 n).
      rewrite <- H0.
      simpl.
      destruct m0.
      simpl. auto.
    }

    specialize (path_particip_stay) as ?.
    destruct (Net_flush_exists MN1 HF1 HRd1) as (mnpath1 & I1 & N2 & NTM1).

    assert (net_instr I0 N0 =[ mnpath0 ++ mnpath1 ]=> net_instr I1 N2) as NTM by attac.

    consider (exists pnpath, '' (net_instr I0 N0) =[ pnpath ]=> '' (net_instr I1 N2)) by eauto using Net_path_corr.

    exists mnpath1, pnpath, I1, N2.
    attac.
  Qed.


  (** Completeness over NV: tau case. *)
  Lemma Net_Vis_Transp_completeness_tau : forall (I : mon_assg) {n : Name} {N0 N1 : PNet},
      (NVTrans n Tau N0 N1) ->
      (NVTrans n (MActP Tau) (net_instr I N0) (net_instr I N1)).

  Proof.
    intros.
    inversion H. subst.
    destruct (&I n) as (MQ & M) eqn:HI.
    apply (Transp_completeness_tau MQ M) in H0.
    repeat constructor; auto.

    unfold net_instr.
    unfold net_instr_n.
    rewrite NetMod.put_map.
    constructor.
    rewrite NetMod.get_map.
    unfold instr. simpl.
    rewrite HI.
    assumption.
  Qed.


  Lemma mactm_invariant_deinstr : forall [n ma MN0 MN1],
      (MN0 =(NTau n (MActM ma))=> MN1) ->
      net_deinstr MN0 = net_deinstr MN1.

  Proof.
    intros *. intros TN.
    kill TN.
    now apply Net_Vis_corr_mon in H0.
  Qed.


  Lemma mcomm_invariant_deinstr : forall [n n' t0] [m : Msg] [MN0 MN1 : MNet],
      (MN0 =(NComm n n' t0 (MValM m))=> MN1) ->
      net_deinstr MN0 = net_deinstr MN1.

  Proof.
    intros *. intros TN.
    kill TN.
    apply Net_Vis_corr_mon in H.
    apply Net_Vis_corr_mon in H0.
    etransitivity; eauto.
  Qed.


  Lemma net_instr_flushed : forall I N, flushed (net_instr I N).

  Proof.
    intros.
    unfold net_instr.
    unfold flushed.
    unfold net_instr_n.
    unfold flushed_in.
    intros.
    rewrite NetMod.get_map.
    destruct (&I n).
    destruct m.
    simpl.
    assumption.
  Qed.

  #[export] Hint Resolve net_instr_flushed : LTS.


  Lemma net_instr_ready_net : forall I N, ready_net (net_instr I N).

  Proof.
    intros.
    unfold net_instr.
    unfold ready_net.
    unfold net_instr_n.
    unfold ready_in.
    intros.
    rewrite NetMod.get_map.
    destruct (&I n).
    destruct m0.
    simpl.
    assumption.
  Qed.

  #[export] Hint Resolve net_instr_ready : LTS.


  Lemma get_instr : forall [n] N [I MQ M],
      I n = (MQ, M) ->
      instr MQ M (NetMod.get n N) = NetMod.get n (net_instr I N).

  Proof.
    intros.
    unfold net_instr in *.
    unfold net_instr_n in *.
    unfold instr in *.
    rewrite NetMod.get_map.
    rewrite H.
    reflexivity.
  Qed.


  (** If a node can perform a sequence of flushing and nil-corr actions, then the network can too. *)
  Lemma admin_path_available1' : forall
      [ma] [MQ0 M0 S0] [MQ1 M1 S1] n I0 N0,
      [ma] >:~ [] ->
      Flushing_act ma ->
      (mq MQ0 M0 S0 =(ma)=> mq MQ1 M1 S1) ->
      exists nmpath I1 MQ',
        (NetMod.put n (mq MQ0 M0 S0) (net_instr I0 N0)
         =[nmpath]=>
           NetMod.put n (mq (MQ1 ++ MQ') M1 S1) (net_instr I1 N0)
        )
        /\ MQ_Clear MQ'.

  Proof.
    intros *. intros HC HF TM.

    kill TM; kill HC; kill HF; try (destruct n0 as [n0 t0]).
    - unshelve eexists [NComm n n0 t0 _]. apply (MValM msg).

      assert (NetMod.get n (NetMod.put n (mq MQ1 M0 S1) (net_instr I0 N0))
              =(MActM (Send (n0, t0) msg))=>
                (mq MQ1 M1 S1)
             ).
      repeat (rewrite NetMod.get_put_eq).
      constructor. assumption.
      apply NT_Vis in H0.
      rewrite NetMod.put_put_eq in H0.
      rename H0 into NT_send.

      destruct (NetMod.get n0 (NetMod.put n (mq MQ1 M1 S1) (net_instr I0 N0)))
        as [MQr Mr Sr] eqn:HeqR.

      assert (NetMod.get n0 (NetMod.put n (mq MQ1 M1 S1) (net_instr I0 N0))
              =(MActM (Recv (n, t0) msg))=>
                (mq (MQr ++ [EvRecv (n, t0) msg]) Mr Sr)
             ).
      rewrite HeqR.
      constructor.

      apply NT_Vis in H0.
      rename H0 into NT_recv.

      destruct (NAME.eq_dec n0 n); subst.
      + rewrite NetMod.put_put_eq in NT_recv.
        rewrite NetMod.get_put_eq in HeqR.
        kill HeqR.
        exists I0, [EvRecv (n, t0) msg].

        split; repeat constructor.

        apply path_seq0.

        replace (MActM _) with (send (n, t0) (MValM msg)) in NT_send; auto.
        replace (MActM _) with (recv (n, t0) (MValM msg)) in NT_recv; auto.

        apply (NT_Comm NT_send NT_recv).

      + rewrite NetMod.put_put_neq in NT_recv; auto.
        rewrite NetMod.get_put_neq in HeqR; auto.

        assert (MQ_Clear (MQr ++ [EvRecv (n, t0) msg])) as HMQr.
        {
          specialize (net_instr_flushed I0 N0 n0) as ?.
          unfold flushed_in in H0.
          rewrite HeqR in H0.
          apply Forall_app; split; attac.
        }

        assert (ready Mr) as HMr.
        {
          specialize (net_instr_ready_net I0 N0 n0) as HR.
          unfold ready_in in HR.
          rewrite HeqR in HR.
          apply HR...
        }

        pose (
            fun n' =>
              if NAME.eqb n0 n'
              then (exist _ (MQr ++ [EvRecv (n, t0) msg]) HMQr, exist _ Mr HMr)
              else I0 n'
          ) as I1; simpl.

        exists I1, [].

        rewrite app_nil_r.
        split; try constructor.

        apply path_seq0.
        replace (MActM _) with (send (n0, t0) (MValM msg)) in NT_send; auto.
        replace (MActM _) with (recv (n, t0) (MValM msg)) in NT_recv; auto.

        specialize (NT_Comm NT_send NT_recv) as ?.

        assert ( (net_instr I1 N0) = (NetMod.put n0 (mq (MQr ++ [EvRecv (n, t0) msg]) Mr Sr) (net_instr I0 N0))).
        {
          unfold net_instr.
          specialize (conscious_replace n0
                        (net_instr_n I0)
                        (fun n' S' => instr (exist _ (MQr ++ [EvRecv (n, t0) msg]) HMQr) (exist _ Mr HMr) S')
                        N0
                     ) as Kek.
          unfold instr in Kek.
          simpl in Kek.

          assert (NetMod.get n0 N0 = Sr) as HeqSr.
          {
            unfold net_instr in HeqR.
            unfold net_instr_n in HeqR.
            rewrite NetMod.get_map in HeqR.
            destruct (I0 n0).
            unfold instr in HeqR.
            destruct (NetMod.get n0 N0).
            kill HeqR.
          }

          subst I1.

          rewrite <- HeqSr.
          rewrite <- Kek.
          unfold net_instr_n.

          apply NetMod.extensionality.
          intros.
          repeat (rewrite NetMod.get_map).

          destruct (NAME.eqb n0 n2) eqn:HEq01; auto.
        }

        rewrite H1.
        auto.
    - exists [NTau n (MActM Tau)].
      exists I0, [].

      rewrite app_nil_r.
      split; try constructor.

      apply path_seq0.
      constructor.
      constructor.

      assert (NetMod.get n (NetMod.put n (mq (EvRecv (n0, t0) v :: MQ1) M0 S1) (net_instr I0 N0))
              =(MActM Tau)=>
                (mq MQ1 M1 S1)
             ).
      repeat (rewrite NetMod.get_put_eq).
      constructor. assumption.

      apply (NT_Vis) in H0.
      rewrite NetMod.put_put_eq in H0.
      apply H0.

    - exists [NTau n (MActM Tau)].
      exists I0, [].

      rewrite app_nil_r.
      split; try constructor.

      apply path_seq0.
      constructor.
      constructor.

      assert (NetMod.get n (NetMod.put n (mq (MQ1) M0 S1) (net_instr I0 N0))
              =(MActM Tau)=>
                (mq MQ1 M1 S1)
             ).
      repeat (rewrite NetMod.get_put_eq).
      constructor. assumption.

      apply (NT_Vis) in H0.
      rewrite NetMod.put_put_eq in H0.
      auto.

    - exists [NTau n (MActP (Recv (n0, t0) v))].
      exists I0, [].

      rewrite app_nil_r.
      split; try constructor.

      apply path_seq0.
      constructor.
      constructor.

      assert (NetMod.get n (NetMod.put n (mq (TrRecv (n0, t0) v :: MQ1) M0 S0) (net_instr I0 N0))
              =(MActP (Recv (n0, t0) v))=>
                (mq MQ1 M1 S1)
             ).
      repeat (rewrite NetMod.get_put_eq).
      constructor; assumption.

      apply (NT_Vis) in H0.
      rewrite NetMod.put_put_eq in H0.
      auto.
  Qed.



  (** If a node can perform a sequence of flushing and nil-corr actions, then the network can too. *)
  Lemma admin_path_available' : forall
      [mpath] [MQ0 M0 S0] [MQ1 M1 S1] n I0 N0,
      mpath >:~ [] ->
      Forall Flushing_act mpath ->
      (mq MQ0 M0 S0 =[mpath]=> mq MQ1 M1 S1) ->
      exists nmpath I1 MQ',
        (NetMod.put n (mq MQ0 M0 S0) (net_instr I0 N0)
         =[nmpath]=>
           NetMod.put n (mq (MQ1 ++ MQ') M1 S1) (net_instr I1 N0)
        )
        /\ MQ_Clear MQ'.

  Proof with (eauto with LTS).
    induction mpath; intros *; intros HC HF TM.
    kill TM. kill HC. kill HF.

    exists [], I0, []...
    repeat split. rewrite app_nil_r. constructor. constructor.

    apply path_split1 in TM as ([MQ0' M0' S0'] & TM0 & TM1).
    apply path_corr_split_nil1 in HC as (HC0 & HC1).
    inversion HF. subst. rename H1 into HF0. rename H2 into HF1.

    destruct (admin_path_available1' n I0 N0 HC0 HF0 TM0)
      as (nmpath0 & I0' & MQ'0' & TNM0 & HCMQ').

    assert (mq (MQ0' ++ MQ'0') M0' S0' =[ mpath ]=> mq (MQ1 ++ MQ'0') M1 S1) by eauto using Flushing_cont.

    specialize IHmpath with (MQ0 := MQ0' ++ MQ'0')(n := n)(I0:=I0')(N0:=N0).
    edestruct IHmpath as (nmpath1 & I1 & MQ1' & TNM1 & HMQ1); eauto.

    exists (nmpath0 ++ nmpath1), I1, (MQ'0' ++ MQ1').
    rewrite app_assoc.
    attac.
  Qed.


  (** If a node can perform a sequence of flushing and nil-corr actions, then the network can too. *)
  Lemma admin_path_available1 : forall
      [ma] [MQ0 M0 S0] [MQ1 M1 S1] n MN0,
      [ma] >:~ [] ->
      Flushing_act ma ->
      (mq MQ0 M0 S0 =(ma)=> mq MQ1 M1 S1) ->
      flushed MN0 ->
      exists nmpath MQ' MN1,
        (NetMod.put n (mq MQ0 M0 S0) MN0
         =[nmpath]=>
           NetMod.put n (mq (MQ1 ++ MQ') M1 S1) MN1
        )
        /\ flushed MN1
        /\ net_deinstr MN0 = net_deinstr MN1
        /\ MQ_Clear MQ'.

  Proof with eattac.
    intros *. intros HC HF TM HFN0.

    kill TM; kill HC; kill HF; try (destruct n0 as [n0 t0]).
    - unshelve eexists [NComm n n0 t0 _]. apply (MValM msg).

      hsimpl in *.
      smash_eq n n0.
      + exists [EvRecv (n, t0) msg], MN0.
        hsimpl; hsimpl; eattac.
        eapply NTrans_Comm_eq_inv. hsimpl.
        eexists _, _. eattac; constructor. eattac.

      (* + eexists [], _. *)
      (* repeat split. TODO bug report? why does this instantiate evar? *)
      + destruct (NetMod.get n0 MN0) as [MQr0 Mr0 Sr0] eqn:?.
        eexists [], (NetMod.put n0 (mq (MQr0 ++ [EvRecv (n, t0) msg]) Mr0 Sr0) MN0).
        eattac.
        * destruct M1. hsimpl in |- *.
          eapply NTrans_Comm_neq_inv; auto.
          ltac1:(autorewrite with LTS in * ).
          exists (mq MQ1 {| handle := handle0; state := state0 |} S1).
          exists (mq (MQr0 ++ [EvRecv (n, t0) msg]) Mr0 Sr0).
          eattac.
          rewrite NetMod.put_put_neq; eattac.

        * unfold flushed, flushed_in, Flushed in *.
          intros.
          specialize (HFN0 n1).
          smash_eq n n0 n1; ltac1:(autorewrite with LTS_concl); attac.
        * unfold net_deinstr in *.
          apply NetMod.extensionality; intros.
          smash_eq n0 n1; attac.
          hsimpl in |- *.
          rewrite Heqm.
          attac.
    - exists [NTau n (MActM Tau)].
      exists [], MN0.

      hsimpl in |- *. attac.
      constructor; attac.
      hsimpl in |- *.
      eapply NVTrans_inv. eattac.

    - exists [NTau n (MActM Tau)].
      exists [], MN0.
      attac.

    - exists [NTau n (MActP (Recv (n0, t0) v))].
      exists [], MN0.

      hsimpl in |- *.
      constructor; attac. (* TODO why doesn't this click? *)
      hsimpl in |- *.
      eapply NTrans_Tau_inv; eattac. eexists _. eattac.
      constructor; eattac. (* WTF? *)
  Qed.


  (** If a node can perform a sequence of flushing and nil-corr actions, then the network can too. *)
  Lemma admin_path_available : forall
      [mpath] [MQ0 M0 S0] [MQ1 M1 S1] n MN0,
      mpath >:~ [] ->
      Forall Flushing_act mpath ->
      (mq MQ0 M0 S0 =[mpath]=> mq MQ1 M1 S1) ->
      flushed MN0 ->
      exists nmpath MQ' MN1,
        (NetMod.put n (mq MQ0 M0 S0) MN0
         =[nmpath]=>
           NetMod.put n (mq (MQ1 ++ MQ') M1 S1) MN1
        )
        /\ flushed MN1
        /\ net_deinstr MN0 = net_deinstr MN1
        /\ MQ_Clear MQ'.

  Proof with eattac.
    induction mpath; intros * HC HF TM HFN0.
    1: exists [], [], MN0...

    apply path_split1 in TM as ([MQ0' M0' S0'] & TM0 & TM1).
    apply path_corr_split_nil1 in HC as (HC0 & HC1).
    inversion HF. subst. rename H1 into HF0. rename H2 into HF1. clear HF.

    destruct (admin_path_available1 n MN0 HC0 HF0 TM0 HFN0)
      as (nmpath0 & MQ'0' & MN0' & TNM0 & HFN0' & HNDI0 & HCMQ').

    apply (Flushing_cont MQ'0') in TM1; auto.

    specialize (IHmpath _ _ _ _ _ _ n MN0' HC1 HF1 TM1 HFN0')
      as (nmpath1 & MQ1' & MN1 & TNM1 & HFN1 & HNDI1 & HMQ1).

    exists (nmpath0 ++ nmpath1), (MQ'0' ++ MQ1'), MN1...
    rewrite app_assoc in *. eattac.
  Qed.


  Lemma Transp_completeness_send_old : forall [n v] [S0 S1] MQ0 M0,
      (S0 =( Send n v )=> S1) -> exists mpath M1,
      (instr MQ0 M0 S0 =[MActP (Send n v) :: mpath ++ [MActT (Send n v)]]=> (mq [] M1 S1))
      /\ mpath >:~ []
      /\ Forall Flushing_act mpath.

  Proof.
    intros.
    specialize (Transp_completeness_send_instr MQ0 M0 H) as TM.
    unfold flush_path in *.
    unfold instr in *.
    exists (mk_flush_path (proj1_sig MQ0) (proj1_sig M0)).
    exists (handle_Mr (TrSend n v) (plain flush_Mr MQ0 M0)).
    eattac.
  Qed.


  Lemma prepare_send : forall I0 [N0 : PNet] [n n' v S1],
      (NetMod.get n N0 =(send n' v)=> S1) ->
      exists mnpath I1 MQ1 M1 MN1,
        (net_instr I0 N0 =[mnpath]=> MN1)
        /\ NVTrans n (send n' (MValP v)) MN1 (NetMod.put n (mq MQ1 M1 S1) (net_instr I1 N0))
        /\ N0 = net_deinstr MN1
        /\ MQ_Clear MQ1.

  Proof.
    intros *. intros T.

    destruct (I0 n) as (MQ0_ & M0_) eqn:HI0.

    destruct (Transp_completeness_send_old MQ0_ M0_ T)
      as (mpath_flush & M1 & TM & HC0 & HF0).

    apply path_split1 in TM as (MS_sentp & TM_sendp & TM).
    apply path_split in TM as (MS_flush & TM_flush & TM_sendm).

    rewrite (get_instr N0 HI0) in TM_sendp.

    specialize (NT_Vis TM_sendp) as TNV_sendp.
    assert (ia (MActP (Send n' v))) by constructor.
    specialize (NT_Tau ltac:(eauto) TNV_sendp) as TNM_sendp.

    specialize (NV_invariant TNV_sendp) as WTF.

    destruct MS_sentp as [MQ_sentp M_sendp S_sentp].
    destruct MS_flush as [MQ_flush M_flush S_flush].

    destruct (admin_path_available' n I0 N0 HC0 HF0 TM_flush)
      as (mnpath & I1 & MQ' & TMN & HMQ').

    exists ((NTau n (MActP (Send n' v))) :: mnpath).

    exists I1, MQ'.
    hsimpl in *.

    exists {|handle:=h; state:=h (TrSend n' v) s|}.
    eexists (NetMod.put n (mq (TrSend n' v :: MQ') ({|handle:=h; state := MRecv s|}) _) (net_instr I1 N0)).

    eattac.
    - eapply NVTrans_inv.
      eattac.
    - apply NetMod.extensionality.
      intros.
      unfold net_deinstr.
      smash_eq n n0.
      + rewrite NetMod.put_map.
        rewrite NetMod.get_put_eq.
        hsimpl in |- *.
        kill T.
        attac.
      + unfold net_instr, net_instr_n.
        hsimpl in |- *.
        destruct (I1 n0).
        hsimpl; attac.
  Qed.

  Lemma Transp_completeness_recv_old : forall [n v] [S0 S1] MQ0 M0,
      MQ_Clear MQ0 ->
      (S0 =( Recv n v )=> S1) ->
      exists mpath M1,
        (mq MQ0 M0 S0 =[MActT (Recv n v) :: mpath]=> mq [TrRecv n v] M1 S0)
        /\ mpath >:~ []
        /\ Forall Flushing_act mpath
        /\ ready M1.

  Proof.
    intros.
    specialize (@Transp_completeness_recv n v S0 S1 MQ0 M0 H H0) as TM.
    unfold flush_path in *.
    unfold instr in *.
    unfold flush_M.
    exists (mk_flush_path MQ0 M0).
    destruct M0. attac.
    exists {| handle := handle0; state := MRecv s|}.
    attac.
  Qed.


  Lemma prepare_recv : forall [MN0 : MNet] [n n' v] [S1],
      (NetMod.get n (net_deinstr MN0) =(recv n' v)=> S1) ->
      flushed MN0 ->
      exists mnpath MS0 MQ1 M1 MN1,
        NVTrans n (recv n' (MValP v)) MN0 (NetMod.put n MS0 MN0)
        /\ ((NetMod.put n MS0 MN0) =[mnpath]=> (NetMod.put n (mq MQ1 M1 S1) MN1))
        /\ net_deinstr MN0 = net_deinstr MN1
        /\ MQ_Clear MQ1
        /\ flushed MN1.

  Proof.
    intros *. intros T0 HFN0.

    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:HEq0.
    unfold net_deinstr in T0.
    rewrite NetMod.get_map in T0.

    assert (MQ_Clear MQ0) as HMQ0.
    {
      specialize (HFN0 n).
      unfold flushed_in in HFN0.
      rewrite HEq0 in HFN0.
      apply HFN0.
    }

    destruct (Transp_completeness_recv_old MQ0 M0 HMQ0 T0)
      as (mpath & M1 & TM & HC1 & HF1 & HRD1).

    unfold instr in TM.
    simpl in TM.

    apply path_split1 in TM as ([MQ1' M1' S1'] & TM0 & TM1).

    assert (NVTrans n (recv n' (MValP v)) MN0 (NetMod.put n (mq MQ1' M1' S1') MN0)) as TNM0.
    {
      eattac.
      hsimpl in *.
      rewrite HEq0.
      unfold deinstr.
      destruct S0.
      attac.
    }

    assert (exists M2, mq [TrRecv n' v] M1 (deinstr (NetMod.get n MN0)) =(MActP (Recv n' v))=> mq [] M2 S1)
      as (M2 & TM2).
    {
      hsimpl in *.
      exists {|handle:=h; state:=h (TrRecv n' v) s|}.
      constructor; eattac.
    }

    assert ([MActP (Recv n' v)] >:~ []) as HC2 by attac.
    assert (Forall Flushing_act [MActP (Recv n' v)]) as HF2 by attac.
    assert (Forall Flushing_act (mpath ++ [MActP (Recv n' v)])) as HF_Coq_stdlib_sucks
        by attac.

    apply path_seq0 in TM2.
    destruct (admin_path_available n MN0 HC1 HF1 TM1 HFN0)
      as (mnpath & MQ2 & MN2 & TNM1 & HFN2 & HNDI & HMQ2).
    clear HF_Coq_stdlib_sucks.

    eapply (Flushing_cont MQ2) in TM2; eauto with LTS.
    rewrite (app_nil_l) in *.
    apply path_split0 in TM2.

    assert (deinstr (NetMod.get n MN0) = S0) as HEqS0 by attac.

    repeat (rewrite HEqS0 in * ). clear HEqS0.

    exists (mnpath ++ [NTau n (MActP (Recv n' v))]).
    exists ((mq MQ1' M1' S1')).
    exists MQ2, M2.
    exists MN2.

    repeat split; eauto with LTS.
    - rewrite HEq0 in *.
      attac.
    - apply path_seq1' with (middle := NetMod.put n (mq ([TrRecv n' v] ++ MQ2) M1 S0) MN2).
      1: attac.

      replace (mq ([TrRecv n' v] ++ MQ2) M1 S0)
        with (NetMod.get n (NetMod.put n (mq ([TrRecv n' v] ++ MQ2) M1 S0)  MN2))
        in TM2 by attac.
      constructor. constructor.

      apply NT_Vis in TM2.
      rewrite NetMod.put_put_eq in TM2.
      attac.
  Qed.


  Lemma put_instr : forall I0 N0 n [MQ M S],
      MQ_Clear MQ ->
      ready M ->
      exists I1 : mon_assg, NetMod.put n (mq MQ M S) (net_instr I0 N0) = net_instr I1 (NetMod.put n S N0).

  Proof.
    intros * HMQ HM.

    assert (flushed (NetMod.put n (mq MQ M &S) (net_instr I0 N0))) as HFN.
    {
      unfold flushed, flushed_in.
      intros n0.
      specialize (net_instr_flushed I0 N0 n0) as HF.
      smash_eq n n0; attac.
    }

    assert (ready_net (NetMod.put n (mq MQ M &S) (net_instr I0 N0))) as HRN.
    {
      unfold ready_net, ready_in.
      intros n0.
      specialize (net_instr_ready_net I0 N0 n0) as HR.
      smash_eq n n0; attac.
    }

    destruct (flushed_ready_instr HFN HRN) as (I1, HEq).
    exists I1.
    rewrite HEq.
    specialize net_deinstr_instr as HNDI.
    unfold net_instr, net_deinstr in *.
    repeat (rewrite NetMod.put_map in * ).
    repeat (rewrite HNDI).
    destruct &S.
    eattac.
  Qed.


  (** Network transparency completeness over a single action *)
  Lemma Net_Transp_completeness1 : forall I0 {na} {N0 N1 : PNet},
      (N0 =(na)=> N1) ->
      exists nmpath I1,
        (net_instr I0 N0 =[nmpath]=> net_instr I1 N1).

  Proof with (eauto with LTS).
    intros * TN.
    kill TN; subst.
    - kill H.
      apply (Net_Vis_Transp_completeness_tau I0) in H0.
      exists [NTau n (MActP Tau)], I0.
      apply path_seq0.
      attac.
    - kill H. kill H0.
      rename H1 into T_send.
      rename H into T_recv.
      rename n' into m.
      rename S into Sn.
      rename S0 into Sm.

      destruct (prepare_send I0 T_send)
        as (mnpath0 & I1 & MQ_n & M_n & MN1 & TN0 & TN_send & HND1 & HMQ_n).

      remember (NetMod.put n (mq MQ_n M_n Sn) (net_instr I1 N0)) as MN1'.

      assert (flushed MN1') as HFN1'.
      specialize (net_instr_flushed I1 N0) as HFN0.
      unfold flushed in *. intros. subst MN1'.
      unfold flushed_in.
      destruct (NAME.eq_dec n0 n); subst.
      rewrite NetMod.get_put_eq. auto.
      rewrite NetMod.get_put_neq; auto. apply HFN0.

      assert ( (net_deinstr MN1') = NetMod.put n Sn N0) as HND0.
      {
        unfold net_deinstr.
        rewrite HeqMN1'.
        assert (deinstr (mq MQ_n M_n Sn) = Sn).
        unfold deinstr.
        destruct Sn. eattac.
        rewrite NetMod.put_map.
        specialize (net_deinstr_instr) as HNDI.
        unfold net_instr in *.
        unfold net_deinstr in *.
        rewrite HNDI.
        rewrite H.
        reflexivity.
      }
      rewrite <- HND0 in T_recv.

      specialize (net_instr_ready I0 (net_deinstr MN1)) as HRC0.
      rewrite <- HND1 in HRC0.

      destruct (prepare_recv T_recv HFN1')
        as (mnpath1 & MS_m0 & MQ_m & M_m & MN3' & TN_recv & TN2 & HND2 & HMQ_m & HFN3').

      remember (NetMod.put m MS_m0 MN1') as MN2.
      remember (NetMod.put m (mq MQ_m M_m Sm) MN3') as MN3.

      replace ( (MActT (Send (m, t) v)))
        with (send (m, t) (MValP v))
        in TN_send; eauto.

      assert (@trans _ _ (@trans_net _ _ _ trans_mqued)
                (NComm n m t (MValP v)) MN1 MN2) as TN1.
      eapply (NT_Comm TN_send TN_recv).
      apply path_seq0 in TN1.

      assert (forall n', not (In n' (path_particip mnpath0
                                  ++ path_particip [NComm n m t (MValP v)]
                                  ++ path_particip mnpath1)
                      ) ->
                    ready_in n' MN3
             ) as HRd3.
      intros.
      apply not_in_app_inv in H as (NI_part0 & H).
      apply not_in_app_inv in H as (NI_part1 & NI_part2).
      specialize (path_particip_stay NI_part0 TN0) as HStay0.
      specialize (path_particip_stay NI_part1 TN1) as HStay1.
      specialize (path_particip_stay NI_part2 TN2) as HStay2.
      unfold ready_in in *. rewrite <- HStay2.
      unfold ready_in in *. rewrite <- HStay1.
      unfold ready_in in *. rewrite <- HStay0.
      unfold net_instr. rewrite NetMod.get_map.
      unfold net_instr_n.
      destruct (I0 n'). unfold instr. simpl. destruct m1. simpl. auto.

      assert (flushed MN3) as HFN3.
      specialize (net_instr_flushed I0 N0) as HNF0.
      rewrite HeqMN3.
      unfold flushed.
      intros.
      unfold flushed_in.

      destruct (NAME.eq_dec n0 m); destruct (NAME.eq_dec n0 n); subst.
      rewrite NetMod.get_put_eq...
      rewrite NetMod.get_put_eq...
      rewrite NetMod.get_put_neq...
      apply HFN3'.
      rewrite NetMod.get_put_neq...
      apply HFN3'.

      destruct (flushed_ready MN3 HRd3)
        as (mnpath2 & MN4 & TN3 & HRd4 & HND4 & HFN4); auto.

      destruct (flushed_ready_instr HFN4 HRd4)
        as (I & Eq).

      unshelve eexists (mnpath0 ++ [NComm n m t _] ++ mnpath1 ++ mnpath2). apply (MValP v).
      exists &I.

      apply path_seq with (middle := MN1); auto.
      apply path_seq with (middle := MN2); auto.
      apply path_seq with (middle := MN3); auto.

      rewrite <- HND4 in *.
      rewrite &Eq in TN3.
      unfold net_deinstr in TN3.
      subst.
      rewrite NetMod.put_map in TN3.
      unfold net_deinstr in HND2.
      rewrite <- HND2 in TN3.
      rewrite NetMod.put_map in TN3.

      assert (deinstr (mq MQ_n M_n Sn) = Sn).
      {
        unfold deinstr.
        destruct Sn. clear - HMQ_n. eattac.
      }

      assert (deinstr (mq MQ_m M_m Sm) = Sm).
      {
        unfold deinstr.
        destruct Sm. simpl. clear - HMQ_m. eattac.
      }

      rewrite H in *.
      rewrite H0 in *.
      subst.
      specialize net_deinstr_instr as HNDI.
      unfold net_instr in *.
      unfold net_deinstr in *.

      repeat (rewrite NetMod.put_map in * ).
      repeat (rewrite HNDI in * ).

      apply TN3.
  Qed.


  (** Network transparency completeness *)
  Theorem Net_Transp_completeness : forall {path} I0 {N0 N1 : PNet},
      (N0 =[ path ]=> N1) ->
      exists mpath I1,
        (net_instr I0 N0 =[ mpath ]=> net_instr I1 N1).

  Proof with attac.
    induction path; intros.
    1: exists [], I0...

    kill H.
    apply (Net_Transp_completeness1 I0) in T0 as (mpath0 & I0' & NT0).
    apply (IHpath I0') in T1 as (mpath1 & I1 & NT1). clear IHpath.

    exists (mpath0 ++ mpath1), I1...
  Qed.


  Lemma mnet_preserve_M_handle [na MN0 MN1 n] :
    (MN0 =(na)=> MN1) ->
    get_H MN0 n = get_H MN1 n.

  Proof.
    intros.
    kill H.
    - ltac1:(autounfold with LTS_get).
      smash_eq n n0.
      2: attac.
      hsimpl in *.
      consider (_ =(_)=> _); attac 1.
    - transitivity '(get_H N0' n); ltac1:(autounfold with LTS_get).
      + smash_eq n n0.
        2: attac.
        hsimpl in *.
        destruct v; attac.
      + smash_eq n n'.
        2: attac.
        hsimpl in *.
        destruct v; attac.
  Qed.


End TRANSP_F.

Module Type TRANSP(Conf : TRANSP_CONF) := Conf <+ TRANSP_PARAMS <+ TRANSP_F.
