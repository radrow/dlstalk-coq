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
  Notation PNet := (NetMod.t Serv).
  (** Monitored network *)
  Notation MNet := (NetMod.t MServ).

  Lemma serv_i_net_inv' : forall I P O n [N : PNet], (* TODO prime' is due to a name clash in SRPCNet.v *)
      NetMod.get n N = serv I P O ->
      serv_i (NetMod.get n N) = I.
  Proof. intros. rewrite H. attac. Qed.

  Lemma serv_p_net_inv' : forall I P O n N,
      NetMod.get n N = serv I P O ->
      serv_p (NetMod.get n N) = P.
  Proof. intros. rewrite H. attac. Qed.

  Lemma serv_o_net_inv' : forall I P O n N,
      NetMod.get n N = serv I P O ->
      serv_o (NetMod.get n N) = O.
  Proof. intros. rewrite H. attac. Qed.

  #[export] Hint Rewrite -> serv_i_net_inv' serv_p_net_inv' serv_o_net_inv' using spank : LTS LTS_concl.
  #[export] Hint Resolve serv_i_net_inv' serv_p_net_inv' serv_o_net_inv' : LTS LTS_concl.


  Lemma mserv_i_net_inv : forall MQ M S n [N : MNet],
      NetMod.get n N = mserv MQ M S ->
      mserv_i (NetMod.get n N) = MQ.
  Proof. intros. rewrite H. attac. Qed.

  Lemma mserv_m_net_inv : forall MQ M S n [N : MNet],
      NetMod.get n N = mserv MQ M S ->
      mserv_m (NetMod.get n N) = M.
  Proof. intros. rewrite H. attac. Qed.

  Lemma mserv_s_net_inv : forall MQ M S n [N : MNet],
      NetMod.get n N = mserv MQ M S ->
      mserv_s (NetMod.get n N) = S.
  Proof. intros. rewrite H. attac. Qed.

  #[export] Hint Rewrite -> mserv_i_net_inv mserv_m_net_inv mserv_s_net_inv using spank : LTS LTS_concl.
  #[export] Hint Resolve mserv_i_net_inv mserv_m_net_inv mserv_s_net_inv : LTS LTS_concl.


  Definition PNAct := @NAct PAct gen_Act_PAct.

  Definition MNAct := @NAct MAct gen_Act_MAct.

  #[export] Hint Transparent PNAct MNAct : LTS typeclass_instances.


  Lemma PNet_trans_simpl_inv a n N I P O S :
    NetMod.get n N = serv I P O ->
    (NetMod.get n N =(a)=> S) <-> (serv I P O =(a)=> S).
  Proof. split; intros; rewrite H in *; auto. Qed.

  Lemma MNet_trans_simpl_inv a n N MQ M S MS :
    NetMod.get n N = mserv MQ M S ->
    (NetMod.get n N =(a)=> MS) <-> (mserv MQ M S =(a)=> MS).
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


  Inductive instr := instr_ {instr_for : Name -> mon_assg}.

  (** Instrumentation of all processes in a network *)
  Definition apply_instr (i : instr) (N : PNet) : MNet :=
    NetMod.map (instr_for i) N.

  Coercion apply_instr : instr >-> Funclass.

  #[export] Hint Transparent apply_instr : LTS.


  (** Deinstrumentation of all processes *)
  Coercion deinstr (N : MNet) : PNet :=
    NetMod.map (fun n S => serv_deinstr S) N.


  #[export] Hint Transparent deinstr : LTS.


  (** Network instrumentation is an injection *)
  Lemma net_instr_inj : forall [I : instr] [N0 N1], I N0 = I N1 -> N0 = N1.

  Proof.
    intros.
    apply NetMod.extensionality.
    intros.
    unfold apply_instr, instr_for in H.
    match! goal with [h : ?l = ?r |-_] => assert (NetMod.get n $l = NetMod.get n $r) by attac end.
    attac.
  Qed.


  (** Deinstrumentation is inversion of instrumentation *)
  Lemma instr_inv : forall I N,
      deinstr (apply_instr I N) = N.

  Proof.
    intros.
    unfold deinstr.
    unfold apply_instr.
    unfold instr_for.
    apply NetMod.extensionality.
    intros.
    do 2 (rewrite NetMod.get_map).
    attac.
  Qed.

  #[export] Hint Immediate instr_inv : LTS.
  #[export] Hint Rewrite -> instr_inv using spank : LTS LTS_concl.


  (** NV-transitions preserve mon_assg_ (almost). *)
  Lemma NV_invariant : forall [n : Name] [a : MAct] [I0] [N0 : PNet] [MN1 : MNet],
      (apply_instr I0 N0) ~(n@a)~> MN1 ->
      MN1 = NetMod.put n (NetMod.get n MN1) (apply_instr I0 N0).

  Proof. eattac. Qed.


  (** NV-receives of monitor stuff preserve mon_assg_ *)
  Lemma recvm_invariant_instr : forall [n n' : Name] [t0 v I0] [N0 : PNet] [MN1 : MNet],
      NVTrans n (MActM (Recv (n', t0) v)) (apply_instr I0 N0) MN1 ->
      exists I1,
        MN1 = apply_instr I1 N0.

  Proof with (eauto with LTS).
    intros.
    kill H.

    unfold apply_instr in *.
    unfold instr_for in *.
    rewrite NetMod.get_map in H0.
    simpl in *.
    kill H0.

    unshelve epose (
        fun n0 => if NAME.eqb n0 n
               then {| assg_mq := assg_mq (instr_for I0 n) ++ [MqProbe (n', t0) v];
                      assg_m := assg_m (instr_for I0 n);
                      assg_clear := _
                 |}
               else instr_for I0 n0
      )
      as I1; destruct (instr_for I0 n) eqn:?; simpl in *...
    attac.
    exists (instr_ I1).
    apply NetMod.extensionality.
    intros.
    subst I1.

    rewrite NetMod.get_map.
    smash_eq n n0; attac.
    rewrite Heqm. attac.
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


  Definition NoMqSend (MS : MServ) : Prop :=
    match MS with (mserv MQ _ _) => NoSends_MQ MQ end.

  Definition no_sends_in n N := NoMqSend (NetMod.get n N).

  Definition no_sends (N : MNet) := forall n, no_sends_in n N.

  Lemma no_sends_in_NoSendsMQ [n MN MQ M S] :
    NetMod.get n MN = mserv MQ M S ->
    no_sends_in n MN ->
    NoSends_MQ MQ.

  Proof. unfold no_sends_in, NoMqSend. attac. Qed.

  #[export] Hint Resolve no_sends_in_NoSendsMQ : LTS.


  Definition Flushed (MS : MServ) : Prop :=
    match MS with (mserv MQ _ _) => MQ_Clear MQ end.

  Definition flushed_in n N := Flushed (NetMod.get n N).

  Definition flushed (N : MNet) := forall n, flushed_in n N.

  Definition Flushing_NAct (n : Name) (a : MNAct) : Prop :=
    match a with
    | NComm n0 n1 t v => n0 = n
    | NTau n' a => n' = n /\ Flushing_act a /\ ia a
    end.


  Lemma flushed_in_MQ_Clear [n MN MQ M S] :
    NetMod.get n MN = mserv MQ M S ->
    flushed_in n MN ->
    MQ_Clear MQ.

  Proof. unfold flushed_in, Flushed. attac. Qed.

  #[export] Hint Resolve flushed_in_MQ_Clear : LTS.


  Lemma Clear_NoSends_MQ : forall MQ, MQ_Clear MQ -> NoSends_MQ MQ.
  Proof. induction MQ; attac. Qed.

  #[export] Hint Immediate Clear_NoSends_MQ  : LTS.

  Fact NetGet_get : forall (P : Serv -> Prop) n (N : PNet), P (NetGet _ N n) <-> P (NetMod.get n N).
    attac. Qed.
  #[export] Hint Immediate NetGet_get : LTS core.
  Fact MNetGet_get : forall (P : MServ -> Prop) n (N : MNet), P (NetGet _ N n) <-> P (NetMod.get n N).
    attac. Qed.
  #[export] Hint Immediate MNetGet_get : LTS core.

  Lemma flushed_in_NoSends_MQ : forall MN n, flushed_in n MN -> NoSends_MQ (mserv_i (MN n)).
  Proof. intros. assert (Flushed (MN n)) by auto. destruct (MN n). attac. Qed.

  #[export] Hint Immediate flushed_in_NoSends_MQ  : LTS.


  Definition ready_in n (N : MNet) :=
    ready (NetMod.get n N).

  Definition ready_net N := forall n, ready_in n N.


  Lemma apply_instr_clear : forall I N MQ M S n,
      NetMod.get n (apply_instr I N) = mserv MQ M S ->
      MQ_Clear MQ.

  Proof.
    intros.
    unfold apply_instr, instr_for, apply_instr in *; hsimpl in *.
    destruct (&I).
    destruct `(mon_assg).
    attac.
  Qed.

  Lemma apply_instr_ready : forall I N MQ M S n,
      NetMod.get n (apply_instr I N) = mserv MQ M S ->
      ready M.

  Proof.
    intros.
    unfold apply_instr, instr_for, serv_instr in *; hsimpl in *.
    attac.
  Qed.

  Hint Resolve apply_instr_clear apply_instr_ready : LTS.

  Lemma flush_act_available : forall [n : Name] a MS [MN0 : MNet],
      (NetMod.get n MN0 =(a)=> MS) ->
      Flushing_act a ->
      (forall t0 v, a <> send (n, t0) v) ->
      (
        exists na MN1,
          (MN0 =(na)=> MN1)
          /\ NetMod.get n MN1 = MS
          /\ (forall m, no_sends_in m MN0 -> no_sends_in m MN1)
          /\ (forall m, no_sends_in n MN0 -> flushed_in m MN0 -> flushed_in m MN1)
          /\ (forall m, not (ready_in n MN0) -> [a] >:~ [] -> ready_in m MN0 -> ready_in m MN1)
          /\ (flushed MN0 -> deinstr MN0 = deinstr MN1)
      ).

  Proof using Type with (eauto with LTS).
    intros * T HF HNoself.
    destruct a; hsimpl in *; hsimpl in |- *.
    - exists (NTau n (MActP p)).
      exists (NetMod.put n &MS MN0).
      hsimpl in *.
      unfold no_sends_in, NoMqSend, flushed_in, flushed, Flushed, deinstr, ready_in in *.

      eattac.
      + destruct p; doubt.
        hsimpl in *.
        smash_eq n m; attac.
      + destruct p; doubt.
        hsimpl in *.
        smash_eq n m; attac.
      + destruct p; doubt.
        hsimpl in *.
        smash_eq n m; attac.
      + destruct p; doubt.
        specialize (H n).
        hsimpl in *.
        bs (MQ_Clear (MqRecv n0 v :: MQ)) by attac.

    - destruct p; attac.
      + destruct n0 as [n0 t0].
        smash_eq n n0.
        1: specialize (HNoself t0 (MValP v)); bs.

        remember (mserv MQ (mon_handle (MqSend (n0, t0) v) s) P) as S.

        assert (exists N0', NetMod.get n N0' = &S /\ NVTrans n (send (n0, t0) (MValP v)) MN0 N0')
          as (N0' & HeqN0 & NT0)
            by (exists (NetMod.put n &S MN0); eattac).

        destruct (recv_available n0 n t0 (MValP v) N0') as (N0'' & NT0').
        exists (NComm n n0 t0 # v), N0''; attac.

        all: unfold no_sends_in, NoMqSend, flushed_in, flushed, Flushed, deinstr, ready_in in *.
        * hsimpl in *.
          smash_eq n n0 m; attac.

        * hsimpl in *. attac.
        * hsimpl in *. hsimpl in *.
          assert (flushed_in n MN0) by auto.
          unfold flushed_in, Flushed in *.
          hsimpl in *. bs.
    - destruct a; attac.
      + destruct n0 as [n0 t0].

        smash_eq n n0.
        1: now (specialize (HNoself t0 (MValM v)); bs).

        assert (exists N1 : MNet, MN0 =( NComm n n0 t0 ^ v)=> N1) as [N1 na]
          by (eapply send_comm_available; rewrite `(NetMod.get n MN0 = _); eattac).
        eexists _, _.
        split. 1: eauto.

        consider (MN0 =(_)=> _).
        hsimpl in *.

        all: unfold no_sends_in, NoMqSend, flushed_in, flushed, Flushed, deinstr, ready_in, ready in *.

        all: hsimpl in *; attac.

        1,2,3: smash_eq n n0 m; hsimpl in *; attac.

        apply NetMod.extensionality.
        intros.
        hsimpl in |- *.
        unfold serv_deinstr.
        smash_eq n n0 n1; attac.

      + exists (NTau n (MActM Tau)).
        exists (NetMod.put n (mserv MQ (mon_handle (MqProbe n0 msg) s) P) MN0).
        eattac.
        1: econstructor; eattac.

        all: unfold no_sends_in, NoMqSend, flushed_in, flushed, Flushed, deinstr, ready_in, ready in *.

        1,2: smash_eq n m; ltac1:(autorewrite with LTS ); attac.
        all: eattac.

        apply NetMod.extensionality.
        intros.
        hsimpl in |- *.
        unfold serv_deinstr.
        smash_eq n n1; attac.
  Qed.


  Lemma flush_act_available_self : forall [n : Name] t0 v [MQ M S] [N0 : MNet],
      (NetMod.get n N0 =(send (n, t0) v)=> mserv MQ M S) ->
      (
        exists na N1 MQ',
          (N0 =(na)=> N1)
          /\ NetMod.get n N1 = mserv (MQ ++ MQ') M S
          /\  (forall m, no_sends_in m N0 -> no_sends_in m N1)
          /\  (forall m, flushed_in m N0 -> flushed_in m N1)
          /\ (forall m, not (ready_in n N0) -> [send (n, t0) v] >:~ [] -> ready_in m N0 -> ready_in m N1)
          /\ (flushed N0 -> deinstr N0 = deinstr N1)
          /\ Forall (fun t0 => match t0 with
                           | MqSend _ _ => False
                           | MqRecv _ _ => not (no_sends_in n N0)
                           | _ => True
                           end
              ) MQ'
      ).

  Proof.
    intros *. intros T.

    specialize (send_comm_available T) as (N1 & TN).

    destruct v; (eexists _, _).
    1: (exists [MqProbe (n, t0) (m)]); rename m into msg.
    2: (exists [MqRecv (n, t0) v]) .
    all: split > [ltac1:(eassumption)|]; repeat split; intros.
    all: unfold no_sends_in, NoMqSend, flushed_in, flushed, Flushed, deinstr, ready_in in *.
    all: kill TN.
    - hsimpl in *.
      attac.
    - hsimpl in *.
      smash_eq n m; attac.
    - hsimpl in *.
      smash_eq n m; eattac.
    - hsimpl in *.
      smash_eq n m; eattac.
    - hsimpl in *.
      hsimpl in *.
      assert (forall MQ nc m M S, serv_deinstr (mserv (MQ ++ [MqProbe nc m]) M S) = serv_deinstr (mserv MQ M S)) as Hreduce.
      {
        clear.
        intros.
        destruct S.
        hsimpl in |- *.
        attac.
      } (* TODO lemma? *)

      unfold serv_deinstr in Hreduce.
      specialize (Hreduce MQ0 (n, t0) msg M0 (NetMod.get n N0)).
      blast_cases.
      attac.

      unfold serv_deinstr.
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
      (mserv MQ0 M0 (serv I0 P O) =[ mpath ]=> mserv [] (MRecv M1) (serv (I0 ++ I1) P O))
      /\ Forall Flushing_act mpath.

  Proof.
    intros.
    exists (mk_flush_path MQ0 M0).
    simpl.
    unshelve eexists (flush_Mstate MQ0 M0).
    exists (retract_recv MQ0).
    simpl.
    replace (serv (I0 ++ retract_recv MQ0) P &O) with (flush_S MQ0 (serv I0 P &O)) by attac.
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

    remember (serv I0 P0 O0) as S0. clear HeqS0.
    remember (serv (I0 ++ I1) P0 O0) as S1. clear HeqS1 I0 I1 P0 O0.
    remember (mserv MQ0 M0 S0) as MS0. clear HeqMS0.

    remember (mserv [] (MRecv M1) S1) as MS1.
    assert (NoMqSend MS1) as HNoSend1 by attac.

    remember [] as MQ1. clear HeqMQ1.

    generalize dependent MS1.
    generalize dependent MQ1.
    generalize dependent MS0.
    generalize dependent MN0.

    induction mpath; intros.
    1: eexists _, _; eattac; kill H; unfold no_sends_in, NoMqSend; kill TM.
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
      assert (NoMqSend (mserv (MQ1 ++ MQ') (MRecv M1) S1)) as HNS1'.
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

    remember (serv I0 P0 O0) as S0. clear HeqS0.
    remember (serv (I0 ++ I1) P0 O0) as S1. clear HeqS1 I0 I1 P0 O0.
    remember (mserv MQ0 M0 S0) as MS0. clear HeqMS0.

    remember (mserv [] (MRecv M1) S1) as MS1; eauto.
    assert (Flushed MS1) as HNoSend1. subst. constructor.

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
    - replace ( MTrans a (NetMod.get n MN0) (mserv MQ0' M0' S0'))
        with  ((NetMod.get n MN0) =(a)=> mserv MQ0' M0' S0')
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

      assert (Flushed (mserv (MQ1 ++ MQ') (MRecv M1) S1)) as HF1'.
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
    unfold ready.
    destruct `(MProc).
    - left.
      eattac.
    - right.
      unfold not.
      intros.
      eattac.
  Qed.

  Lemma ready_exists : forall MQ M0 S,
    exists mpath M1,
      (mserv MQ M0 S =[mpath]=> mserv MQ M1 S)
      /\ Forall Flushing_act mpath
      /\ ready M1
      /\ mpath >:~ [].

  Proof with eattac.
    intros.
    generalize dependent MQ.
    induction `(MProc); intros.
    - exists []...
    - specialize (IHM0 MQ).
      edestruct IHM0 as (mpath & M1 & TM & HF & HR & HC).
      exists (MActM (Send to msg) :: mpath), M1...
  Qed.

  #[export] Hint Resolve ready_exists : LTS.


  Lemma ready_exists_q : forall MS0,
    exists mpath (MS1 : MServ),
      (MS0 =[mpath]=> MS1)
      /\ Forall Flushing_act mpath
      /\ ready MS1
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
      (deinstr MNm1 = deinstr MN0 /\ flushed MN0) ->
      exists nmpath MN1,
        (MN0 =[ nmpath ]=> MN1)
        /\ (forall m, (n = m \/ ready_in m MN0) -> ready_in m MN1)
        /\ (deinstr MNm1 = deinstr MN1 /\ flushed MN1).

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


  Lemma net_instr_inv (I : instr) (N0 N1 : PNet) : I N0 = I N1 <-> N0 = N1.
  Proof. attac. eauto using net_instr_inj. Qed.


  Lemma flushed_ready : forall [chans] MN0,
      (forall n, not (In n chans) -> ready_in n MN0) ->
      (deinstr MN0 = deinstr MN0 /\ flushed MN0) ->
      exists nmpath MN1,
        (MN0 =[nmpath]=> MN1)
        /\ ready_net MN1
        /\ (deinstr MN0 = deinstr MN1 /\ flushed MN1).

  Proof.
    intros chans.
    intros MN0.
    specialize (net_induction) with (P := fun (M : MServ) => ready M).
    eauto using flushed_ready_one.
  Qed.


  Lemma flushed_ready_instr : forall [MN],
      flushed MN ->
      ready_net MN ->
      exists I, MN = apply_instr I (deinstr MN).

  Proof.
    intros MN HF HR.

    unfold flushed in HF.
    unfold ready_net in HR.
    unfold flushed_in in HF.
    unfold ready_in in HR.

    unfold apply_instr.
    unfold instr_for.

    assert (forall n, {assg : mon_assg | NetMod.get n MN = assg (NetMod.get n MN)}).
    {
      intros.
      destruct (NetMod.get n MN) as [MQ M S] eqn:HI.
      assert (MQ_Clear MQ).
      { specialize (HF n). rewrite HI in HF. apply HF. }
      unshelve eapply (exist _ (_mon_assg MQ _ (MRecv M)) _).
      specialize (HR n). rewrite HI in HR. hsimpl in *. subst.
      unfold serv_instr; attac.
    }

    assert ((NetMod.init (fun n => match NetMod.get n MN with
                                | mserv _ _ s => s
                                end
            )) = deinstr MN).
    {
      unfold deinstr.
      apply NetMod.extensionality.
      intros.
      rewrite NetMod.init_get.
      rewrite NetMod.get_map.
      unfold serv_deinstr.
      specialize (H n).
      destruct H.
      subst.
      destruct (NetMod.get n MN).
      hsimpl; attac. (* TODO hsimpl and attac *)
    }
    rewrite <- H0.
    unshelve eexists (instr_ (fun n => match H n with exist _ _ _ => _ end)).
    apply NetMod.extensionality.
    intros.
    attac.
    unfold deinstr, serv_instr in *.
    rewrite NetMod.init_get.
    attac.
  Qed.


  Lemma flushed_in_no_sends : forall [n N],
      flushed_in n N -> no_sends_in n N.

  Proof.
    intros n N HF.
    unfold no_sends_in. unfold flushed_in in HF.
    unfold NoMqSend. unfold Flushed in HF.
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
        (MN0 =[ mnpath ]=> apply_instr I1 N1).

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
    exists &I, (deinstr MN3).

    hrewrite MN3 in * |- .
    eauto with LTS.
  Qed.


  Lemma Net_corr_extraction : forall [MN0 MN1 : MNet] [mnpath],
      (MN0 =[ mnpath ]=> MN1) ->
      forall n,
      exists mpath ppath,
        Path_of n mnpath mpath
        /\ (NetMod.get n (deinstr MN0) =[ ppath ]=> NetMod.get n (deinstr MN1))
        /\ mpath >:~ ppath.

  Proof.
    intros *.
    intros TN n.

    destruct (path_of_exists n mnpath) as (mpath & HPo).
    specialize (path_of_ptrans HPo TN) as TM.

    unfold deinstr.
    do 2 (rewrite NetMod.get_map).
    assert (serv_deinstr (NetMod.get n MN0) =[ MPath_to_PPath mpath ]=>
              serv_deinstr (NetMod.get n MN1)
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
      deinstr MN0 = deinstr MN1.

  Proof.
    intros *. intros T.

    kill T.
    kill H.

    unfold deinstr in *.
    rewrite NetMod.put_map in *.
    kill TP.

    assert (serv_deinstr (mserv MQ M (serv &I P ((n', t0, v) :: &O))) = serv_deinstr (NetMod.get n MN0))
      by (rewrite <- H2; reflexivity).

    clear H2.
    simpl in *.
    do 2 (hsimpl). rewrite <- app_assoc. simpl.

    (* This line is mandatory. `Set Printing All` helps here. *)
    (* Set Printing All. *)
    unfold NameTag in *.
    rewrite H.

    unfold serv_deinstr.

    rewrite <- (NetMod.put_map (fun _ S =>
                                 match S with
                                 | mserv _ _ _ => _
                                 end
      )).
    rewrite NetMod.put_get_eq.
    reflexivity.
  Qed.


  Lemma Net_Vis_corr_precv : forall [n n' : Name] [t0 v] [MN0 MN1 : MNet],
      (NVTrans n (MActP (Recv (n', t0) v)) MN0 MN1) ->
      deinstr MN0 = deinstr MN1.

  Proof.
    intros *. intros T.

    kill T.
    kill H.

    unfold deinstr in *.
    rewrite NetMod.put_map in *.

    assert (serv_deinstr (mserv MQ M1 S1) = NetMod.get n (NetMod.map (fun _ S => serv_deinstr S) MN0)).

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
      (NVTrans n Tau (deinstr MN0) (deinstr MN1)).

  Proof.
    intros *. intros T.

    kill T.
    kill H.

    unfold deinstr.
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
      (NVTrans n (Send (n', t0) v) (deinstr MN0) (deinstr MN1)).

  Proof.
    intros *. intro T.
    kill T.
    kill H.

    unfold deinstr.
    rewrite NetMod.put_map.
    constructor.
    rewrite NetMod.get_map.
    rewrite <- H3. clear H3.
    simpl. clear MN0 n.
    destruct S0; eattac.
  Qed.


  Lemma Net_Vis_corr_recv : forall [n n' : Name] [t0 v] [MN0 MN1 : MNet],
      (NVTrans n (MActT (Recv (n', t0) v)) MN0 MN1) ->
      (NVTrans n (Recv (n', t0) v) (deinstr MN0) (deinstr MN1)).

  Proof.
    intros *. intro T.
    kill T.
    kill H.

    unfold deinstr.
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
      deinstr MN0 = deinstr MN1.

  Proof.
    intros.
    kill H.
    kill H0.
  Qed.


  Lemma Net_Vis_corr_mon : forall [n : Name] [ma] [MN0 MN1 : MNet],
      (NVTrans n (MActM ma) MN0 MN1) ->
      deinstr MN0 = deinstr MN1.

  Proof.
    intros.
    kill H.

    unfold deinstr in *.
    rewrite NetMod.put_map in *.
    destruct S as [MQ M S].

    replace (serv_deinstr (mserv MQ M &S)) with (NetMod.get n (NetMod.map (fun _ S => serv_deinstr S) MN0)); attac.

    consider (_ =(_)=> _); hsimpl; eattac.
  Qed.

  #[export] Hint Immediate
    Net_Vis_corr_mon
    Net_Vis_corr_tau
    Net_Vis_corr_recv
    Net_Vis_corr_send
    Net_Vis_corr_ptau
    Net_Vis_corr_precv
    Net_Vis_corr_psend : LTS.


  Lemma transp_sound1 : forall [ma] [MN0 MN1 : MNet],
      (MN0 =(ma)=> MN1) ->
      exists pnpath,
        (deinstr MN0 =[pnpath]=> deinstr MN1).

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


  Lemma deinstr_act [MN0 MN1 : MNet] [na] :
    (MN0 =(na)=> MN1) ->
    match MNAct_to_PNAct na with
    | Some a => deinstr MN0 =(a)=> deinstr MN1
    | None => deinstr MN0 = deinstr MN1
    end.

  Proof.
    intros.
    kill H.
    - destruct_ma &a; doubt; simpl; eattac.
    - destruct v.
      + hsimpl in *; hsimpl in |- *.
        apply NetMod.extensionality; intros.
        unfold deinstr in *; simpl in *.
        hsimpl in |- *.
        smash_eq_on n0 n n'; subst; hsimpl in *; hsimpl in |- *; auto.
        all: unfold serv_deinstr in *; destruct P; hsimpl; attac.
      + simpl in *.
        enough (exists N, deinstr MN0 ~( n @ Send (n', &t) v )~> N /\ N ~( n' @ Recv (n, &t) v )~> deinstr MN1).
        {
          destruct H as [N [? ?]].
          econstructor; eauto.
        }
        kill H0.
        unfold deinstr in *; simpl in *.
        hsimpl in |- *.
        kill H.
        destruct S0 as [I P O].
        exists (NetMod.put n (serv (&I ++ retract_recv MQ) P (retract_send MQ ++ &O)) (deinstr MN0)).
        split.
        * constructor.
          unfold deinstr, serv_deinstr in *.
          attac.
        * unfold deinstr, serv_deinstr in *.
          hsimpl in *. hsimpl in |- *.
          constructor.
          destruct P0 as [I0 P0 O0].
          smash_eq n' n; hsimpl; attac.
  Qed.

  #[export] Hint Immediate deinstr_act : LTS.


  Lemma deinstr_act_do [MN0 MN1] [ma a] :
    MNAct_to_PNAct ma = Some a ->
    (MN0 =(ma)=> MN1) ->
    (deinstr MN0 =(a)=> deinstr MN1).
  Proof.
    intros.
    specialize (deinstr_act `(MN0 =(_)=> _)) as ?.
    rewrite `(_ = Some _) in *.
    auto.
  Qed.


  Lemma deinstr_act_skip [MN0 MN1] [ma] :
    MNAct_to_PNAct ma = None ->
    (MN0 =(ma)=> MN1) ->
    deinstr MN0 = deinstr MN1.
  Proof.
    intros.
    specialize (deinstr_act `(MN0 =(_)=> _)) as ?.
    rewrite `(_ = None) in *.
    auto.
  Qed.

  #[export] Hint Resolve deinstr_act_do deinstr_act_skip : LTS.


  (** Process path is replicable under serv_deinstrumentation *)
  Theorem transp_sound : forall [mnpath] [MN0 MN1 : MNet],
      (MN0 =[ mnpath ]=> MN1) ->
      exists pnpath,
        (deinstr MN0 =[pnpath]=> deinstr MN1).

  Proof.
    induction mnpath; intros.
    kill H.
    exists []. constructor.

    kill H.
    rename T0 into TNM0.
    rename T1 into TNM1.
    rename N1 into MN0'.

    destruct (transp_sound1 TNM0) as (pnpath0 & TN0).
    apply (IHmnpath) in TNM1 as (pnpath1 & TN1).

    exists (pnpath0 ++ pnpath1).
    eauto with LTS.
  Qed.


  Fact assg_mq_Clear : forall a, MQ_Clear (assg_mq a).
  Proof. destruct a; attac. Qed.
  #[export] Hint Resolve assg_mq_Clear : LTS. (* TODO to Model *)

  (** Soundness of network transparency *)
  Theorem transp_sound_instr : forall {mnpath0} {I0} {N0 : PNet} {MN1 : MNet},
      (apply_instr I0 N0 =[ mnpath0 ]=> MN1) ->
      exists mnpath1 pnpath I2 N2,
        (MN1 =[ mnpath1 ]=> apply_instr I2 N2)
        /\ (N0 =[ pnpath ]=> N2).

  Proof.
    intros *.
    intros NTM0.

    assert (forall n, not (In n (path_particip mnpath0)) -> flushed_in n MN1) as HF1.
    {
      intros.
      specialize (path_particip_stay H NTM0) as ?.
      unfold flushed_in. rewrite <- H0.
      unfold apply_instr in *.
      rewrite NetMod.get_map in *.
      rewrite H0.
      unfold Flushed.
      unfold instr_for in *.
      destruct (I0).
      rewrite <- H0.
      attac.
    }

    assert (forall n : Name, ~ In n (path_particip mnpath0) -> ready_in n MN1) as HRd1.
    {
      intros.
      specialize (path_particip_stay H NTM0) as ?.
      unfold ready_in. rewrite <- H0.
      unfold apply_instr in *.
      rewrite NetMod.get_map in *.
      rewrite H0.
      unfold instr_for in *.
      destruct (I0).
      attac.
    }

    specialize (path_particip_stay) as ?.
    destruct (Net_flush_exists MN1 HF1 HRd1) as (mnpath1 & I1 & N2 & NTM1).

    assert (apply_instr I0 N0 =[ mnpath0 ++ mnpath1 ]=> apply_instr I1 N2) as NTM by attac.

    consider (exists pnpath, deinstr (apply_instr I0 N0) =[ pnpath ]=> deinstr (apply_instr I1 N2)) by eauto using transp_sound.

    exists mnpath1, pnpath, I1, N2.
    attac.
  Qed.


  (** Completeness over NV: tau case. *)
  Lemma Net_Vis_Transp_completeness_tau : forall (I : instr) {n : Name} {N0 N1 : PNet},
      (NVTrans n Tau N0 N1) ->
      (NVTrans n (MActP Tau) (apply_instr I N0) (apply_instr I N1)).

  Proof.
    intros.
    inversion H. subst.
    apply (Transp_completeness_tau (instr_for &I n)) in H0.
    repeat constructor; auto.

    unfold apply_instr.
    unfold instr_for.
    rewrite NetMod.put_map.
    attac.
  Qed.


  Lemma mactm_invariant_serv_deinstr : forall [n ma MN0 MN1],
      (MN0 =(NTau n (MActM ma))=> MN1) ->
      deinstr MN0 = deinstr MN1.

  Proof.
    intros *. intros TN.
    kill TN.
    now apply Net_Vis_corr_mon in H0.
  Qed.


  Lemma mcomm_invariant_serv_deinstr : forall [n n' t0] [m : Msg] [MN0 MN1 : MNet],
      (MN0 =(NComm n n' t0 (MValM m))=> MN1) ->
      deinstr MN0 = deinstr MN1.

  Proof.
    intros *. intros TN.
    kill TN.
    apply Net_Vis_corr_mon in H.
    apply Net_Vis_corr_mon in H0.
    etransitivity; eauto.
  Qed.


  Lemma apply_instr_flushed : forall I N, flushed (apply_instr I N).

  Proof.
    intros.
    unfold apply_instr.
    unfold flushed.
    unfold instr_for.
    unfold flushed_in.
    intros.
    rewrite NetMod.get_map.
    attac.
  Qed.

  #[export] Hint Resolve apply_instr_flushed : LTS.


  Lemma apply_instr_ready_net : forall I N, ready_net (apply_instr I N).

  Proof.
    intros.
    unfold apply_instr.
    unfold ready_net.
    unfold instr_for.
    unfold ready_in.
    intros.
    rewrite NetMod.get_map.
    attac.
  Qed.

  #[export] Hint Resolve apply_instr_ready : LTS.

  Lemma get_instr : forall [n] N I,
      instr_for I n (NetMod.get n N) = NetMod.get n (apply_instr I N).

  Proof.
    intros.
    unfold apply_instr in *.
    unfold instr_for in *.
    rewrite NetMod.get_map.
    attac.
  Qed.


  (** If a node can perform a sequence of flushing and nil-corr actions, then the network can too. *)
  Lemma admin_path_available1' : forall
      [ma] [MQ0 M0 S0] [MQ1 M1 S1] n I0 N0,
      [ma] >:~ [] ->
      Flushing_act ma ->
      (mserv MQ0 M0 S0 =(ma)=> mserv MQ1 M1 S1) ->
      exists nmpath I1 MQ',
        (NetMod.put n (mserv MQ0 M0 S0) (apply_instr I0 N0)
         =[nmpath]=>
           NetMod.put n (mserv (MQ1 ++ MQ') M1 S1) (apply_instr I1 N0)
        )
        /\ MQ_Clear MQ'.

  Proof.
    intros *. intros HC HF TM.

    kill TM; kill HC; kill HF; try (destruct n0 as [n0 t0]).
    - unshelve eexists [NComm n n0 t0 _]. apply (MValM msg).

      assert (NetMod.get n (NetMod.put n (mserv MQ1 M0 S1) (apply_instr I0 N0))
              =(MActM (Send (n0, t0) msg))=>
                (mserv MQ1 M1 S1)
             ).
      repeat (rewrite NetMod.get_put_eq).
      constructor. assumption.
      apply NT_Vis in H0.
      rewrite NetMod.put_put_eq in H0.
      rename H0 into NT_send.

      destruct (NetMod.get n0 (NetMod.put n (mserv MQ1 M1 S1) (apply_instr I0 N0)))
        as [MQr Mr Sr] eqn:HeqR.

      assert (NetMod.get n0 (NetMod.put n (mserv MQ1 M1 S1) (apply_instr I0 N0))
              =(MActM (Recv (n, t0) msg))=>
                (mserv (MQr ++ [MqProbe (n, t0) msg]) Mr Sr)
             ).
      rewrite HeqR.
      constructor.

      apply NT_Vis in H0.
      rename H0 into NT_recv.

      destruct (NAME.eq_dec n0 n); subst.
      + rewrite NetMod.put_put_eq in NT_recv.
        rewrite NetMod.get_put_eq in HeqR.
        kill HeqR.
        exists I0, [MqProbe (n, t0) msg].

        split; repeat constructor.

        apply path_seq0.

        replace (MActM _) with (send (n, t0) (MValM msg)) in NT_send; auto.
        replace (MActM _) with (recv (n, t0) (MValM msg)) in NT_recv; auto.

        apply (NT_Comm NT_send NT_recv).

      + rewrite NetMod.put_put_neq in NT_recv; auto.
        rewrite NetMod.get_put_neq in HeqR; auto.

        assert (MQ_Clear (MQr ++ [MqProbe (n, t0) msg])) as HMQr.
        {
          specialize (apply_instr_flushed I0 N0 n0) as ?.
          unfold flushed_in in H0.
          rewrite HeqR in H0.
          apply Forall_app; split; attac.
        }

        assert (ready Mr) as HMr.
        {
          specialize (apply_instr_ready_net I0 N0 n0) as HR.
          unfold ready_in in HR.
          rewrite HeqR in HR.
          apply HR...
        }

        pose (instr_
            (fun n' =>
              if NAME.eqb n0 n'
              then _mon_assg (MQr ++ [MqProbe (n, t0) msg]) HMQr Mr
              else instr_for I0 n'
          )) as I1; simpl.

        exists I1, [].

        rewrite app_nil_r.
        split; try constructor.

        apply path_seq0.
        replace (MActM _) with (send (n0, t0) (MValM msg)) in NT_send; auto.
        replace (MActM _) with (recv (n, t0) (MValM msg)) in NT_recv; auto.

        specialize (NT_Comm NT_send NT_recv) as ?.

        assert ( (I1 N0) = (NetMod.put n0 (mserv (MQr ++ [MqProbe (n, t0) msg]) Mr Sr) (apply_instr I0 N0))).
        {
          unfold apply_instr.
          specialize (conscious_replace n0
                        (instr_for I0)
                        (fun n' S' => instr_for I1 n' S')
                        N0
                     ) as Kek.
          simpl in Kek.

          assert (NetMod.get n0 N0 = Sr) as HeqSr.
          {
            unfold apply_instr in HeqR.
            unfold instr_for in HeqR.
            rewrite NetMod.get_map in HeqR.
            destruct (instr_for I0 n0).
            destruct (NetMod.get n0 N0).
            kill HeqR.
          }

          subst I1.

          rewrite <- HeqSr.

          apply NetMod.extensionality.
          intros.
          repeat (rewrite NetMod.get_map).

          destruct (NAME.eqb n0 n2) eqn:HEq01; auto.
          destruct (NAME.eqb n0 n0) eqn:?; attac.
          destruct (NAME.eqb n0 n0) eqn:?; attac.
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

      assert (NetMod.get n (NetMod.put n (mserv (MqProbe (n0, t0) v :: MQ1) M0 S1) (apply_instr I0 N0))
              =(MActM Tau)=>
                (mserv MQ1 M1 S1)
             ).
      repeat (rewrite NetMod.get_put_eq).
      constructor. assumption.

      apply (NT_Vis) in H0.
      rewrite NetMod.put_put_eq in H0.
      apply H0.

    - exists [NTau n (MActP (Recv (n0, t0) v))].
      exists I0, [].

      rewrite app_nil_r.
      split; try constructor.

      apply path_seq0.
      constructor.
      constructor.

      assert (NetMod.get n (NetMod.put n (mserv (MqRecv (n0, t0) v :: MQ1) M0 S0) (apply_instr I0 N0))
              =(MActP (Recv (n0, t0) v))=>
                (mserv MQ1 M1 S1)
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
      (mserv MQ0 M0 S0 =[mpath]=> mserv MQ1 M1 S1) ->
      exists nmpath I1 MQ',
        (NetMod.put n (mserv MQ0 M0 S0) (apply_instr I0 N0)
         =[nmpath]=>
           NetMod.put n (mserv (MQ1 ++ MQ') M1 S1) (apply_instr I1 N0)
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

    assert (mserv (MQ0' ++ MQ'0') M0' S0' =[ mpath ]=> mserv (MQ1 ++ MQ'0') M1 S1) by eauto using Flushing_cont.

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
      (mserv MQ0 M0 S0 =(ma)=> mserv MQ1 M1 S1) ->
      flushed MN0 ->
      exists nmpath MQ' MN1,
        (NetMod.put n (mserv MQ0 M0 S0) MN0
         =[nmpath]=>
           NetMod.put n (mserv (MQ1 ++ MQ') M1 S1) MN1
        )
        /\ flushed MN1
        /\ deinstr MN0 = deinstr MN1
        /\ MQ_Clear MQ'.

  Proof with eattac.
    intros *. intros HC HF TM HFN0.

    kill TM; kill HC; kill HF; try (destruct n0 as [n0 t0]).
    - unshelve eexists [NComm n n0 t0 _]. apply (MValM msg).

      hsimpl in *.
      smash_eq n n0.
      + exists [MqProbe (n, t0) msg], MN0.
        hsimpl; hsimpl; eattac.
        eapply NTrans_Comm_eq_inv. hsimpl.
        eexists _, _. eattac; constructor. 

      (* + eexists [], _. *)
      (* repeat split. TODO bug report? why does this instantiate evar? *)
      + destruct (NetMod.get n0 MN0) as [MQr0 Mr0 Sr0] eqn:?.
        eexists [], (NetMod.put n0 (mserv (MQr0 ++ [MqProbe (n, t0) msg]) Mr0 Sr0) MN0).
        eattac.
        * eapply NTrans_Comm_neq_inv; auto.
          ltac1:(autorewrite with LTS in * ).
          exists (mserv MQ1 M1 S1).
          exists (mserv (MQr0 ++ [MqProbe (n, t0) msg]) Mr0 Sr0).
          eattac.
          rewrite NetMod.put_put_neq; eattac.

        * unfold flushed, flushed_in, Flushed in *.
          intros.
          specialize (HFN0 n1).
          smash_eq n n0 n1; ltac1:(autorewrite with LTS_concl); attac.
        * unfold deinstr in *.
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
      (mserv MQ0 M0 S0 =[mpath]=> mserv MQ1 M1 S1) ->
      flushed MN0 ->
      exists nmpath MQ' MN1,
        (NetMod.put n (mserv MQ0 M0 S0) MN0
         =[nmpath]=>
           NetMod.put n (mserv (MQ1 ++ MQ') M1 S1) MN1
        )
        /\ flushed MN1
        /\ deinstr MN0 = deinstr MN1
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


  Lemma Transp_completeness_send_old : forall [n v] [S0 S1] (a : mon_assg),
      (S0 =( Send n v )=> S1) -> exists mpath M1,
      (a S0 =[MActP (Send n v) :: mpath ++ [MActT (Send n v)]]=> (mserv [] M1 S1))
      /\ mpath >:~ []
      /\ Forall Flushing_act mpath.

  Proof.
    intros.
    specialize (Transp_completeness_send_instr a H) as TM.
    unfold flush_path in *.
    exists (mk_flush_path (assg_mq a) (MRecv (assg_m a))).
    exists (mon_handle (MqSend n v) (flush_Mstate (assg_mq a) (MRecv (assg_m a)))).
    eattac.
  Qed.


  Lemma prepare_send : forall I0 [N0 : PNet] [n n' v S1],
      (NetMod.get n N0 =(send n' v)=> S1) ->
      exists mnpath I1 MQ1 M1 MN1,
        (apply_instr I0 N0 =[mnpath]=> MN1)
        /\ NVTrans n (send n' (MValP v)) MN1 (NetMod.put n (mserv MQ1 M1 S1) (apply_instr I1 N0))
        /\ N0 = deinstr MN1
        /\ MQ_Clear MQ1.

  Proof.
    intros *. intros T.

    destruct (Transp_completeness_send_old (instr_for I0 n) T)
      as (mpath_flush & M1 & TM & HC0 & HF0).

    apply path_split1 in TM as (MS_sentp & TM_sendp & TM).
    apply path_split in TM as (MS_flush & TM_flush & TM_sendm).

    rewrite (get_instr) in TM_sendp.

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

    exists (mon_handle (MqSend n' v) s).
    eexists (NetMod.put n (mserv (MqSend n' v :: MQ') (MRecv s) _) (apply_instr I1 N0)).

    eattac.
    - eapply NVTrans_inv.
      eattac.
    - apply NetMod.extensionality.
      intros.
      unfold deinstr.
      smash_eq n n0.
      + rewrite NetMod.put_map.
        rewrite NetMod.get_put_eq.
        hsimpl in |- *.
        kill T.
        attac.
      + unfold apply_instr.
        hsimpl in |- *.
        destruct (instr_for I1 n0).
        hsimpl; attac.
  Qed.

  Lemma Transp_completeness_recv_old : forall [n v] [S0 S1] MQ0 M0,
      MQ_Clear MQ0 ->
      (S0 =( Recv n v )=> S1) ->
      exists mpath M1,
        (mserv MQ0 M0 S0 =[MActT (Recv n v) :: mpath]=> mserv [MqRecv n v] M1 S0)
        /\ mpath >:~ []
        /\ Forall Flushing_act mpath
        /\ ready M1.

  Proof.
    intros.
    specialize (@Transp_completeness_recv n v S0 S1 MQ0 M0 H H0) as TM.
    unfold flush_path in *.
    unfold flush_M.
    exists (mk_flush_path MQ0 M0).
    attac.
    exists (MRecv s).
    attac.
  Qed.


  Lemma prepare_recv : forall [MN0 : MNet] [n n' v] [S1],
      (NetMod.get n (deinstr MN0) =(recv n' v)=> S1) ->
      flushed MN0 ->
      exists mnpath MS0 MQ1 M1 MN1,
        NVTrans n (recv n' (MValP v)) MN0 (NetMod.put n MS0 MN0)
        /\ ((NetMod.put n MS0 MN0) =[mnpath]=> (NetMod.put n (mserv MQ1 M1 S1) MN1))
        /\ deinstr MN0 = deinstr MN1
        /\ MQ_Clear MQ1
        /\ flushed MN1.

  Proof.
    intros *. intros T0 HFN0.

    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:HEq0.
    unfold deinstr in T0.
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

    apply path_split1 in TM as ([MQ1' M1' S1'] & TM0 & TM1).

    assert (NVTrans n (recv n' (MValP v)) MN0 (NetMod.put n (mserv MQ1' M1' S1') MN0)) as TNM0.
    {
      eattac.
      hsimpl in *.
      rewrite HEq0.
      unfold serv_deinstr.
      destruct S0.
      attac.
    }

    assert (exists M2, mserv [MqRecv n' v] M1 (serv_deinstr (NetMod.get n MN0)) =(MActP (Recv n' v))=> mserv [] M2 S1)
      as (M2 & TM2).
    {
      hsimpl in *.
      exists (mon_handle (MqRecv n' v) s).
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

    assert (serv_deinstr (NetMod.get n MN0) = S0) as HEqS0 by attac.

    repeat (rewrite HEqS0 in * ). clear HEqS0.

    exists (mnpath ++ [NTau n (MActP (Recv n' v))]).
    exists ((mserv MQ1' M1' S1')).
    exists MQ2, M2.
    exists MN2.

    repeat split; eauto with LTS.
    - rewrite HEq0 in *.
      attac.
    - apply path_seq1' with (middle := NetMod.put n (mserv ([MqRecv n' v] ++ MQ2) M1 S0) MN2).
      1: attac.

      replace (mserv ([MqRecv n' v] ++ MQ2) M1 S0)
        with (NetMod.get n (NetMod.put n (mserv ([MqRecv n' v] ++ MQ2) M1 S0)  MN2))
        in TM2 by attac.
      constructor. constructor.

      apply NT_Vis in TM2.
      rewrite NetMod.put_put_eq in TM2.
      attac.
  Qed.


  Lemma put_instr : forall (I0 : instr) N0 n [MQ M S],
      MQ_Clear MQ ->
      ready M ->
      exists I1 : instr, NetMod.put n (mserv MQ M S) (apply_instr I0 N0) = apply_instr I1 (NetMod.put n S N0).

  Proof.
    intros * HMQ HM.

    assert (flushed (NetMod.put n (mserv MQ M &S) (apply_instr I0 N0))) as HFN.
    {
      unfold flushed, flushed_in.
      intros n0.
      specialize (apply_instr_flushed I0 N0 n0) as HF.
      smash_eq n n0; attac.
    }

    assert (ready_net (NetMod.put n (mserv MQ M &S) (apply_instr I0 N0))) as HRN.
    {
      unfold ready_net, ready_in.
      intros n0.
      specialize (apply_instr_ready_net I0 N0 n0) as HR.
      smash_eq n n0; attac.
    }

    destruct (flushed_ready_instr HFN HRN) as (I1, HEq).
    exists I1.
    rewrite HEq.
    specialize instr_inv as HNDI.
    unfold apply_instr, deinstr in *.
    repeat (rewrite NetMod.put_map in * ).
    repeat (rewrite HNDI).
    destruct &S.
    eattac.
  Qed.


  (** Network transparency completeness over a single action *)
  Lemma transp_complete1 : forall I0 {na} {N0 N1 : PNet},
      (N0 =(na)=> N1) ->
      exists nmpath I1,
        (apply_instr I0 N0 =[nmpath]=> apply_instr I1 N1).

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

      remember (NetMod.put n (mserv MQ_n M_n Sn) (apply_instr I1 N0)) as MN1'.

      assert (flushed MN1') as HFN1'.
      specialize (apply_instr_flushed I1 N0) as HFN0.
      unfold flushed in *. intros. subst MN1'.
      unfold flushed_in.
      destruct (NAME.eq_dec n0 n); subst.
      rewrite NetMod.get_put_eq. auto.
      rewrite NetMod.get_put_neq; auto. apply HFN0.

      assert ( (deinstr MN1') = NetMod.put n Sn N0) as HND0.
      {
        unfold deinstr.
        rewrite HeqMN1'.
        assert (serv_deinstr (mserv MQ_n M_n Sn) = Sn).
        unfold serv_deinstr.
        destruct Sn. eattac.
        rewrite NetMod.put_map.
        specialize (instr_inv) as HNDI.
        unfold apply_instr in *.
        unfold deinstr in *.
        rewrite HNDI.
        rewrite H.
        reflexivity.
      }
      rewrite <- HND0 in T_recv.

      specialize (apply_instr_ready I0 (deinstr MN1)) as HRC0.
      rewrite <- HND1 in HRC0.

      destruct (prepare_recv T_recv HFN1')
        as (mnpath1 & MS_m0 & MQ_m & M_m & MN3' & TN_recv & TN2 & HND2 & HMQ_m & HFN3').

      remember (NetMod.put m MS_m0 MN1') as MN2.
      remember (NetMod.put m (mserv MQ_m M_m Sm) MN3') as MN3.

      replace ( (MActT (Send (m, t) v)))
        with (send (m, t) (MValP v))
        in TN_send; eauto.

      assert (@trans _ _ (@trans_net _ _ _ trans_mserv)
                (NComm n m t (MValP v)) MN1 MN2) as TN1.
      eapply (NT_Comm TN_send TN_recv).
      apply path_seq0 in TN1.

      assert (forall n', not (In n' (path_particip mnpath0
                                  ++ path_particip [NComm n m t (MValP v)]
                                  ++ path_particip mnpath1)
                      ) ->
                    ready_in n' MN3
             ) as HRd3.
      {
        intros.
        apply not_in_app_inv in H as (NI_part0 & H).
        apply not_in_app_inv in H as (NI_part1 & NI_part2).
        specialize (path_particip_stay NI_part0 TN0) as HStay0.
        specialize (path_particip_stay NI_part1 TN1) as HStay1.
        specialize (path_particip_stay NI_part2 TN2) as HStay2.
        unfold ready_in in *. rewrite <- HStay2.
        unfold ready_in in *. rewrite <- HStay1.
        unfold ready_in in *. rewrite <- HStay0.
        unfold apply_instr. rewrite NetMod.get_map.
        unfold instr_for.
        destruct (instr_for I0 n'). unfold serv_instr. simpl. auto.
        attac.
      }

      assert (flushed MN3) as HFN3.
      {
        specialize (apply_instr_flushed I0 N0) as HNF0.
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
      }

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
      unfold deinstr in TN3.
      subst.
      rewrite NetMod.put_map in TN3.
      unfold deinstr in HND2.
      rewrite <- HND2 in TN3.
      rewrite NetMod.put_map in TN3.

      assert (serv_deinstr (mserv MQ_n M_n Sn) = Sn).
      {
        unfold serv_deinstr.
        destruct Sn. clear - HMQ_n. eattac.
      }

      assert (serv_deinstr (mserv MQ_m M_m Sm) = Sm).
      {
        unfold serv_deinstr.
        destruct Sm. simpl. clear - HMQ_m. eattac.
      }

      rewrite H in *.
      rewrite H0 in *.
      subst.
      specialize instr_inv as HNDI.
      unfold apply_instr in *.
      unfold deinstr in *.

      repeat (rewrite NetMod.put_map in * ).
      repeat (rewrite HNDI in * ).

      apply TN3.
  Qed.


  (** Network transparency completeness *)
  Theorem transp_complete : forall {path} I0 {N0 N1 : PNet},
      (N0 =[ path ]=> N1) ->
      exists mpath I1,
        (apply_instr I0 N0 =[ mpath ]=> apply_instr I1 N1).

  Proof with attac.
    induction path; intros.
    1: exists [], I0...

    kill H.
    apply (transp_complete1 I0) in T0 as (mpath0 & I0' & NT0).
    apply (IHpath I0') in T1 as (mpath1 & I1 & NT1). clear IHpath.

    exists (mpath0 ++ mpath1), I1...
  Qed.


End TRANSP_F.

Module Type TRANSP(Conf : TRANSP_CONF) := Conf <+ TRANSP_PARAMS <+ TRANSP_F.
