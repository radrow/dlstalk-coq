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
Require Import DlStalk.Model.
Require Import DlStalk.ModelData.
Require Import DlStalk.Network.
Require Import DlStalk.SRPC.
Require Import DlStalk.Que.
Require Import DlStalk.Locks.
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

Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.

Import ListNotations.
Import BoolNotations.

Require Import DlStalk.Compl.


Module Type SOUND_F(Import Conf : DETECT_CONF)(Import Params : DETECT_PARAMS(Conf)).
  Include COMPL_F(Conf)(Params).
  Module Import NT := NetTactics(Conf)(Params.NetLocks.Net).

  Import SrpcDefs.
  Import SrpcNet.

  Section Inversions.
    (* These hints should not quadrate with SRPC_serv variants because SRPC_net does not expose
      SRPC_pq_in_net *)


    Lemma SRPC_M_net_AnySrpc [N S n] :
      net_sane '' N ->
      NetMod.get n N = S ->
      AnySRPC_serv S.
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *; hsimpl in *.
      kill H. eauto with LTS.
    Qed.


    (* TODO to Que *)
    Lemma Deq_app_l_not_Deq : forall [E : Set] [n : NameTag] [v] [Q0 Q1 Q1'],
        (forall (v' : E) Q0', ~ Deq n v' Q0 Q0') ->
        Deq n v Q1 Q1' ->
        Deq n v (Q0 ++ Q1) (Q0 ++ Q1').

    Proof.
      intros.
      generalize dependent Q1 Q1'.
      induction Q0; attac.
      destruct a.
      econstructor 3; iattac.
      eapply IHQ0; iattac.
      assert (~ Deq n v' ((n0, e)::Q0) ((n0, e)::Q0')); auto.
      apply H2.
      econstructor 3; iattac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_in_M [N n c v v' MQ0 MQ1 M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv (MQ0 ++ TrRecv (c, Q) v :: MQ1) M (serv I P O) ->
      ~ List.In (c, Q, v') (I ++ MQ_r (MQ0 ++ MQ1)).

    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      hsimpl in *.
      unfold net_deinstr, deinstr in *; hsimpl in *.
      rewrite MQ_r_app.
      remember (MQ_r MQ1) as I1 eqn:x; clear x.
      repeat (rewrite (app_assoc) in * ).
      remember (&I ++ MQ_r MQ0) as I0 eqn:x; clear x.
      destruct (Deq_dec' I0 (c, Q)); hsimpl in *.
      - rename Q' into I0'.
        assert (Deq (c, Q) v0 (I0 ++ (c, Q, v) :: I1) (I0' ++ (c, Q, v) :: I1)) by attac.
        bs (~ List.In (c, Q, v) (I0' ++ (c, Q, v) :: I1)).
      - assert (Deq (c, Q) v ((c, Q, v) :: I1) I1) by attac.
        bs (Deq (c, Q) v (I0 ++ (c, Q, v) :: I1) (I0 ++ I1)) by eauto using Deq_app_l_not_Deq.
    Qed.

    Lemma SRPC_M_net_in_net_Q_in_M0 [N n c v v' MQ0 MQ1 M S] :
      net_sane '' N ->
      NetMod.get n N = mserv (MQ0 ++ TrRecv (c, Q) v :: MQ1) M S ->
      ~ List.In (TrRecv (c, Q) v') MQ0.
    Proof. intros. destruct S as [I P O].
           assert (~ List.In (c, Q, v') (&I ++ MQ_r (MQ0 ++ MQ1))) by eauto using SRPC_M_net_in_net_Q_in_M.
           iattac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_in_M1 [N n c v v' MQ0 MQ1 M S] :
      net_sane '' N ->
      NetMod.get n N = mserv (MQ0 ++ TrRecv (c, Q) v :: MQ1) M S ->
      ~ List.In (TrRecv (c, Q) v') MQ1.
    Proof. intros. destruct S as [I P O].
           assert (~ List.In (c, Q, v') (&I ++ MQ_r (MQ0 ++ MQ1))) by eauto using SRPC_M_net_in_net_Q_in_M.
           iattac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_in_MP [N n c v v' MQ0 MQ1 M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv (MQ0 ++ TrRecv (c, Q) v :: MQ1) M (serv I P O) ->
      ~ List.In (c, Q, v') I.
    Proof. intros.
           assert (~ List.In (c, Q, v') (&I ++ MQ_r (MQ0 ++ MQ1))) by eauto using SRPC_M_net_in_net_Q_in_M.
           iattac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_in_P [N n c v v' MQ M I I' P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (c, Q) v I I' ->
      ~ List.In (c, Q, v') (I' ++ MQ_r MQ).

    Proof.
      intros.
      kill H. specialize (H_Sane_SRPC n) as [srpc H].
      hsimpl in *.
      unfold net_deinstr, deinstr in *; hsimpl in *.
      assert (Deq (c, Q) v (&I ++ MQ_r MQ) (I' ++ MQ_r MQ)) by attac.
      iattac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_in_PP [N n c v v' MQ M I I' P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (c, Q) v I I' ->
      ~ List.In (c, Q, v') I'.
    Proof. intros.
           assert (~ List.In (c, Q, v') (&I' ++ MQ_r MQ)) by eauto using SRPC_M_net_in_net_Q_in_P.
           iattac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_in_PM [N n c v v' MQ M I I' P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (c, Q) v I I' ->
      ~ List.In (TrRecv (c, Q) v') MQ.
    Proof. intros.
           assert (~ List.In (c, Q, v') (&I' ++ MQ_r MQ)) by eauto using SRPC_M_net_in_net_Q_in_P.
           iattac.
    Qed.

    Lemma SRPC_M_net_in_net_R_in_M [N n s s' v v' MQ0 MQ1 M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv (MQ0 ++ TrRecv (s, R) v :: MQ1) M (serv I P O) ->
      ~ List.In (s', R, v') (I ++ MQ_r (MQ0 ++ MQ1)).

    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      hsimpl in *.
      unfold net_deinstr, deinstr in *; hsimpl in *.
      remember (MQ_r MQ1) as I1 eqn:x; clear x.
      repeat (rewrite (app_assoc) in * ).
      remember (&I ++ MQ_r MQ0) as I0 eqn:x; clear x.

      destruct (Deq_dec' I0 (s, R)); hsimpl in *.
      - rename Q' into I0'.
        assert (Deq (s, R) v0 (I0 ++ (s, R, v) :: I1) (I0' ++ (s, R, v) :: I1)) by attac.
        bs (~ List.In (s, R, v) (I0' ++ (s, R, v) :: I1)).
      - assert (Deq (s, R) v ((s, R, v) :: I1) I1) by attac.
        assert (Deq (s, R) v (I0 ++ (s, R, v) :: I1) (I0 ++ I1)) by eauto using Deq_app_l_not_Deq.
        bs (~ List.In (s', R, v) (I0 ++ I1)).
    Qed.

    Lemma SRPC_M_net_in_net_R_in_M0 [N n s s' v v' MQ0 MQ1 M S] :
      net_sane '' N ->
      NetMod.get n N = mserv (MQ0 ++ TrRecv (s, R) v :: MQ1) M S ->
      ~ List.In (TrRecv (s', R) v') MQ0.
    Proof.
      intros. destruct S as [I P O].
      assert (~ List.In (s', R, v') (&I ++ MQ_r (MQ0 ++ MQ1))) by eauto using SRPC_M_net_in_net_R_in_M.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_in_M1 [N n s s' v v' MQ0 MQ1 M S] :
      net_sane '' N ->
      NetMod.get n N = mserv (MQ0 ++ TrRecv (s, R) v :: MQ1) M S ->
      ~ List.In (TrRecv (s', R) v') MQ1.
    Proof.
      intros. destruct S as [I P O].
      assert (~ List.In (s', R, v') (&I ++ MQ_r (MQ0 ++ MQ1))) by eauto using SRPC_M_net_in_net_R_in_M.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_in_MP [N n s s' v v' MQ0 MQ1 M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv (MQ0 ++ TrRecv (s, R) v :: MQ1) M (serv I P O) ->
      ~ List.In (s', R, v') I.
    Proof.
      intros.
      assert (~ List.In (s', R, v') (&I ++ MQ_r (MQ0 ++ MQ1))) by eauto using SRPC_M_net_in_net_R_in_M.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_in_P [N n s s' v v' MQ M I I' P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (s, R) v I I' ->
      ~ List.In (s', R, v') (I' ++ MQ_r MQ).

    Proof.
      intros.
      kill H. specialize (H_Sane_SRPC n) as [srpc H].
      hsimpl in *.
      unfold net_deinstr, deinstr in *; hsimpl in *.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_in_PP [N n s s' v v' MQ M I I' P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (s, R) v I I' ->
      ~ List.In (s', R, v') I'.
    Proof.
      intros.
      assert (~ List.In (s', R, v') (&I' ++ MQ_r MQ)) by eauto using SRPC_M_net_in_net_R_in_P.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_in_PM [N n s s' v v' MQ M I I' P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (s, R) v I I' ->
      ~ List.In (TrRecv (s', R) v') MQ.
    Proof.
      intros.
      assert (~ List.In (s', R, v') (&I' ++ MQ_r MQ)) by eauto using SRPC_M_net_in_net_R_in_P.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_in_lock [N n s v MQ M S] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M S ->
      List.In (TrRecv (s, R) v) MQ ->
      exists c, SRPC_serv (Lock c s) (NetMod.get n N).
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *.
      hsimpl in *.
      consider (exists c, srpc = Lock c s); eattac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_out_lock [N n s v MQ M S] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M S ->
      List.In (TrSend (s, Q) v) MQ ->
      exists c, SRPC_serv (Lock c s) (NetMod.get n N).
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *.
      hsimpl in *.
      consider (exists c, srpc = Lock c s); eattac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_out_uniq_M [N n c v v' MQ0 MQ1 M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv (MQ0 ++ TrSend (c, R) v :: MQ1) M (serv I P O) ->
      ~ List.In (c, R, v') (MQ_s (MQ0 ++ MQ1) ++ O).

    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      hsimpl in *.
      unfold net_deinstr, deinstr in *; hsimpl in *.
      repeat (rewrite <- app_assoc in * ).
      repeat (rewrite <- app_comm_cons in * ).
      remember (MQ_s MQ1 ++ &O) as O1 eqn:x; clear x.
      remember (MQ_s MQ0) as O0 eqn:x; clear x.

      destruct (Deq_dec' O0 (c, R)); hsimpl in *.
      - rename Q' into O0'.
        assert (Deq (c, R) v0 (O0 ++ (c, R, v) :: O1) (O0' ++ (c, R, v) :: O1)) by attac.
        bs (~ List.In (c, R, v) (O0' ++ (c, R, v) :: O1)).
      - assert (Deq (c, R) v ((c, R, v) :: O1) O1) by attac.
        assert (Deq (c, R) v (O0 ++ (c, R, v) :: O1) (O0 ++ O1)) by eauto using Deq_app_l_not_Deq.
        bs (~ List.In (c, R, v) (O0 ++ O1)).
    Qed.

    Lemma SRPC_M_net_in_net_Q_out_uniq_M0 [N n c v v' MQ0 MQ1 M S] :
      net_sane '' N ->
      NetMod.get n N = mserv (MQ0 ++ TrSend (c, R) v :: MQ1) M S ->
      ~ List.In (TrSend (c, R) v') MQ0.
    Proof.
      intros. destruct S as [I P O].
      assert (~ List.In (c, R, v') (MQ_s (MQ0 ++ MQ1) ++ &O)) by eauto using SRPC_M_net_in_net_Q_out_uniq_M.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_out_uniq_M1 [N n c v v' MQ0 MQ1 M S] :
      net_sane '' N ->
      NetMod.get n N = mserv (MQ0 ++ TrSend (c, R) v :: MQ1) M S ->
      ~ List.In (TrSend (c, R) v') MQ1.
    Proof.
      intros. destruct S as [I P O].
      assert (~ List.In (c, R, v') (MQ_s (MQ0 ++ MQ1) ++ &O)) by eauto using SRPC_M_net_in_net_Q_out_uniq_M.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_out_uniq_MP [N n c v v' MQ0 MQ1 M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv (MQ0 ++ TrSend (c, R) v :: MQ1) M (serv I P O) ->
      ~ List.In (c, R, v') O.
    Proof.
      intros.
      assert (~ List.In (c, R, v') (MQ_s (MQ0 ++ MQ1) ++ &O)) by eauto using SRPC_M_net_in_net_Q_out_uniq_M.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_out_uniq_P [N n c v v' MQ M I P O O'] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (c, R) v O O' ->
      ~ (List.In (c, R, v') (MQ_s MQ ++ O')).
    Proof.
      intros.
      kill H. specialize (H_Sane_SRPC n) as [srpc H].
      hsimpl in *.
      unfold net_deinstr, deinstr in *; hsimpl in *.
      remember (MQ_s MQ) as O1 eqn:x; clear x.

      destruct (Deq_dec' O1 (c, R)); hsimpl in *.
      - rename Q' into O1'.
        assert (Deq (c, R) v0 (O1 ++ &O) (O1' ++ &O)) by attac.
        assert (~ List.In (c, R, v) (O1' ++ &O)) by attac.
        bs (List.In (c, R, v) &O) by attac.
      - assert (Deq (c, R) v (O1 ++ &O) (O1 ++ O')) by eauto using Deq_app_l_not_Deq.
        bs (~ List.In (c, R, v) (O1 ++ O')).
    Qed.

    Lemma SRPC_M_net_in_net_Q_out_uniq_PM [N n c v v' MQ M I P O O'] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (c, R) v O O' ->
      ~ (List.In (TrSend (c, R) v') MQ).
    Proof.
      intros.
      assert (~ (List.In (c, R, v') (MQ_s MQ ++ O'))) by eauto using SRPC_M_net_in_net_Q_out_uniq_P.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_out_uniq_PP [N n c v v' MQ M I P O O'] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (c, R) v O O' ->
      ~ (List.In (c, R, v') O').
    Proof.
      intros.
      assert (~ (List.In (c, R, v') (MQ_s MQ ++ O'))) by eauto using SRPC_M_net_in_net_Q_out_uniq_P.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_Q_M [N n s v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (TrRecv (s, R) v) MQ ->
      ~ (List.In (s, Q, v') (MQ_s MQ ++ O)).
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *; hsimpl in *.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_Q_MM [N n s v v' MQ M S] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M S ->
      List.In (TrRecv (s, R) v) MQ ->
      ~ (List.In (TrSend (s, Q) v') MQ).
    Proof.
      intros. destruct S as [I P O].
      assert ( ~ (List.In (s, Q, v') (MQ_s MQ ++ &O))) by eauto using SRPC_M_net_in_net_R_Q_M.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_Q_MP [N n s v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (TrRecv (s, R) v) MQ ->
      ~ (List.In (TrSend (s, Q) v') MQ).
    Proof.
      intros.
      assert ( ~ (List.In (s, Q, v') (MQ_s MQ ++ &O))) by eauto using SRPC_M_net_in_net_R_Q_M.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_Q_P [N n s v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (s, R, v) I ->
      ~ (List.In (s, Q, v') (MQ_s MQ ++ O)).
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *; hsimpl in *.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_Q_PM [N n s v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (s, R, v) I ->
      ~ (List.In (TrSend (s, Q) v') MQ).
    Proof.
      intros.
      assert ( ~ (List.In (s, Q, v') (MQ_s MQ ++ &O))) by eauto using SRPC_M_net_in_net_R_Q_P.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_Q_PP [N n s v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (s, R, v) I ->
      ~ (List.In (s, Q, v') O).
    Proof.
      intros.
      assert (~ (List.In (s, Q, v') (MQ_s MQ ++ &O))) by eauto using SRPC_M_net_in_net_R_Q_P.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_R_M [N n s v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (TrSend (s, Q) v) MQ ->
      ~ (List.In (s, R, v') (I ++ MQ_r MQ)).
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *; hsimpl in *.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_R_MM [N n s v v' MQ M S] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M S ->
      List.In (TrSend (s, Q) v) MQ ->
      ~ (List.In (TrRecv (s, R) v') MQ).
    Proof.
      intros. destruct S as [I P O].
      assert ( ~ (List.In (s, R, v') (&I ++ MQ_r MQ))) by eauto using SRPC_M_net_in_net_Q_R_M.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_R_MP [N n s v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (TrSend (s, Q) v) MQ ->
      ~ (List.In (s, R, v') I).
    Proof.
      intros.
      assert ( ~ (List.In (s, R, v') (&I ++ MQ_r MQ))) by eauto using SRPC_M_net_in_net_Q_R_M.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_R_P [N n s v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (s, Q, v) O ->
      ~ (List.In (s, R, v') (I ++ MQ_r MQ)).
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *; hsimpl in *.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_R_PM [N n s v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (s, Q, v) O ->
      ~ (List.In (TrRecv (s, R) v') MQ).
    Proof.
      intros.
      assert ( ~ (List.In (s, R, v') (&I ++ MQ_r MQ))) by eauto using SRPC_M_net_in_net_Q_R_P.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_R_PP [N n s v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (s, Q, v) O ->
      ~ (List.In (s, R, v') I).
    Proof.
      intros.
      assert ( ~ (List.In (s, R, v') (&I ++ MQ_r MQ))) by eauto using SRPC_M_net_in_net_Q_R_P.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_excl_R_M [N n c v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (TrRecv (c, Q) v) MQ ->
      ~ List.In (c, R, v') (MQ_s MQ ++ O).
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *; hsimpl in *.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_excl_R_MM [N n c v v' MQ M S] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M S ->
      List.In (TrRecv (c, Q) v) MQ ->
      ~ List.In (TrSend (c, R) v') MQ.
    Proof.
      intros. destruct S as [I P O].
      assert (~ List.In (c, R, v') (MQ_s MQ ++ &O)) by eauto using SRPC_M_net_in_net_Q_excl_R_M.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_excl_R_MP [N n c v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (TrRecv (c, Q) v) MQ ->
      ~ List.In (c, R, v') O.
    Proof.
      intros.
      assert (~ List.In (c, R, v') (MQ_s MQ ++ &O)) by eauto using SRPC_M_net_in_net_Q_excl_R_M.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_excl_R_P [N n c v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (c, Q, v) I ->
      ~ List.In (c, R, v') (MQ_s MQ ++ O).
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *; hsimpl in *.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_excl_R_PM [N n c v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (c, Q, v) I ->
      ~ List.In (TrSend (c, R) v') MQ.
    Proof.
      intros.
      assert (~ List.In (c, R, v') (MQ_s MQ ++ &O)) by eauto using SRPC_M_net_in_net_Q_excl_R_P.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_excl_R_PP [N n c v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (c, Q, v) I ->
      ~ List.In (c, R, v') O.
    Proof.
      intros.
      assert (~ List.In (c, R, v') (MQ_s MQ ++ &O)) by eauto using SRPC_M_net_in_net_Q_excl_R_P.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_excl_c_M [N n c v MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (TrRecv (c, Q) v) MQ ->
      ~ proc_client c P.
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *; hsimpl in *.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_excl_c_P [N n c v MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (c, Q, v) I ->
      ~ proc_client c P.
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *; hsimpl in *.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_excl_Q_M [N n c v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (TrSend (c, R) v) MQ ->
      ~ List.In (c, Q, v') (I ++ MQ_r MQ).
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *; hsimpl in *.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_excl_Q_MM [N n c v v' MQ M S] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M S ->
      List.In (TrSend (c, R) v) MQ ->
      ~ List.In (TrRecv (c, Q) v') MQ.
    Proof.
      intros. destruct S as [I P O].
      assert (~ List.In (c, Q, v') (&I ++ MQ_r MQ)) by eauto using SRPC_M_net_in_net_R_excl_Q_M.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_excl_Q_MP [N n c v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (TrSend (c, R) v) MQ ->
      ~ List.In (c, Q, v') I.
    Proof.
      intros.
      assert (~ List.In (c, Q, v') (&I ++ MQ_r MQ)) by eauto using SRPC_M_net_in_net_R_excl_Q_M.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_excl_Q_P [N n c v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (c, R, v) O ->
      ~ List.In (c, Q, v') (I ++ MQ_r MQ).
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *; hsimpl in *.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_excl_Q_PM [N n c v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (c, R, v) O ->
      ~ List.In (TrRecv (c, Q) v') MQ.
    Proof.
      intros.
      assert (~ List.In (c, Q, v') (&I ++ MQ_r MQ)) by eauto using SRPC_M_net_in_net_R_excl_Q_P.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_excl_Q_PP [N n c v v' MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (c, R, v) O ->
      ~ List.In (c, Q, v') I.
    Proof.
      intros.
      assert (~ List.In (c, Q, v') (&I ++ MQ_r MQ)) by eauto using SRPC_M_net_in_net_R_excl_Q_P.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_excl_c_M [N n c v MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (TrRecv (c, Q) v) MQ ->
      ~ proc_client c P.
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *; hsimpl in *.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_excl_c_P [N n c v MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (c, Q, v) I ->
      ~ proc_client c P.
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *; hsimpl in *.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_c_excl_Q_M [N n c v MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      proc_client c P ->
      ~ List.In (TrRecv (c, Q) v) MQ.
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *; hsimpl in *.
      enough (~ In (c, Q, v) (&I ++ MQ_r MQ)) by attac.
      eattac.
    Qed.

    Lemma SRPC_M_net_in_net_c_excl_Q_P [N n c v MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      proc_client c P ->
      ~ List.In (c, Q, v) (I).
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *; hsimpl in *.
      enough (~ In (c, Q, v) (&I ++ MQ_r MQ)) by attac.
      iattac.
    Qed.

    Lemma SRPC_M_net_in_net_c_excl_R [N n c v MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      proc_client c P ->
      ~ List.In (c, R, v) (MQ_s MQ ++ O).
    Proof.
      intros. kill H. specialize (H_Sane_SRPC n) as [srpc H].
      unfold net_deinstr, deinstr in *; hsimpl in *.
      iattac.
    Qed.

    Lemma SRPC_M_net_in_net_c_excl_R_M [N n c v MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      proc_client c P ->
      ~ List.In (TrSend (c, R) v) MQ.
    Proof.
      intros.
      assert (~ List.In (c, R, v) (MQ_s MQ ++ &O)) by eauto using SRPC_M_net_in_net_c_excl_R.
      iattac.
    Qed.

    Lemma SRPC_M_net_in_net_c_excl_R_P [N n c v MQ M I P O] :
      net_sane '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      proc_client c P ->
      ~ List.In (c, R, v) O.
    Proof.
      intros.
      assert (~ List.In (c, R, v) (MQ_s MQ ++ &O)) by eauto using SRPC_M_net_in_net_c_excl_R.
      iattac.
    Qed.

  End Inversions.


  #[export] Hint Resolve
    SRPC_M_net_AnySrpc
    SRPC_M_net_in_net_Q_in_M0
    SRPC_M_net_in_net_Q_in_M1
    SRPC_M_net_in_net_Q_in_MP
    SRPC_M_net_in_net_Q_in_PM
    SRPC_M_net_in_net_Q_in_PP
    SRPC_M_net_in_net_R_in_M0
    SRPC_M_net_in_net_R_in_M1
    SRPC_M_net_in_net_R_in_MP
    SRPC_M_net_in_net_R_in_PM
    SRPC_M_net_in_net_R_in_PP
    SRPC_M_net_in_net_R_in_lock
    SRPC_M_net_in_net_Q_out_lock
    SRPC_M_net_in_net_Q_out_uniq_M0
    SRPC_M_net_in_net_Q_out_uniq_M1
    SRPC_M_net_in_net_Q_out_uniq_MP
    SRPC_M_net_in_net_Q_out_uniq_PM
    SRPC_M_net_in_net_Q_out_uniq_PP
    SRPC_M_net_in_net_R_Q_MM
    SRPC_M_net_in_net_R_Q_MP
    SRPC_M_net_in_net_R_Q_PM
    SRPC_M_net_in_net_R_Q_PP
    SRPC_M_net_in_net_Q_R_MM
    SRPC_M_net_in_net_Q_R_MP
    SRPC_M_net_in_net_Q_R_PM
    SRPC_M_net_in_net_Q_R_PP
    SRPC_M_net_in_net_Q_excl_R_MM
    SRPC_M_net_in_net_Q_excl_R_MP
    SRPC_M_net_in_net_Q_excl_R_PM
    SRPC_M_net_in_net_Q_excl_R_PP
    SRPC_M_net_in_net_Q_excl_c_M
    SRPC_M_net_in_net_Q_excl_c_P
    SRPC_M_net_in_net_R_excl_Q_MM
    SRPC_M_net_in_net_R_excl_Q_MP
    SRPC_M_net_in_net_R_excl_Q_PM
    SRPC_M_net_in_net_R_excl_Q_PP
    SRPC_M_net_in_net_R_excl_c_M
    SRPC_M_net_in_net_R_excl_c_P
    SRPC_M_net_in_net_c_excl_Q_M
    SRPC_M_net_in_net_c_excl_Q_P
    SRPC_M_net_in_net_c_excl_R_M
    SRPC_M_net_in_net_c_excl_R_P
    : LTS.


  Inductive sends_to_mon : MProc -> Name -> MProbe -> Prop :=
  | stm_find n p M : sends_to_mon (MSend (n, R) p M) n p
  | stm_seek n nc' p p' M :
    nc' <> (n, R) \/ p <> p' ->
    sends_to_mon M n p ->
    sends_to_mon (MSend nc' p' M) n p
  .

  #[export] Hint Constructors sends_to_mon : LTS.


  Definition sends_to N n0 n1 p := sends_to_mon (get_Mc N n0) n1 p.
  #[export] Hint Unfold sends_to : LTS_get.
  #[export] Hint Transparent sends_to : LTS.


  Lemma sends_to_mon_dec M n p : (sends_to_mon M n p \/ ~ sends_to_mon M n p).

  Proof.
    induction M; attac.
    destruct `(_ \/ _).
    - destruct (NameTag_eq_dec to (n, R)); subst.
      destruct (MProbe_eq_dec msg p); subst.
      left; constructor 1; attac.
      left; constructor 2; attac.
      left; constructor 2; attac.
    - destruct (NameTag_eq_dec to (n, R)); subst.
      destruct (MProbe_eq_dec msg p); subst.
      left; constructor 1; attac.
      + right; bs.
      + right; bs.
  Qed.


  Lemma sends_to_dec MN0 n0 n1 p : (sends_to MN0 n0 n1 p \/ ~ sends_to MN0 n0 n1 p).

  Proof.
    unfold sends_to.
    eauto using sends_to_mon_dec.
  Qed.

  #[export] Hint Resolve sends_to_mon_dec sends_to_dec : LTS.


  Lemma sends_to_mon_bs_inv state n p :
    sends_to_mon (MRecv state) n p <-> False.
  Proof. split; attac. Qed.

  Hint Resolve -> sends_to_mon_bs_inv : bs.
  Hint Rewrite -> sends_to_mon_bs_inv using eassumption : LTS LTS_concl.

  Lemma sends_to_mon_last_inv state nc n p0 p1 :
    sends_to_mon (MSend nc p1 (MRecv state)) n p0 <->
      nc = (n, R) /\ p1 = p0.
  Proof. destruct nc as [n' [|]]; split; attac; try (kill H); attac. Qed.

  Import Rad.

  Lemma sends_to_mon_many_inv state n ns t p0 p1 :
    sends_to_mon (MSend_all ns t p1 (MRecv state)) n p0 <->
      List.In n ns /\ t = R /\ p1 = p0.
  Proof.
    induction ns.
    1: split; attac.
    smash_eq n a.
    - split; intros.
      2: attac.
      consider (sends_to_mon _ _ _).
      1: attac.
      eapply IHns in H1.
      attac.
    - split; intros.
      2: attac.
      consider (sends_to_mon _ _ _).
      eapply IHns in H1.
      attac.
  Qed.

  #[export] Hint Rewrite -> sends_to_mon_last_inv sends_to_mon_many_inv using eassumption : LTS.


  Fixpoint no_Q_probe m :=
    match m with
    | MRecv _ => True
    | MSend (_, t) _ m' => t = R /\ no_Q_probe m'
    end.

  Definition no_Q_probe_in MN n := no_Q_probe (get_Mc MN n).


  Inductive KIS (MN : MNet) :=
    KIS_
      (* We are sane *)
      (H_sane_S : net_sane '' MN)
      (* `self` is correct *)
      (H_self_S : forall n0, _of self MN n0 = n0)
      (* We are using the algorithm *)
      (H_Rad_S : forall n0, handle (get_M MN n0) = Rad.Rad_handle)
      (* Monitor correctly judges the lock, unless there is a reply incoming it is about to see *)
      (H_lock_S : forall n0 n1, _of lock MN n0 = Some n1 -> net_lock_on '' MN n0 n1 \/ exists v, List.In (TrRecv (n1, R) v) (get_MQ MN n0))
      (* All members of the waiting list are locked on us *)
      (H_wait_S : forall n0 n1, List.In n0 (_of waitees MN n1) -> net_lock_on '' MN n0 n1)
      (* Monitors send probes only to those locked. *)
      (H_sendp_S : forall n0 n1 p, sends_to MN n1 n0 p -> net_lock_on '' MN n0 n1)
      (* All sent probes have their index no higher than the lock id of the initiator *)
      (H_index_send_S : forall n0 n1 p, sends_to MN n0 n1 p -> (index p <= _of lock_id MN (init p))%nat)
      (* All received probes have their index no higher than the lock id of the initiator *)
      (H_index_recvp_S : forall n0 n1 p, List.In (EvRecv (n1, R) p) (get_MQ MN n0) -> (index p <= _of lock_id MN (init p))%nat)
      (* If we are about to receive a hot probe of someone whose monitor considers locked, then we depend on them. *)
      (H_sendp_hot_S : forall n0 n1 n2, sends_to MN n1 n0 (hot_of MN n2) -> _of lock MN n2 <> None -> dep_on '' MN n0 n2)
      (* If we received a hot probe of someone whose monitor considers locked, then we depend on them. *)
      (H_recvp_hot_S : forall n0 n1 n2, List.In (hot_ev_of MN n2 n0) (get_MQ MN n1) -> _of lock MN n0 <> None -> dep_on '' MN n1 n0)
      (* No false alarms: if anyone screams, they are indeed deadlocked *)
      (H_alarm_S : forall n, _of alarm MN n = true -> dep_on '' MN n n)
      : KIS MN.


  Lemma KIS_sane [MN] : KIS MN -> net_sane '' MN.
  Proof. intros; consider (KIS _). Qed.

  Lemma KIS_self [MN] : KIS MN -> forall n0, _of self MN n0 = n0.
  Proof. intros; consider (KIS _). Qed.

  Lemma KIS_Rad [MN] : KIS MN -> forall n0, handle (get_M MN n0) = Rad.Rad_handle.
  Proof. intros; consider (KIS _). Qed.

  Lemma KIS_lock [MN] : KIS MN -> forall n0 n1, _of lock MN n0 = Some n1 -> net_lock_on '' MN n0 n1 \/ exists v, List.In (TrRecv (n1, R) v) (get_MQ MN n0).
  Proof. intros; consider (KIS _). Qed.

  Lemma KIS_wait [MN] : KIS MN -> forall n0 n1, List.In n0 (_of waitees MN n1) -> net_lock_on '' MN n0 n1.
  Proof. intros; consider (KIS _). Qed.

  Lemma KIS_sendp [MN] : KIS MN -> forall n0 n1 p, sends_to MN n1 n0 p -> net_lock_on '' MN n0 n1.
  Proof. intros; consider (KIS _). eauto. Qed.

  Lemma KIS_index_sendp [MN] : KIS MN -> forall n0 n1 p, sends_to MN n0 n1 p -> (index p <= _of lock_id MN (init p))%nat.
  Proof. intros; consider (KIS _). eauto. Qed.

  Lemma KIS_index_recvp [MN] : KIS MN -> forall n0 n1 p, List.In (EvRecv (n1, R) p) (get_MQ MN n0) -> (index p <= _of lock_id MN (init p))%nat.
  Proof. intros; consider (KIS _). eauto. Qed.

  Lemma KIS_sendp_hot [MN] : KIS MN -> forall n0 n1 n2, sends_to MN n1 n0 (hot_of MN n2) -> _of lock MN n2 <> None -> dep_on '' MN n0 n2.
  Proof. intros; consider (KIS _). eauto. Qed.

  Lemma KIS_recvp_hot [MN] : KIS MN -> forall n0 n1 n2, List.In (hot_ev_of MN n2 n0) (get_MQ MN n1) -> _of lock MN n0 <> None -> dep_on '' MN n1 n0.
  Proof. intros; consider (KIS _). eauto. Qed.

  Lemma KIS_alarm [MN] : KIS MN -> forall n, _of alarm MN n = true -> dep_on '' MN n n.
  Proof. intros; consider (KIS _). Qed.

  #[export] Hint Immediate
    KIS_sane
    KIS_self
    KIS_Rad
    KIS_lock
    KIS_wait
    KIS_sendp
    KIS_index_sendp
    KIS_index_recvp
    KIS_sendp_hot
    KIS_recvp_hot
    KIS_alarm : LTS.


  Lemma KIS_self_get [MN n0] [MQ h s S] [self'] :
    KIS MN ->
    NetMod.get n0 MN = mserv MQ {|handle:=h; state:=s|} S ->
    self (next_state s) = self' ->
    self' = n0.

  Proof. intros. assert (_of self MN n0 = n0) by eauto with LTS.
         ltac1:(autounfold with LTS_get in * ); hsimpl in * |-; auto.
  Qed.


  Lemma KIS_Rad_get [MN n0] [MQ h s S] :
    KIS MN ->
    NetMod.get n0 MN = mserv MQ {|handle:=h; state:=s|} S ->
    h = Rad_handle.

  Proof. intros. assert (handle (get_M MN n0) = Rad_handle) by eauto with LTS.
         ltac1:(autounfold with LTS_get in * ); hsimpl in * |-; auto.
  Qed.


  Lemma KIS_lock_get [MN n0 n1] [MQ h s S] :
    KIS MN ->
    NetMod.get n0 MN = mserv MQ {|handle:=h; state:=s|} S ->
    lock (next_state s) = Some n1 ->
    net_lock_on '' MN n0 n1 \/ exists v, List.In (TrRecv (n1, R) v) MQ.

  Proof. intros.
         assert (_of lock MN n0 = Some n1) by (ltac1:(autounfold with LTS_get in * ); attac).
         assert (net_lock_on '' MN n0 n1 \/ exists v, List.In (TrRecv (n1, R) v) (get_MQ MN n0)) by attac.
         ltac1:(autounfold with LTS_get in * ); hsimpl in * |-; auto.
  Qed.


  Lemma KIS_wait_get [MN n0 n1] [MQ h s S] :
    KIS MN ->
    NetMod.get n1 MN = mserv MQ {|handle:=h; state:=s|} S ->
    List.In n0 (waitees (next_state s)) ->
    net_lock_on '' MN n0 n1.

  Proof. intros.
         assert (List.In n0 (_of waitees MN n1)) by (ltac1:(autounfold with LTS_get in * ); attac).
         assert (net_lock_on '' MN n0 n1) by attac.
         ltac1:(autounfold with LTS_get in * ); hsimpl in * |-; auto.
  Qed.


  Lemma KIS_index_sendp_get [MN n0 n1 n2 p] [MQ0 MQ2 h0 h2 s0 s2 S0 S2] [index' lock_id'] :
    KIS MN ->
    NetMod.get n0 MN = mserv MQ0 {|handle:=h0; state:=s0|} S0 ->
    NetMod.get n2 MN = mserv MQ2 {|handle:=h2; state:=s2|} S2 ->
    sends_to_mon s0 n1 p ->
    index p = index' ->
    init p = n2 ->
    lock_id (next_state s2) = lock_id' ->
    index' <= lock_id'.

  Proof. intros.
         assert (sends_to MN n0 n1 p) by (ltac1:(autounfold with LTS_get in * ); attac).
         assert (index p <= _of lock_id MN (init p)) by attac.
         destruct p; simpl in *.
         ltac1:(autounfold with LTS_get in * ); attac.
         attac.
  Qed.


  Lemma KIS_index_recvp_get [MN n0 n1 n2 p] [MQ0 MQ2 h0 h2 s0 s2 S0 S2] [index' lock_id'] :
    KIS MN ->
    NetMod.get n0 MN = mserv MQ0 {|handle:=h0; state:=s0|} S0 ->
    NetMod.get n2 MN = mserv MQ2 {|handle:=h2; state:=s2|} S2 ->
    List.In (EvRecv (n1, R) p) MQ0 ->
    index p = index' ->
    init p = n2 ->
    lock_id (next_state s2) = lock_id' ->
    index' <= lock_id'.

  Proof. intros.
         assert (List.In (EvRecv (n1, R) p) (get_MQ MN n0)) by (ltac1:(autounfold with LTS_get in * ); attac).
         assert (index p <= _of lock_id MN (init p)) by attac.
         destruct p; simpl in *.
         ltac1:(autounfold with LTS_get in * ); attac.
         attac.
  Qed.


  Lemma KIS_sendp_hot_get [MN n0 n1 n2 p] [MQ1 MQ2 h1 h2 s1 s2 S1 S2] [lock_id'] :
    KIS MN ->
    NetMod.get n1 MN = mserv MQ1 {|handle:=h1; state:=s1|} S1 ->
    NetMod.get n2 MN = mserv MQ2 {|handle:=h2; state:=s2|} S2 ->
    sends_to_mon s1 n0 p ->
    index p = lock_id (next_state s2) ->
    init p = n2 ->
    lock_id (next_state s2) = lock_id' ->
    lock (next_state s2) <> None ->
    dep_on '' MN n0 n2.

  Proof. intros.
         destruct p.
         assert (sends_to MN n1 n0 (hot_of MN n2)) by (unfold hot_of in *; ltac1:(autounfold with LTS_get in * ); attac).
         assert (_of lock MN n2 <> None) by (ltac1:(autounfold with LTS_get in * ); attac).
         eauto with LTS.
  Qed.


  Lemma KIS_recvp_hot_get [MN n0 n1 n2 p] [MQ0 MQ2 h0 h2 s0 s2 S0 S2] [lock_id'] :
    KIS MN ->
    NetMod.get n0 MN = mserv MQ0 {|handle:=h0; state:=s0|} S0 ->
    NetMod.get n2 MN = mserv MQ2 {|handle:=h2; state:=s2|} S2 ->
    List.In (EvRecv (n1, R) p) MQ0 ->
    index p = lock_id (next_state s2) ->
    init p = n2 ->
    lock_id (next_state s2) = lock_id' ->
    lock (next_state s2) <> None ->
    dep_on '' MN n0 n2.

  Proof. intros.
         destruct p.
         assert (List.In (hot_ev_of MN n1 n2) (get_MQ MN n0)) by (unfold hot_ev_of, hot_of in *; ltac1:(autounfold with LTS_get in * ); attac).
         assert (_of lock MN n2 <> None) by (ltac1:(autounfold with LTS_get in * ); attac).
         eauto with LTS.
  Qed.


  Lemma KIS_alarm_get [MN n0] [MQ h s S] :
    KIS MN ->
    NetMod.get n0 MN = mserv MQ {|handle:=h; state:=s|} S ->
    alarm (next_state s) = true ->
    dep_on '' MN n0 n0.

  Proof. intros.
         enough (_of alarm MN n0 = true) by attac.
         ltac1:(autounfold with LTS_get in * ); attac.
  Qed.

  Hint Resolve
    KIS_self_get
    KIS_Rad_get
    KIS_lock_get
    KIS_wait_get
    KIS_index_sendp_get
    KIS_index_recvp_get
    KIS_sendp_hot_get
    KIS_recvp_hot_get
    KIS_alarm : LTS.


  Lemma KIS_invariant_sane [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    net_sane '' MN1.

  Proof.
    intros.
    assert (net_sane '' MN0) by eauto with LTS.
    destruct (MNAct_to_PNAct a) eqn:?.
    - eauto using net_deinstr_act_do with LTS.
    - now replace ('' MN1) with ('' MN0) by eauto using net_deinstr_act_skip with LTS.
  Qed.

  Hint Immediate KIS_invariant_sane : LTS.


  Lemma KIS_invariant_self [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n0, _of self MN1 n0 = n0.

  Proof.
    intros.
    assert (_of self MN0 n0 = n0) by attac.
    enough (_of self MN0 n0 = _of self MN1 n0) by attac.
    enough (handle (get_M MN0 n0) = Rad.Rad_handle) by eauto using net_preserve_self with LTS.
    attac.
  Qed.

  Hint Immediate KIS_invariant_self : LTS.


  Lemma KIS_invariant_Rad [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n0, handle (get_M MN1 n0) = Rad.Rad_handle.

  Proof.
    intros.
    enough (handle (get_M MN0 n0) = handle (get_M MN1 n0)) by attac.
    eauto using net_preserve_handle.
  Qed.

  Hint Immediate KIS_invariant_Rad : LTS.

  Ltac2 Notation "destruct_mna" a(constr) :=
      destruct $a as [? [[[? [|]]|[? [|]]|]|[[? ?]|[? ?]|]|[[? ?]|[? ?]|]] | ? ? [|] [?|?]]; doubt.

  Lemma M_lock_set [MN0 MN1 a n0 n1] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    _of lock MN0 n0 = None ->
    _of lock MN1 n0 = Some n1 ->
    exists v, a = NComm n0 n1 Q (MValP v).

  Proof.
    intros.
    destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; doubt.

    all:
      Control.enter (fun _ => consider (h = Rad.Rad_handle) by eauto with LTS);
      destruct s; hsimpl in *; simpl in *; doubt.

    - destruct n2 as [? [|]]; simpl in *; doubt.
    - eattac.
    - eattac.
  Qed.


  Lemma M_lock_unset [MN0 MN1 a n0 n1] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    _of lock MN0 n0 = Some n1 ->
    _of lock MN1 n0 = None ->
    exists v, a = NTau n0 (MActP (Recv (n1, R) v)).

  Proof.
    intros.
     destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; doubt.

    all:
      Control.enter (fun _ => consider (h = Rad.Rad_handle) by (eauto with LTS));
      destruct s; hsimpl in *; simpl in *; doubt.

    - smash_eq n2 n1; eattac.
    - destruct n2 as [? [|]]; eattac.
      smash_eq n n1; eattac.
      destruct (NAME.eqb (init msg) &self); attac.
      destruct (&lock_id =? index msg); attac.
  Qed.


  (* Lemma SRPC_pq_in_net_in_R_no_out [srpc I P O s v] : *)
  (*   SRPC_pq_in_net srpc (serv I P O) -> *)
  (*   List.In (s, R, v) I -> *)
  (*   O = []. *)

  (* Proof. *)
  (*   intros. *)
  (*   enough (forall n t v, ~ List.In (n, t, v) &O) as Hx. *)
  (*   { *)
  (*     clear - Hx. *)
  (*     induction O; intros; auto. *)
  (*     destruct a as [[n t] v]. *)
  (*     bs (List.In (n, &t, v) ((n, &t, v)::&O)). *)
  (*   } *)
  (*   intros n t v'. *)
  (*   destruct t. *)
  (*   - intros ?. *)
  (*     consider (n = s). *)
  (*     { *)
  (*       assert (exists c, srpc = Lock c s) by eauto with LTS. *)
  (*       assert (exists c, srpc = Lock c n) by eauto with LTS. *)
  (*       attac. *)
  (*     } *)
  (*     bs. *)
  (*   - consider (exists c, srpc = Lock c s) by eauto with LTS. *)
  (*     assert (&O = [] \/ &O <> []) as [|] by (destruct O; attac); subst; auto. *)
  (*     consider (exists v, List.In (s, Q, v) &O) by eauto with LTS. *)
  (*     bs. *)
  (* Qed. *)


  Lemma M_lock_no_send [MN0 MN1 n0 n1 m0 m1 t v] :
    KIS MN0 ->
    _of lock MN0 n0 = Some n1 ->
    (MN0 =(NComm m0 m1 t (MValP v))=> MN1) ->
    n0 <> m0.

  Proof.
    intros.
    assert (net_lock_on '' MN0 n0 n1 \/ exists v, List.In (TrRecv (n1, R) v) (get_MQ MN0 n0)) as [|]
        by eauto with LTS.
    1: eauto using locked_M_no_send with LTS.

    intros ?; subst.
    hsimpl in *.
    unfold get_MQ in *.

    destruct (NetMod.get m0 '' MN0) as [I0 P0 O0] eqn:?.
    assert (List.In (n1, R, v0) I0).
    {
      destruct (NetMod.get m0 MN0) as [MQ0 M0 [I0' P0' O0']] eqn:?.
      unfold net_deinstr, deinstr in *. hsimpl in *.
      attac.
    }

    consider (O0 = []).
    {
      consider (net_sane '' MN0) by eauto with LTS.
      specialize (H_Sane_SRPC m0) as [srpc Hsrpc].
      hrewrite NetMod.get in *.
      replace O0 with (serv_o (serv I0 P0 O0)) by auto.
      eauto using SRPC_sane_R_in_out_nil with LTS.
    }

    consider (_ =(_)=> _).
    compat_hsimpl in *.
    unfold net_deinstr, deinstr in *.
    hsimpl in *.
    destruct P1.
    bs.
  Qed.


  Lemma M_lock_no_reset [MN0 MN1 a n0 n1 n1'] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    _of lock MN0 n0 = Some n1 ->
    _of lock MN1 n0 = Some n1' ->
    n1' = n1.

  Proof.
    intros.

    assert (forall n t v, a <> NComm n0 n t (MValP v)).
    {
      iattac; bs (n0 <> n0) by eauto using M_lock_no_send.
    }

    destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; doubt;
       Control.enter (fun _ => consider (h = Rad.Rad_handle) by eauto with LTS);
       destruct s; hsimpl in *; simpl in *; doubt.

    - blast_cases; iattac.
    - destruct n2 as [? [|]]; eattac.
      smash_eq n n1; eattac.
      destruct (NAME.eqb (init msg) &self); attac.
      destruct (&lock_id =? index msg); attac.
    - bs (NComm n1' n1' Q # v <> NComm n1' n1' Q # v).
    - bs (NComm n0 n1' Q # v <> NComm n0 n1' Q # v).
  Qed.


  Lemma M_lock_set_act [MN0 MN1 n0 n1 v] :
    KIS MN0 ->
    (MN0 =(NComm n0 n1 Q (MValP v))=> MN1) ->
    _of lock MN0 n0 = None /\ _of lock MN1 n0 = Some n1.

  Proof.
    intros.
    consider (~ net_lock_on '' MN0 n0 n1 /\ net_lock_on '' MN1 n0 n1)
      by (eauto using SRPC_M_net_query_new_lock with LTS).

    split.
    - enough (forall n, _of lock MN0 n0 <> Some n) by (destruct (_of lock MN0 n0); attac). intros ? ?.
      apply `(~ net_lock_on '' MN0 _ _).
      assert (net_lock_on '' MN0 n0 n \/ exists v, List.In (TrRecv (n, R) v) (get_MQ MN0 n0)) as [|]
          by eauto with LTS.
      + consider (n = n1) by eauto using SRPC_M_net_no_immediate_relock with LTS.
      + hsimpl in *.

        destruct (NetMod.get n0 '' MN0) as [I0 P0 O0] eqn:?.
        assert (List.In (n, R, v0) I0).
        {
          unfold get_MQ in *.
          destruct (NetMod.get n0 MN0) as [MQ0 M0 [I0' P0' O0']] eqn:?.
          unfold net_deinstr, deinstr in *. hsimpl in *.
          attac.
        }

        consider (O0 = []).
        {
          consider (net_sane '' MN0) by eauto with LTS.
          specialize (H_Sane_SRPC n0) as [srpc Hsrpc].
          rewrite `(NetMod.get n0 _ = _) in *.
          replace (O0) with (serv_o (serv I0 P0 O0)) by auto. (* TODO seek and destroy this bs *)
          eauto using SRPC_sane_R_in_out_nil with LTS.
        }

        consider (_ =(_)=> _).
        compat_hsimpl in *.
        unfold net_deinstr, deinstr in *.
        hsimpl in *.
        destruct P1.
        bs.
    - consider (_ =(_)=> _).
      compat_hsimpl in *.
      unfold net_deinstr, deinstr in *.
      hsimpl in *.
      consider (h = Rad.Rad_handle) by eauto with LTS.
      destruct s.
      simpl in *.
      smash_eq n0 n1; hsimpl in *; attac.
  Qed.


  Lemma M_R_in_no_send [MN0 n0 n1 v MQ M I P O] :
    KIS MN0 ->
    NetMod.get n0 MN0 = mserv MQ M (serv I P O) ->
    List.In (n1, R, v) (I ++ MQ_r MQ)  ->
    (MQ_s MQ ++ O) = [].

  Proof.
    intros.

    destruct (NetMod.get n0 '' MN0) as [I0 P0 O0] eqn:?.
    assert (List.In (n1, R, v) I0).
    {
      unfold get_MQ in *.
      unfold net_deinstr, deinstr in *. hsimpl in *.
      attac.
    }

    consider (O0 = []).
    {
      consider (net_sane '' MN0) by eauto with LTS.
      specialize (H_Sane_SRPC n0) as [srpc Hsrpc].
      rewrite `(NetMod.get n0 _ = _) in *.
      replace (O0) with (serv_o (serv I0 P0 O0)) by auto. (* TODO seek and destroy this bs *)
      eauto using SRPC_sane_R_in_out_nil with LTS.
    }

    unfold net_deinstr, deinstr in *.
    attac.
  Qed.


  Lemma M_R_in_no_send_MM [MN0 n0 n1 v] :
    KIS MN0 ->
    List.In (TrRecv (n1, R) v) (get_MQ MN0 n0)  ->
    MQ_s (get_MQ MN0 n0) = [].

  Proof.
    intros.
    destruct (NetMod.get n0 MN0) as [MQ0 M0 [I0 P0 O0]] eqn:?.
    unfold get_MQ in *; hsimpl in *.
    assert (List.In (n1, R, v) (I0 ++ MQ_r MQ0)) by attac.
    assert ((MQ_s MQ0 ++ O0) = []) by eauto using M_R_in_no_send with LTS.
    apply app_eq_nil in H2.
    attac.
  Qed.
  Lemma M_R_in_no_send_MP [MN0 n0 n1 v MQ M I P O] :
    KIS MN0 ->
    NetMod.get n0 MN0 = mserv MQ M (serv I P O) ->
    List.In (n1, R, v) (I ++ MQ_r MQ)  ->
    O = [].
  Proof.
    intros.
    destruct (NetMod.get n0 MN0) as [MQ0 M0 [I0 P0 O0]] eqn:?.
    assert (List.In (n1, R, v) (I0 ++ MQ_r MQ0)) by attac.
    assert ((MQ_s MQ0 ++ O0) = []) by eauto using M_R_in_no_send with LTS.
    apply app_eq_nil in H3.
    attac.
  Qed.
  Lemma M_R_in_no_send_PM [MN0 n0 n1 v MQ M I P O] :
    KIS MN0 ->
    NetMod.get n0 MN0 = mserv MQ M (serv I P O) ->
    List.In (n1, R, v) (I ++ MQ_r MQ)  ->
    MQ_s MQ = [].
  Proof.
    intros.
    destruct (NetMod.get n0 MN0) as [MQ0 M0 [I0 P0 O0]] eqn:?.
    assert (List.In (n1, R, v) (I0 ++ MQ_r MQ0)) by attac.
    assert ((MQ_s MQ0 ++ O0) = []) by eauto using M_R_in_no_send with LTS.
    apply app_eq_nil in H3.
    attac.
  Qed.
  Lemma M_R_in_no_send_PP [MN0 n0 n1 v MQ M I P O] :
    KIS MN0 ->
    NetMod.get n0 MN0 = mserv MQ M (serv I P O) ->
    List.In (n1, R, v) (I ++ MQ_r MQ)  ->
    O = [].
  Proof.
    intros.
    destruct (NetMod.get n0 MN0) as [MQ0 M0 [I0 P0 O0]] eqn:?.
    assert (List.In (n1, R, v) (I0 ++ MQ_r MQ0)) by attac.
    assert ((MQ_s MQ0 ++ O0) = []) by eauto using M_R_in_no_send with LTS.
    apply app_eq_nil in H3.
    attac.
  Qed.

  #[export] Hint Resolve M_R_in_no_send_MM M_R_in_no_send_MP M_R_in_no_send_PM M_R_in_no_send_PP : LTS.


  Lemma M_wait_add [MN0 MN1 a n0 n1] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    ~ List.In n1 (_of waitees MN0 n0) ->
    List.In n1 (_of waitees MN1 n0) ->
    exists v, a = NTau n0 (MActP (Recv (n1, Q) v)).

  Proof.
    intros.

    destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; doubt.

    all:
      Control.enter (fun _ => consider (h = Rad.Rad_handle) by eauto with LTS);
      destruct s; hsimpl in *; simpl in *; doubt.

    - assert (List.In n1 (n2::&waitees)) by (blast_cases; attac).
      attac.
    - assert (List.In n1 &waitees) by (blast_cases; attac).
      bs.
    - assert (List.In n1 &waitees) by (blast_cases; attac).
      bs.
    - bs (List.In n1 &waitees /\ n1 <> n0) by eauto using in_remove.
    - bs (List.In n1 &waitees /\ n1 <> n2) by eauto using in_remove.
  Qed.


  Lemma M_wait_remove [MN0 MN1 a n0 n1] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    List.In n1 (_of waitees MN0 n0) ->
    ~ List.In n1 (_of waitees MN1 n0) ->
    exists v, a = NComm n0 n1 R v.

  Proof.
    intros.

    destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; doubt.

    all:
      Control.enter (fun _ => consider (h = Rad.Rad_handle) by eauto with LTS);
      destruct s; hsimpl in *; simpl in *; doubt.

    all: blast_cases; eattac.
    - smash_eq n1 n0; attac.
      bs (List.In n1 (List.remove NAME.eq_dec n0 &waitees)) by eauto using in_in_remove.

    - smash_eq n1 n2; attac.
      bs (List.In n1 (List.remove NAME.eq_dec n2 &waitees)) by eauto using in_in_remove.
  Qed.


  Lemma M_lock_id_update [MN0 MN1 a n0] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    _of lock_id MN0 n0 <> _of lock_id MN1 n0 ->
    exists n1 v, a = NComm n0 n1 Q (MValP v).

  Proof.
    intros.

    destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; doubt.

    all:
      Control.enter (fun _ => consider (h = Rad.Rad_handle) by eauto with LTS);
      destruct s; hsimpl in *; simpl in *; doubt.

    all: blast_cases; eattac.
  Qed.


  Lemma M_lock_id_incr [MN0 MN1 a n0] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    _of lock_id MN1 n0 = _of lock_id MN0 n0 \/ _of lock_id MN1 n0 = S (_of lock_id MN0 n0).

  Proof.
    intros.

    destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; doubt.

    all: eattac.
    all:
      Control.enter (fun _ => consider (h = Rad.Rad_handle) by eauto with LTS);
      destruct s; hsimpl in *; simpl in *; doubt.

    all: blast_cases; eattac.
  Qed.


  Lemma M_lock_id_update_act [MN0 MN1 n0 n1 v] :
    KIS MN0 ->
    (MN0 =(NComm n0 n1 Q (MValP v))=> MN1) ->
    _of lock_id MN1 n0 = S (_of lock_id MN0 n0).

  Proof.
    intros.
    consider (_ =(_)=> _).
    compat_hsimpl in *.
    ltac1:(autounfold with LTS_get in * ).
    consider (h = Rad.Rad_handle) by eauto with LTS.
    hsimpl_net; attac.
  Qed.


  Lemma M_alarm_set [MN0 MN1 a n0] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    _of alarm MN0 n0 = false ->
    _of alarm MN1 n0 = true ->
    a = NTau n0 (MActM Tau) /\
      exists n1, List.In (EvRecv (n1, R) {|init:=n0; index:=_of lock_id MN0 n0|}) (get_MQ MN0 n0).

  Proof.
    intros.

    assert (_of self MN1 n0 = n0) by eauto using KIS_invariant_self.

    destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; doubt.

    all: try (destruct msg).

    all:
      Control.enter (fun _ => consider (h = Rad.Rad_handle) by eauto with LTS);
      destruct s; hsimpl in *; simpl in *; doubt.

    all: blast_cases; eattac.

    consider (&lock_id = &index) by (apply PeanoNat.Nat.eqb_eq; auto).
    eauto with LTS.
  Qed.


  Lemma KIS_invariant_lock [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n0 n1, _of lock MN1 n0 = Some n1 -> net_lock_on '' MN1  n0 n1 \/ exists v, List.In (TrRecv (n1, R) v) (get_MQ MN1 n0).

  Proof.
    intros.

    destruct (net_sane_lock_dec '' MN1 n0 n1); eauto using KIS_invariant_sane with LTS.
    right.

    destruct (net_sane_lock_dec '' MN0 n0 n1); eauto with LTS.
    - consider (exists v, a = NComm n1 n0 R (MValP v))
        by eauto using SRPC_M_net_unlock_reply with LTS.
      unfold get_MQ in *.
      consider (_ =(_)=> _).
      eattac.
    - assert (net_sane '' MN0) by eauto with LTS.
      assert (net_sane '' MN1) by eauto with LTS.

      assert ((exists v, List.In (TrRecv (n1, R) v) (get_MQ MN1 n0))
                              \/ forall v, ~ List.In (TrRecv (n1, R) v) (get_MQ MN1 n0)
             ) as [|]; auto.
      {
        generalize (get_MQ MN1 n0) as Q0. clear.
        intros.
        induction Q0; attac.
        destruct `(_ \/ _); attac.
        destruct a; attac.
        destruct (NameTag_eq_dec n (n1, R)); attac.
      }
      exfalso.

      destruct (_of lock MN0 n0) as [n1'| ] eqn:?.
      + consider (n1' = n1) by (symmetry; eauto using M_lock_no_reset).
        assert (net_lock_on '' MN0 n0 n1 \/ exists v, List.In (TrRecv (n1, R) v) (get_MQ MN0 n0)) by eauto with LTS.
        hsimpl in *.
        unfold get_MQ in *.

        destruct (NetMod.get n0 MN0) as [MQ0 M0 [I0 P0 O0]] eqn:?.
        destruct (NetMod.get n0 MN1) as [MQ1 M1 [I1 P1 O1]] eqn:?.

        destruct_mna a; hsimpl in *.

        all: smash_eq n n0; hsimpl in *.

        par: doubt.

        all: hsimpl in *.
        * bs (~ In (TrRecv (n1, R) v) (MQ0 ++ [TrSend _ _])) by eauto.
        * bs (~ In (TrRecv (n1, R) v) (MQ0 ++ [TrSend _ _])) by eauto.
        * bs.
        * destruct `(_ \/ _); hsimpl in *; doubt.
          consider (h = Rad.Rad_handle) by eauto with LTS.
          ltac1:(autounfold with LTS_get in * ).
          hsimpl in *.
          simpl in H1.
          destruct s.
          hsimpl in *; bs.
        * bs.
        * assert (~ In (TrRecv (n1, R) v) MQ1) by eauto.
          consider (MN0 =(_)=> _); hsimpl in *.
          hsimpl_net; bs.
        * assert (~ In (TrRecv (n1, R) v) MQ1) by eauto.
          consider (MN0 =(_)=> _); hsimpl in *.
          hsimpl_net; bs.
        * assert (~ In (TrRecv (n1, R) v) MQ1) by eauto.
          consider (MN0 =(_)=> _); hsimpl in *.
          hsimpl_net; bs.
        * assert (~ In (TrRecv (n1, R) v) MQ1) by eauto.
          consider (MN0 =(_)=> _); hsimpl in *.
          hsimpl_net; bs.
        * assert (~ In (TrRecv (n1, R) v) MQ1) by eauto.
          consider (MN0 =(_)=> _); hsimpl in *.
          hsimpl_net; bs.
        * assert (~ In (TrRecv (n1, R) v) MQ1) by eauto.
          consider (MN0 =(_)=> _); hsimpl in *.
          hsimpl_net; bs.
        * assert (~ In (TrRecv (n1, R) v) MQ1) by eauto.
          consider (MN0 =(_)=> _); hsimpl in *.
          hsimpl_net; bs.
        * assert (~ In (TrRecv (n1, R) v) MQ1) by eauto.
          consider (MN0 =(_)=> _); hsimpl in *.
          hsimpl_net; bs.

      + enough (exists v, a = NComm n0 n1 Q (MValP v))
          by (hsimpl in *; consider (~ net_lock_on '' MN0 n0 n1 /\ net_lock_on '' MN1 n0 n1) by eauto using SRPC_M_net_query_new_lock).

        eauto using M_lock_set.
  Qed.


  Lemma KIS_invariant_wait [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n0 n1, List.In n0 (_of waitees MN1 n1) -> net_lock_on '' MN1 n0 n1.

  Proof.
    intros.
    destruct (net_sane_lock_dec '' MN1 n0 n1); eauto with LTS.
    exfalso.

    destruct (in_dec NAME.eq_dec n0 (_of waitees MN0 n1)).
    - assert (net_lock_on '' MN0 n0 n1) by eauto with LTS.
      consider (exists v, a = NComm n1 n0 R (MValP v)) by eauto using SRPC_M_net_unlock_reply with LTS.

      consider (_ =(_)=> _).
      compat_hsimpl in *.
      ltac1:(autounfold with LTS_get in * ).
      consider (h = Rad.Rad_handle) by eauto with LTS.
      destruct s.
      hsimpl_net.
      + bs (~ List.In n0 (List.remove NAME.eq_dec n0 &waitees)) by eauto using remove_In.
      + bs (~ List.In n0 (List.remove NAME.eq_dec n0 &waitees)) by eauto using remove_In.

    - rename n into Hn.
      assert (exists v, a = NTau n1 (MActP (Recv (n0, Q) v))) by eauto using M_wait_add with LTS.

      enough (net_lock_on '' MN0 n0 n1).
      {
        consider (exists v, a = NComm n1 n0 R (MValP v)) by eauto using SRPC_M_net_unlock_reply with LTS.
        bs.
      }

      destruct (NetMod.get n1 '' MN0) as [I0' P0' O0'] eqn:?.
      destruct (NetMod.get n1 MN0) as [MQ0 M0 [I0 P0 O0]] eqn:?.

      enough (pq_client n0 (NetMod.get n1 '' MN0)) by eauto with LTS.
      enough (exists v, List.In (n0, Q, v) I0') by iattac.
      enough (exists v, List.In (TrRecv (n0, Q) v) MQ0)
        by (hsimpl in *; exists v0; unfold net_deinstr, deinstr in *; ieattac).
      eattac.
  Qed.


  Lemma M_sends_to_send_unset [MN0 MN1 a n0 n1 p] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    sends_to MN0 n0 n1 p ->
    ~ sends_to MN1 n0 n1 p ->
    a = NComm n0 n1 R ^ p.

  Proof.
    intros.

    destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; hsimpl in *; doubt.
    - consider (sends_to_mon _ _ _).
    - consider (sends_to_mon _ _ _).
  Qed.


  Lemma M_sends_to_send_set [MN0 MN1 a n0 n1 p] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    ~ sends_to MN0 n0 n1 p ->
    sends_to MN1 n0 n1 p ->
    (exists v, a = NTau n0 (MActP (Recv (n1, Q) v))) \/ a = NTau n0 (MActM Tau).

  Proof.
    intros.

    destruct (NetMod.get n0 MN0) as [MQ0 [h s0] S0] eqn:?.
    consider (h = Rad.Rad_handle) by eauto with LTS.
    destruct (NetMod.get n0 MN1) as [MQ1 [h s1] S1] eqn:?.
    assert (handle (get_M MN1 n0) = Rad_handle) by eauto with LTS.

    destruct_mna a; hsimpl in *.

    all: ltac1:(autounfold with LTS_get in * ); hsimpl_net; blast_cases; eattac.

    - consider (MN0 =(_)=> _); hsimpl in *.
      hsimpl_net; doubt.
    - consider (MN0 =(_)=> _); hsimpl in *.
      hsimpl_net; doubt.
    - consider (MN0 =(_)=> _); hsimpl in *.
      exfalso.
      hsimpl_net; hsimpl in *; doubt.
      + apply `(~ sends_to_mon _ _ _).
        constructor; eattac.
        destruct (MProbe_eq_dec m p); subst; constructor; attac.
        smash_eq n0 n1.
        attac.
      + apply `(~ sends_to_mon _ _ _).
        constructor; eattac.
        destruct (MProbe_eq_dec m p); subst; constructor; attac.
        smash_eq n2 n1.
        attac.
    - consider (MN0 =(_)=> _); hsimpl in *.
      hsimpl_net; hsimpl in *; doubt.
  Qed.


  Lemma KIS_invariant_sendp [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n0 n1 p, sends_to MN1 n1 n0 p -> net_lock_on '' MN1 n0 n1.

  Proof.
    intros.

    destruct (NetMod.get n1 MN0) as [MQ0 [h0 s0] S0] eqn:?.
    consider (h0 = Rad.Rad_handle) by eauto with LTS.

    destruct (NetMod.get n1 MN1) as [MQ1 [h1 s1] S1] eqn:?.

    destruct (net_sane_lock_dec '' MN1 n0 n1); eauto with LTS.

    destruct (sends_to_dec MN0 n1 n0 p).
    - assert (net_lock_on '' MN0 n0 n1) by eauto with LTS.

      consider (exists v, a = NComm n1 n0 R (MValP v)) by eauto using SRPC_M_net_unlock_reply with LTS.

      consider (_ =(_)=> _); compat_hsimpl in *.
      ltac1:(autounfold with LTS_get in * ); attac.

    - assert ((exists v, a = NTau n1 (MActP (Recv (n0, Q) v))) \/ a = NTau n1 (MActM Tau)) as [|]
          by eauto using M_sends_to_send_set with LTS.
      + hsimpl in *.
        enough (net_lock_on '' MN0 n0 n1).
        {
          consider (exists v', NTau n1 (MActP (Recv (n0, Q) v)) = NComm n1 n0 R (MValP v')) by (eapply SRPC_M_net_unlock_reply; attac; constructor; attac).
          bs.
        }

        enough (pq_client n0 (NetMod.get n1 '' MN0)) by eauto with LTS.
          enough (List.In (TrRecv (n0, Q) v) (get_MQ MN0 n1))
          by (ltac1:(autounfold with LTS_get in * ); unfold net_deinstr, deinstr in *; attac).
        ltac1:(autounfold with LTS_get in * ); hsimpl in *.
        blast_cases; attac.
      + enough (List.In n0 (_of waitees MN1 n1)) by eauto using KIS_invariant_wait.
        consider (MN0 =(_)=> _).
        hsimpl in *.

        blast_cases; attac.

        par: unfold sends_to in *; ltac1:(autounfold with LTS_get in * ); hsimpl in *; bs.
  Qed.


  Lemma KIS_invariant_index_sendp [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n0 n1 p, sends_to MN1 n0 n1 p -> (index p <= _of lock_id MN1 (init p))%nat.

  Proof.
    intros.

    destruct (NetMod.get n0 MN0) as [MQ0 [h s0] S0] eqn:?.
    consider (h = Rad.Rad_handle) by eauto with LTS.
    destruct (NetMod.get n0 MN1) as [MQ1 [h s1] S1] eqn:?.
    assert (handle (get_M MN1 n0) = Rad_handle) by eauto with LTS.

    destruct (sends_to_dec MN0 n0 n1 p).
    - assert ((index p <= _of lock_id MN0 (init p))%nat) by eauto with LTS.
      unfold sends_to in *.

      destruct p.

      destruct (NetMod.get &init MN0) as [MQp0 [h' sp0] Sp0] eqn:?.
      consider (h' = Rad.Rad_handle) by eauto with LTS.
      destruct (NetMod.get &init MN1) as [MQp1 [h' sp1] Sp1] eqn:?.
      assert (handle (get_M MN1 n0) = Rad_handle) by eauto with LTS.

      destruct_mna a;
        consider (MN0 =(_)=> _);
        ltac1:(autounfold with LTS_get in * );
        hsimpl in *; hsimpl_net; hsimpl in *; doubt.

      par: simpl in *; blast_cases; ieattac.

    - destruct (NetMod.get (init p) MN0) as [MQp0 [h'' sp0] Sp0] eqn:?.
      consider (h'' = Rad.Rad_handle) by eauto with LTS.
      destruct (NetMod.get (init p) MN1) as [MQp1 [h'' sp1] Sp1] eqn:?.
      assert (handle (get_M MN1 (init p)) = Rad_handle) by eauto with LTS.

      assert ((exists v, a = NTau n0 (MActP (Recv (n1, Q) v))) \/ a = NTau n0 (MActM Tau)) as [|]
          by eauto using M_sends_to_send_set with LTS.
      + hsimpl in *.
        ltac1:(autounfold with LTS_get in * ).
        hsimpl_net; hsimpl in *.
        all: blast_cases; attac.

        consider (&self = n0) by eauto with LTS.
        bs.

      + hsimpl in *.

        unfold sends_to in *; ltac1:(autounfold with LTS_get in * ); hsimpl in *; doubt.
        all: blast_cases; attac.


        hsimpl_net; hsimpl in *.
        * enough (index p <= _of lock_id MN0 (init p))
            by (ltac1:(autounfold with LTS_get in * ); hsimpl in *; eattac).
          enough (List.In (EvRecv (n1, R) p) (get_MQ MN0 (init p))) by eauto with LTS.

          absurd (&self = init p); auto.
          enough (_of self MN0 (init p) = (init p)) by (ltac1:(autounfold with LTS_get in * ); attac).
          eauto with LTS.
        * enough (index p <= _of lock_id MN0 (init p))
            by (ltac1:(autounfold with LTS_get in * ); hsimpl in *; eattac).
          eenough (List.In (EvRecv (_, R) p) (get_MQ MN0 n0)) by eauto with LTS.

          enough (&self = n0) by (ltac1:(autounfold with LTS_get in * ); attac).

          enough (_of self MN0 n0 = n0) by (ltac1:(autounfold with LTS_get in * ); attac).
          eauto with LTS.
  Qed.


  Lemma M_recv_ev_act [MN0 MN1 a n0 n1 t p] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    ~ List.In (EvRecv (n1, t) p) (get_MQ MN0 n0) ->
    List.In (EvRecv (n1, t) p) (get_MQ MN1 n0) ->
    a = NComm n1 n0 t ^ p.

  Proof.
    intros.

    destruct (NetMod.get n0 MN0) as [MQ0 [h s0] S0] eqn:?.
    consider (h = Rad.Rad_handle) by eauto with LTS.

    destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; hsimpl in *; doubt.

    all: auto.
  Qed.


  Lemma KIS_invariant_index_recvp [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n0 n1 p, List.In (EvRecv (n1, R) p) (get_MQ MN1 n0) ->
                                      (index p <= _of lock_id MN1 (init p))%nat.

  Proof.
    intros.

    assert (handle (get_M MN1 (init p)) = Rad_handle) by eauto with LTS.

    assert (In (EvRecv (n1, R) p) (get_MQ MN0 n0) \/ ~ In (EvRecv (n1, R) p) (get_MQ MN0 n0)) as [|].
    - induction (get_MQ MN0 n0); attac.
      destruct `(_ \/ _); attac.
      destruct a0; attac.
      destruct n.
      destruct (MProbe_eq_dec p m); attac.
      destruct t; attac.
      smash_eq n n1; attac.
    - assert (index p <= _of lock_id MN0 (init p)) by eauto with LTS.
      destruct (PeanoNat.Nat.eq_dec (_of lock_id MN1 (init p)) (_of lock_id MN0 (init p))).
      1: attac.

      consider (exists n1' v, a = NComm (init p) n1' Q (MValP v)) by eauto using M_lock_id_update.

      consider (_of lock MN0 (init p) = None /\ _of lock MN1 (init p) = Some n1') by eauto using M_lock_set_act.
      consider (_ =(_)=> _); compat_hsimpl in *.
      ltac1:(autounfold with LTS_get in * ); hsimpl in *.
      hsimpl_net; hsimpl in *; doubt.
      all: blast_cases; attac.
    - assert (a = NComm n1 n0 R ^ p) by eauto using  M_recv_ev_act.
      destruct (PeanoNat.Nat.eq_dec (_of lock_id MN1 (init p)) (_of lock_id MN0 (init p))).
      2: consider (exists n1' v, a = NComm (init p) n1' Q (MValP v)) by (eauto using M_lock_id_update; hsimpl in * ); bs.
      enough (sends_to MN0 n1 n0 p) by (rewrite `(_of lock_id MN1 _ = _) in *; eauto with LTS).

      subst.
      consider (_ =(_)=> _); compat_hsimpl in *.
      unfold sends_to in *; ltac1:(autounfold with LTS_get in * ); hsimpl in *.
      attac.
  Qed.


  Lemma dep_dec_after : forall N0 N1 a n0 n1,
      net_sane N0 ->
      dep_on N0 n0 n1 ->
      (N0 =(a)=> N1) ->
      dep_on N1 n0 n1 \/ ~ dep_on N1 n0 n1.

  Proof.
    intros.
    apply dep_lock_chain in H0 as [L [? ?]].
    generalize dependent n0.
    induction L; intros; hsimpl in *.
    - destruct (net_sane_lock_dec N1 n0 n1); eauto with LTS.
      right; intros ?.
      consider (dep_on N1 n0 _).
      consider (n1 = n2) by eauto using SRPC_net_no_relock with LTS.
    - specialize (IHL ltac:(auto) a0 ltac:(auto)) as [|].
      + destruct (net_sane_lock_dec N1 n0 a0); eauto with LTS.
        right; intros ?.
        consider (dep_on N1 _ _).
        * consider (a0 = n1) by eauto using SRPC_net_no_relock with LTS.
        * consider (a0 = n2) by eauto using SRPC_net_no_relock with LTS.
      + right; intros ?.
        consider (dep_on N1 n0 n1).
        * consider (a0 = n1) by eauto using SRPC_net_no_relock with LTS.
        * consider (a0 = n2) by eauto using SRPC_net_no_relock with LTS.
  Qed.

  Lemma dep_dec_after_M : forall MN0 MN1 ma n0 n1,
      net_sane '' MN0 ->
      dep_on '' MN0 n0 n1 ->
      (MN0 =(ma)=> MN1) ->
      dep_on '' MN1 n0 n1 \/ ~ dep_on '' MN1 n0 n1.

  Proof.
    intros.
    destruct (MNAct_to_PNAct ma) as [a|] eqn:?.
    - assert ('' MN0 =(a)=> '' MN1) by eauto using net_deinstr_act_do with LTS.
      now eauto using dep_dec_after.
    - replace ('' MN1) with ('' MN0) by eauto using net_deinstr_act_skip with LTS.
      now left.
  Qed.


  Lemma KIS_invariant_recvp_hot [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n0 n1 n2, List.In (hot_ev_of MN1 n1 n2) (get_MQ MN1 n0) ->
                                  _of lock MN1 n2 <> None ->
                                  dep_on '' MN1 n0 n2.

  Proof.
    intros.

    destruct (NetMod.get n0 MN0) as [MQ00 [h0 s00] S00] eqn:?.
    consider (h0 = Rad.Rad_handle) by eauto with LTS.
    destruct (NetMod.get n0 MN1) as [MQ01 [h0 s01] S01] eqn:?.
    assert (handle (get_M MN1 n0) = Rad_handle) by eauto with LTS.

    destruct (NetMod.get n1 MN0) as [MQ10 [h1 s10] S10] eqn:?.
    consider (h1 = Rad.Rad_handle) by eauto with LTS.
    destruct (NetMod.get n1 MN1) as [MQ11 [h1 s11] S11] eqn:?.
    assert (handle (get_M MN1 n1) = Rad_handle) by eauto with LTS.

    destruct (NetMod.get n2 MN0) as [MQ20 [h2 s20] S20] eqn:?.
    consider (h2 = Rad.Rad_handle) by eauto with LTS.
    destruct (NetMod.get n2 MN1) as [MQ21 [h2 s21] S21] eqn:?.
    assert (handle (get_M MN1 n2) = Rad_handle) by eauto with LTS.

    assert (In (hot_ev_of MN1 n1 n2) (get_MQ MN0 n0) \/ ~ In (hot_ev_of MN1 n1 n2) (get_MQ MN0 n0)) as [|].
    {
      unfold hot_ev_of. clear.
      induction (get_MQ MN0 n0); attac.
      destruct `(_ \/ _); attac.
      destruct a; attac.
      destruct n.
      destruct (MProbe_eq_dec (hot_of MN1 n2) m); attac.
      destruct t; attac.
      smash_eq n n1; attac.
    }
    2: {
      unfold hot_ev_of in *.
      consider (a = NComm n1 n0 R ^ (hot_of MN1 n2)) by eauto using M_recv_ev_act.
      assert (sends_to MN0 n1 n0 (hot_of MN1 n2)).
      {
        remember (hot_of MN1 n2) as p; clear - H.
        consider (_ =(_)=> _); compat_hsimpl in *.
        unfold sends_to; ltac1:(autounfold with LTS_get in * ); attac.
      }
      consider (net_lock_on '' MN0 n0 n1 /\ net_lock_on '' MN1 n0 n1).
      {
        assert (net_lock_on '' MN0 n0 n1) by eauto with LTS.
        split; auto.
        destruct (net_sane_lock_dec '' MN1 n0 n1); eauto with LTS.
        consider (exists v, NComm n1 n0 R ^ (hot_of MN1 n2) = NComm n1 n0 R (MValP v)) by eauto using SRPC_M_net_unlock_reply with LTS.
        bs.
      }
      assert (_of lock MN0 n2 <> None).
      {
        intros ?.
        destruct (_of lock MN1 n2) as [n3|] eqn:?; doubt.
        consider (exists v, NComm n1 n0 R ^ (hot_of MN1 n2) = NComm n2 n3 Q (MValP v)) by eauto using M_lock_set.
      }
      assert (hot_of MN1 n2 = hot_of MN0 n2).
      {
        enough (_of lock_id MN1 n2 = _of lock_id MN0 n2) by (unfold hot_of; attac).
        destruct (PeanoNat.Nat.eq_dec (_of lock_id MN1 n2) (_of lock_id MN0 n2)); auto.
        consider (exists n3' v, NComm n1 n0 R ^ (hot_of MN1 n2) = NComm n2 n3' Q (MValP v)) by eauto using M_lock_id_update.
        bs.
      }
      rewrite `(hot_of _ _ = _) in *.

      assert (dep_on '' MN0 n0 n2) by eauto with LTS.

      enough ('' MN0 = '' MN1) by attac.
      eapply net_deinstr_act_skip; attac.
    }

    destruct (_of lock MN1 n2) as [n3|] eqn:?. 2: doubt.

    assert ((exists v, a = NComm n2 n3 Q (MValP v)) \/ forall v, a <> NComm n2 n3 Q (MValP v)) as [|].
    {
      clear.
      destruct_mna a; try (solve [left; eexists; eattac | right; eattac ]).
      smash_eq n n0 n2 n3; try (solve [left; eexists; eattac | right; eattac ]).
    }
    - assert (_of lock_id MN0 n2 < _of lock_id MN1 n2).
      {
        hsimpl in *.
        assert (_of lock_id MN1 n2 = S (_of lock_id MN0 n2)) by eauto using M_lock_id_update_act.
        lia.
      }

      enough (_of lock_id MN1 n2 <= _of lock_id MN0 n2) by lia.
      enough (index (hot_of MN1 n2) <= _of lock_id MN0 (init (hot_of MN1 n2))) by (simpl in *; lia).
      eauto with LTS.

    - assert (_of lock_id MN0 n2 = _of lock_id MN1 n2).
      {
        destruct (PeanoNat.Nat.eq_dec (_of lock_id MN0 n2) (_of lock_id MN1 n2)) as [He|He]; auto.
        consider (exists n3' v, a = NComm n2 n3' Q (MValP v)) by eauto using M_lock_id_update.
        consider (_of lock MN0 n2 = None /\ _of lock MN1 n2 = Some n3') by eauto using M_lock_set_act.
        attac.
      }
      replace (hot_ev_of MN1 n1 n2) with (hot_ev_of MN0 n1 n2) by (unfold hot_ev_of, hot_of; attac).
      assert (_of lock MN0 n2 = Some n3).
      {
        destruct (_of lock MN0 n2) as [n3'|] eqn:?.
        - enough (n3 = n3') by attac.
          eauto using M_lock_no_reset.
        - consider (exists v, a = NComm n2 n3 Q (MValP v)) by eauto using M_lock_set.
          bs.
      }
      assert (dep_on '' MN0 n0 n2) by (assert (_of lock MN0 n2 <> None) by attac; eauto with LTS).
      assert (dep_on '' MN1 n0 n2 \/ ~ dep_on '' MN1 n0 n2) as [|]; eauto using dep_dec_after_M with LTS.

      consider (exists n0' v, (n0 = n0' \/ dep_on '' MN1 n0 n0') /\ a = NComm n2 n0' R (MValP v)).
      {
        destruct (MNAct_to_PNAct a) eqn:?.
        - assert ('' MN0 =(p)=> '' MN1) by eauto using net_deinstr_act_do with LTS.
          consider (exists n0' v, p = NComm n2 n0' R v /\ (n0' = n0 \/ dep_on '' MN1 n0 n0')).
          {
            eapply net_dep_on_unlock with (n0:=n0)(n1:=n2)(N1:=''MN1)(N0:=''MN0); eauto with LTS.
          }

          exists n0', v.
          split.
          1: { destruct `(_ \/ _); eauto using eq_sym. }
          destruct_mna a; doubt.
          attac.
        - replace ('' MN1) with ('' MN0) by eauto using net_deinstr_act_skip with LTS.
          bs.
      }

      bs (n2 <> n2) by eauto using M_lock_no_send.
  Qed.


  Lemma KIS_invariant_sendp_hot [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    (forall n0 n1 n2, sends_to MN1 n1 n0 (hot_of MN1 n2) -> _of lock MN1 n2 <> None -> dep_on '' MN1 n0 n2).

  Proof.
    intros.

    destruct (NetMod.get n0 MN0) as [MQ00 [h0 s00] S00] eqn:?.
    consider (h0 = Rad.Rad_handle) by eauto with LTS.
    destruct (NetMod.get n0 MN1) as [MQ01 [h0 s01] S01] eqn:?.
    assert (handle (get_M MN1 n0) = Rad_handle) by eauto with LTS.

    destruct (NetMod.get n1 MN0) as [MQ10 [h1 s10] S10] eqn:?.
    consider (h1 = Rad.Rad_handle) by eauto with LTS.
    destruct (NetMod.get n1 MN1) as [MQ11 [h1 s11] S11] eqn:?.
    assert (handle (get_M MN1 n1) = Rad_handle) by eauto with LTS.

    destruct (NetMod.get n2 MN0) as [MQ20 [h2 s20] S20] eqn:?.
    consider (h2 = Rad.Rad_handle) by eauto with LTS.
    destruct (NetMod.get n2 MN1) as [MQ21 [h2 s21] S21] eqn:?.
    assert (handle (get_M MN1 n2) = Rad_handle) by eauto with LTS.

    assert (net_lock_on '' MN1 n0 n1) by eauto using KIS_invariant_sendp.

    destruct (sends_to_dec MN0 n1 n0 (hot_of MN1 n2)) as [|].
    2: {
      assert ((exists v, a = NTau n1 (MActP (Recv (n0, Q) v))) \/ a = NTau n1 (MActM Tau))
        by eauto using M_sends_to_send_set with LTS.

      assert (_of lock MN0 n2 <> None).
      {
        intros ?.
        destruct (_of lock MN1 n2) as [n3|] eqn:?; doubt.
        consider (exists v, a = NComm n2 n3 Q (MValP v)) by eauto using M_lock_set.
        destruct `(_ \/ _); bs.
      }
      assert (hot_of MN1 n2 = hot_of MN0 n2).
      {
        enough (_of lock_id MN1 n2 = _of lock_id MN0 n2) by (unfold hot_of; attac).
        destruct (PeanoNat.Nat.eq_dec (_of lock_id MN1 n2) (_of lock_id MN0 n2)); auto.
        consider (exists n3' v, a = NComm n2 n3' Q (MValP v)) by eauto using M_lock_id_update.
        destruct `(_ \/ _); bs.
      }
      rewrite `(hot_of _ _ = _) in *.

      assert (net_lock_on '' MN0 n0 n1).
      {
        destruct (net_sane_lock_dec '' MN0 n0 n1); auto with LTS.
        consider (exists v, a = NComm n0 n1 Q (MValP v)) by eauto using SRPC_M_net_new_lock_query with LTS.
        destruct `(_ \/ _); bs.
      }

      destruct `(_ \/ _).
      - hsimpl in *.
        enough (n2 = n1) by attac 2.
        consider (_ =(_)=> _); compat_hsimpl in * |-.
        assert (_of self MN0 n1 = n1) by eauto with LTS.
        unfold hot_ev_of, hot_of in *; ltac1:(autounfold with LTS_get in * ).
        destruct &lock.
        consider (sends_to_mon _ _ _); attac 2.
        consider (sends_to_mon _ _ _).
        bs.
      - assert (dep_on '' MN0 n0 n2).
        {
          enough (dep_on '' MN0 n1 n2) by attac.
          enough (exists n', List.In (hot_ev_of MN0 n' n2) (get_MQ MN0 n1)) by (hsimpl in *; eauto with LTS).
          unfold hot_ev_of, hot_of, sends_to in *.
          ltac1:(autounfold with LTS_get in * ); hsimpl in *.
          consider (_ =(_)=> _); compat_hsimpl in *.
          blast_cases; attac.
        }

        assert (dep_on '' MN1 n0 n2 \/ ~ dep_on '' MN1 n0 n2) as [|] by eauto using dep_dec_after_M with LTS; auto.

        assert (exists m0 m1 v, (n0 = m0 \/ dep_on '' MN0 n0 m0) /\ NTau n1 (MActM Tau) = NComm m1 m0 R (MValP v)).
        {
          subst.
          destruct (MNAct_to_PNAct (NTau n1 (MActM Tau))) eqn:?.
          - assert ('' MN0 =(p)=> '' MN1) by eauto using net_deinstr_act_do with LTS.
            consider (exists n0' v, p = NComm n2 n0' R v /\ (n0' = n0 \/ dep_on '' MN1 n0 n0')).
            {
              eapply net_dep_on_unlock with (n0:=n0)(n1:=n2)(N1:=''MN1)(N0:=''MN0); eauto with LTS.
            }
            bs.
          - replace ('' MN1) with ('' MN0) by eauto using eq_sym, net_deinstr_act_skip.
            bs.
        }
        hsimpl in *; bs.
    }

    destruct (_of lock MN1 n2) as [n3|] eqn:?. 2: doubt.

    assert ((exists v, a = NComm n2 n3 Q (MValP v)) \/ forall v, a <> NComm n2 n3 Q (MValP v)) as [|].
    {
      clear.
      destruct_mna a; try (solve [left; eexists; eattac | right; eattac ]).
      smash_eq n n0 n2 n3; try (solve [left; eexists; eattac | right; eattac ]).
    }
    - assert (_of lock_id MN0 n2 < _of lock_id MN1 n2).
      {
        hsimpl in *.
        assert (_of lock_id MN1 n2 = S (_of lock_id MN0 n2)) by eauto using M_lock_id_update_act.
        lia.
      }

      enough (_of lock_id MN1 n2 <= _of lock_id MN0 n2) by lia.
      enough (index (hot_of MN1 n2) <= _of lock_id MN0 (init (hot_of MN1 n2))) by (simpl in *; lia).
      eauto with LTS.
    - assert (_of lock_id MN0 n2 = _of lock_id MN1 n2).
      {
        destruct (PeanoNat.Nat.eq_dec (_of lock_id MN0 n2) (_of lock_id MN1 n2)) as [He|He]; auto.
        consider (exists n3' v, a = NComm n2 n3' Q (MValP v)) by eauto using M_lock_id_update.
        consider (_of lock MN0 n2 = None /\ _of lock MN1 n2 = Some n3') by eauto using M_lock_set_act.
        attac.
      }
      replace (hot_of MN1 n2) with (hot_of MN0 n2) by (unfold hot_of; attac).
      assert (_of lock MN0 n2 = Some n3).
      {
        destruct (_of lock MN0 n2) as [n3'|] eqn:?.
        - enough (n3 = n3') by attac.
          eauto using M_lock_no_reset.
        - consider (exists v, a = NComm n2 n3 Q (MValP v)) by eauto using M_lock_set.
          bs.
      }
      assert (dep_on '' MN0 n0 n2) by (assert (_of lock MN0 n2 <> None) by attac; eauto with LTS).

      assert (dep_on '' MN1 n0 n2 \/ ~ dep_on '' MN1 n0 n2) as [|] by eauto using dep_dec_after_M with LTS; auto.

      consider (exists n0' v, (n0 = n0' \/ dep_on '' MN1 n0 n0') /\ a = NComm n2 n0' R (MValP v)).
      {
        destruct (MNAct_to_PNAct a) eqn:?.
        - assert ('' MN0 =(p)=> '' MN1) by eauto using net_deinstr_act_do with LTS.
          consider (exists n0' v, p = NComm n2 n0' R v /\ (n0' = n0 \/ dep_on '' MN1 n0 n0')).
          {
            eapply net_dep_on_unlock with (n0:=n0)(n1:=n2)(N1:=''MN1)(N0:=''MN0); eauto with LTS.
          }

          exists n0', v.
          split.
          1: { destruct `(_ \/ _); eauto using eq_sym. }
            destruct_mna a; doubt.
          attac.
        - replace ('' MN1) with ('' MN0) by eauto using net_deinstr_act_skip with LTS.
          bs.
      }

      bs (n2 <> n2) by eauto using M_lock_no_send.
  Qed.


  Lemma KIS_invariant_alarm [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n, _of alarm MN1 n = true -> dep_on '' MN1 n n.

  Proof.
    intros.
    destruct (NetMod.get n MN0) as [MQ [h s] S] eqn:?.
    consider (h = Rad.Rad_handle) by eauto with LTS.

    enough (dep_on '' MN0 n n).
    {
      assert (deadlocked n '' MN0) by (eauto using dep_self_deadlocked with LTS).
      eauto 3 using deadlocked_M_dep_invariant1 with LTS.
    }

    destruct (_of alarm MN0 n) eqn:?; eauto 2 with LTS.

    consider (a = NTau n (MActM Tau) /\
                exists n1, List.In (EvRecv (n1, R) {|init:=n; index:=_of lock_id MN0 n|}) (get_MQ MN0 n)) by eauto using M_alarm_set.

    assert (List.In (hot_ev_of MN0 n1 n) (get_MQ MN0 n)) by eauto with LTS.

    enough (_of lock MN0 n <> None) by eauto with LTS.

    consider (_ =(_)=> _); compat_hsimpl in *.
    ltac1:(autounfold with LTS_get in * ); hsimpl in *.
    blast_cases; attac.
  Qed.


  Theorem KIS_invariant : trans_invariant KIS always.

  Proof.
    unfold trans_invariant.
    intros.
    constructor;
      eauto using
        KIS_invariant_sane
      , KIS_invariant_self
      , KIS_invariant_Rad
      , KIS_invariant_lock
      , KIS_invariant_wait
      , KIS_invariant_sendp
      , KIS_invariant_index_sendp
      , KIS_invariant_index_recvp
      , KIS_invariant_recvp_hot
      , KIS_invariant_sendp_hot
      , KIS_invariant_alarm.
  Qed.

  Hint Resolve KIS_invariant : LTS inv.
  Hint Extern 0 (KIS _) => solve_invariant : LTS.


  Lemma KIS_detection [MN n] :
    KIS MN ->
    _of alarm MN n = true ->
    exists DS, DeadSet DS '' MN /\ In n DS.

  Proof.
    intros.
    enough (deadlocked n MN) by (consider (deadlocked _ _); attac).
    enough (dep_on '' MN n n) by eauto using dep_self_deadlocked with LTS.
    consider (KIS MN).
  Qed.


  Theorem detection_soundness [i0 N0 MN1 mpath n] :
    KIS (net_instr i0 N0) ->
    (net_instr i0 N0 =[mpath]=> MN1) ->
    _of alarm MN1 n = true ->
    exists DS, DeadSet DS '' MN1 /\ In n DS.

  Proof.
    intros.
    eauto using KIS_detection with LTS.
  Qed.


  Lemma MNPath_do : forall mpath MN0 MN1,
      (MN0 =[mpath]=> MN1) ->
      (net_deinstr MN0 =[mpath]=> net_deinstr MN1).

  Proof.
    induction mpath; intros.
    1: attac.
    hsimpl in *.
    destruct (MNAct_to_PNAct a) eqn:?.
    - apply path_seq1 with (middle:=''N1).
      2: eauto.
      destruct a; kill Heqo; blast_cases; doubt; hsimpl in |- *.
      + Print Serv_Transp_M.
        Print MNAct_to_PNAct.
        assert ('' MN0 =(p)=> '' N1). eapply net_deinstr_act_do. 2: eauto. simpl in *. eauto.
        attac.
        {
          constructor. eauto with LTS.
          unfold net_deinstr in *.
          rewrite NetMod.put_map in *.
          constructor.
          rewrite NetMod.get_map in *.
          hsimpl in *.
          subst.
          rewrite H.
          attac.
          kill H2.
          kill H3.
          hsimpl in *.
          rewrite H in *.
          unfold deinstr in *.
          eauto.
        }

      + assert ('' MN0 =(p)=> '' N1). eapply net_deinstr_act_do. 2: eauto. simpl in *. eauto.
        attac.
        kill H2.
        kill H1.
        kill H3.
        unfold net_deinstr in *.
        smash_eq n n0; hsimpl in *.
        * rewrite NetMod.put_map in *.
          rewrite H7 in *.
          eapply NComm_eq.
          -- rewrite NetMod.get_map in *.
             eapply H2.
          -- eauto.
             eattac.
        * rewrite NetMod.put_map in *.
          eapply NComm_neq; eauto.
          -- rewrite NetMod.get_map in *.
             eapply H2.
          -- eauto.
             eattac.
    - replace ('' MN0) with ('' N1) by eauto using net_deinstr_act_skip, eq_sym.
      eapply path_seq1 with (middle:=N1).
      2: eauto.
      destruct a; kill Heqo; blast_cases; doubt; hsimpl in |- *.
      + eapply NTrans_Tau_inv.
        kill H; hsimpl in *.
        unfold net_deinstr.
        rewrite NetMod.put_map in *.
        hsimpl.
        eexists; eattac.
      + eapply NTrans_Tau_inv.
        kill H; hsimpl in *.
        unfold net_deinstr.
        rewrite NetMod.put_map in *.
        hsimpl.
        eexists; eattac.
      + eapply NTrans_Tau_inv.
        kill H; hsimpl in *.
        unfold net_deinstr.
        rewrite NetMod.put_map in *.
        hsimpl.
        eexists; eattac.
      + eapply NTrans_Tau_inv.
        kill H; hsimpl in *.
        unfold net_deinstr.
        rewrite NetMod.put_map in *.
        hsimpl.
        eexists; eattac.
      + smash_eq n n0.
        * eapply NTrans_Comm_eq_inv.
          kill H; hsimpl in *.
          eexists _, _; eattac.
        * eapply NTrans_Comm_neq_inv.
          kill H; hsimpl in *.
          eexists _, _; eattac.
  Qed.
  (* TODO: make it into a normal relation? *)


  Corollary detection_soundness_instr [N0 i0 MN1 mpath0 n] :
    KIS (net_instr i0 N0) ->
    (net_instr i0 N0 =[ mpath0 ]=> MN1) ->
    _of alarm MN1 n = true ->
    exists mpath1 i1 N1 DS,
      (MN1 =[mpath1]=> net_instr i1 N1)
      /\ (N0 =[ mpath0 ++ mpath1 ]=> N1)
      /\ In n DS
      /\ DeadSet DS N1.

  Proof.
    intros.

    consider (exists mpath1 path i2 N2, (MN1 =[ mpath1 ]=> net_instr i2 N2) /\ (N0 =[ path ]=> N2)) by eauto using Net_Transp_soundness.
    assert ('' (net_instr i0 N0) =[mpath0 ++ mpath1]=> '' (net_instr i2 N2)) by eauto using MNPath_do with LTS.

    hsimpl in *.

    consider (exists DS, DeadSet DS '' MN1 /\ In n DS) by eauto using detection_soundness.

    assert (DeadSet DS '' (net_instr i2 N2)).
    {
      consider (exists ppath, '' MN1 =[ppath]=> '' (net_instr i2 N2)) by eauto using Net_path_corr.
      attac.
    }

    exists mpath1, i2, N2, DS.
    eattac.
  Qed.
End SOUND_F.

Module Type SOUND(Conf : DETECT_CONF) := Conf <+ DETECT_PARAMS(Conf) <+ SOUND_F.
