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
      SRPC_serv_in_net *)


    Lemma SRPC_M_net_AnySrpc [N S n] :
      well_formed '' N ->
      NetMod.get n N = S ->
      AnySRPC_serv S.
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *; hsimpl in *.
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
      well_formed '' N ->
      NetMod.get n N = mserv (MQ0 ++ MqRecv (c, Q) v :: MQ1) M (serv I P O) ->
      ~ List.In (c, Q, v') (I ++ retract_recv (MQ0 ++ MQ1)).

    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      hsimpl in *.
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      rewrite retract_recv_app.
      remember (retract_recv MQ1) as I1 eqn:x; clear x.
      repeat (rewrite (app_assoc) in * ).
      remember (&I ++ retract_recv MQ0) as I0 eqn:x.
      destruct (Deq_dec' I0 (c, Q)); hsimpl in *.
      - rename Q' into I0'.
        assert (Deq (c, Q) v0 (_ ++ (c, Q, v) :: I1) (I0' ++ (c, Q, v) :: I1)) by attac.
        bs (~ List.In (c, Q, v) (I0' ++ (c, Q, v) :: I1)).
      - assert (Deq (c, Q) v ((c, Q, v) :: I1) I1) by attac.
        bs (Deq (c, Q) v (_ ++ (c, Q, v) :: I1) (_ ++ I1)) by eauto using Deq_app_l_not_Deq.
    Qed.

    Lemma SRPC_M_net_in_net_Q_in_M0 [N n c v v' MQ0 MQ1 M S] :
      well_formed '' N ->
      NetMod.get n N = mserv (MQ0 ++ MqRecv (c, Q) v :: MQ1) M S ->
      ~ List.In (MqRecv (c, Q) v') MQ0.
    Proof. intros. destruct S as [I P O].
           assert (~ List.In (c, Q, v') (&I ++ retract_recv (MQ0 ++ MQ1))) by eauto using SRPC_M_net_in_net_Q_in_M.
           iattac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_in_M1 [N n c v v' MQ0 MQ1 M S] :
      well_formed '' N ->
      NetMod.get n N = mserv (MQ0 ++ MqRecv (c, Q) v :: MQ1) M S ->
      ~ List.In (MqRecv (c, Q) v') MQ1.
    Proof. intros. destruct S as [I P O].
           assert (~ List.In (c, Q, v') (&I ++ retract_recv (MQ0 ++ MQ1))) by eauto using SRPC_M_net_in_net_Q_in_M.
           iattac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_in_MP [N n c v v' MQ0 MQ1 M I P O] :
      well_formed '' N ->
      NetMod.get n N = mserv (MQ0 ++ MqRecv (c, Q) v :: MQ1) M (serv I P O) ->
      ~ List.In (c, Q, v') I.
    Proof. intros.
           assert (~ List.In (c, Q, v') (&I ++ retract_recv (MQ0 ++ MQ1))) by eauto using SRPC_M_net_in_net_Q_in_M.
           iattac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_in_P [N n c v v' MQ M I I' P O] :
      well_formed '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (c, Q) v I I' ->
      ~ List.In (c, Q, v') (I' ++ retract_recv MQ).

    Proof.
      intros.
      kill H. specialize (H_wf_SRPC n) as [srpc H].
      hsimpl in *.
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      assert (Deq (c, Q) v (&I ++ retract_recv MQ) (I' ++ retract_recv MQ)) by attac.
      iattac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_in_PP [N n c v v' MQ M I I' P O] :
      well_formed '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (c, Q) v I I' ->
      ~ List.In (c, Q, v') I'.
    Proof. intros.
           assert (~ List.In (c, Q, v') (&I' ++ retract_recv MQ)) by eauto using SRPC_M_net_in_net_Q_in_P.
           iattac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_in_PM [N n c v v' MQ M I I' P O] :
      well_formed '' N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (c, Q) v I I' ->
      ~ List.In (MqRecv (c, Q) v') MQ.
    Proof. intros.
           assert (~ List.In (c, Q, v') (&I' ++ retract_recv MQ)) by eauto using SRPC_M_net_in_net_Q_in_P.
           iattac.
    Qed.

    Lemma SRPC_M_net_in_net_R_in_M [N n s s' v v' MQ0 MQ1 M I P O] :
      well_formed '' N ->
      NetMod.get n N = mserv (MQ0 ++ MqRecv (s, R) v :: MQ1) M (serv I P O) ->
      ~ List.In (s', R, v') (I ++ retract_recv (MQ0 ++ MQ1)).

    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      hsimpl in *.
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      remember (retract_recv MQ1) as I1 eqn:x; clear x.
      repeat (rewrite (app_assoc) in * ).
      remember (&I ++ retract_recv MQ0) as I0 eqn:x.

      destruct (Deq_dec' I0 (s, R)); hsimpl in *.
      - rename Q' into I0'.
        assert (Deq (s, R) v0 (_ ++ (s, R, v) :: I1) (I0' ++ (s, R, v) :: I1)) by attac.
        bs (~ List.In (s, R, v) (I0' ++ (s, R, v) :: I1)).
      - assert (Deq (s, R) v ((s, R, v) :: I1) I1) by attac.
        assert (Deq (s, R) v (_ ++ (s, R, v) :: I1) (_ ++ I1)) by eauto using Deq_app_l_not_Deq.
        bs (~ List.In (s', R, v) (_ ++ I1)).
    Qed.

    Lemma SRPC_M_net_in_net_R_in_M0 [N n s s' v v' MQ0 MQ1 M S] :
      well_formed '' N ->
      NetMod.get n N = mserv (MQ0 ++ MqRecv (s, R) v :: MQ1) M S ->
      ~ List.In (MqRecv (s', R) v') MQ0.
    Proof.
      intros. destruct S as [I P O].
      assert (~ List.In (s', R, v') (&I ++ retract_recv (MQ0 ++ MQ1))) by eauto using SRPC_M_net_in_net_R_in_M.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_in_M1 [N n s s' v v' MQ0 MQ1 M S] :
      well_formed '' N ->
      NetMod.get n N = mserv (MQ0 ++ MqRecv (s, R) v :: MQ1) M S ->
      ~ List.In (MqRecv (s', R) v') MQ1.
    Proof.
      intros. destruct S as [I P O].
      assert (~ List.In (s', R, v') (&I ++ retract_recv (MQ0 ++ MQ1))) by eauto using SRPC_M_net_in_net_R_in_M.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_in_MP [N n s s' v v' MQ0 MQ1 M I P O] :
      well_formed '' N ->
      NetMod.get n N = mserv (MQ0 ++ MqRecv (s, R) v :: MQ1) M (serv I P O) ->
      ~ List.In (s', R, v') I.
    Proof.
      intros.
      assert (~ List.In (s', R, v') (&I ++ retract_recv (MQ0 ++ MQ1))) by eauto using SRPC_M_net_in_net_R_in_M.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_in_P [N : MNet] [ n s s' v v' MQ M I I' P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (s, R) v I I' ->
      ~ List.In (s', R, v') (I' ++ retract_recv MQ).

    Proof.
      intros.
      kill H. specialize (H_wf_SRPC n) as [srpc H].
      hsimpl in *.
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_in_PP [N : MNet] [ n s s' v v' MQ M I I' P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (s, R) v I I' ->
      ~ List.In (s', R, v') I'.
    Proof.
      intros.
      assert (~ List.In (s', R, v') (&I' ++ retract_recv MQ)) by eauto using SRPC_M_net_in_net_R_in_P.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_in_PM [N : MNet] [ n s s' v v' MQ M I I' P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (s, R) v I I' ->
      ~ List.In (MqRecv (s', R) v') MQ.
    Proof.
      intros.
      assert (~ List.In (s', R, v') (&I' ++ retract_recv MQ)) by eauto using SRPC_M_net_in_net_R_in_P.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_in_locked [N : MNet] [ n s v MQ M S] :
      well_formed N ->
      NetMod.get n N = mserv MQ M S ->
      List.In (MqRecv (s, R) v) MQ ->
      exists c, SRPC_serv (Locked c s) (NetMod.get n N).
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *.
      hsimpl in *.
      consider (exists c, srpc = Locked c s); eattac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_out_locked [N : MNet] [ n s v MQ M S] :
      well_formed N ->
      NetMod.get n N = mserv MQ M S ->
      List.In (MqSend (s, Q) v) MQ ->
      exists c, SRPC_serv (Locked c s) (NetMod.get n N).
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *.
      hsimpl in *.
      consider (exists c, srpc = Locked c s); eattac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_out_uniq_M [N : MNet] [ n c v v' MQ0 MQ1 M I P O] :
      well_formed N ->
      NetMod.get n N = mserv (MQ0 ++ MqSend (c, R) v :: MQ1) M (serv I P O) ->
      ~ List.In (c, R, v') (retract_send (MQ0 ++ MQ1) ++ O).

    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      hsimpl in *.
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      repeat (rewrite <- app_assoc in * ).
      repeat (rewrite <- app_comm_cons in * ).
      remember (retract_send MQ1 ++ &O) as O1 eqn:x; clear x.
      remember (retract_send MQ0) as O0 eqn:x; clear x.

      destruct (Deq_dec' O0 (c, R)); hsimpl in *.
      - rename Q' into O0'.
        assert (Deq (c, R) v0 (O0 ++ (c, R, v) :: O1) (O0' ++ (c, R, v) :: O1)) by attac.
        bs (~ List.In (c, R, v) (O0' ++ (c, R, v) :: O1)).
      - assert (Deq (c, R) v ((c, R, v) :: O1) O1) by attac.
        assert (Deq (c, R) v (O0 ++ (c, R, v) :: O1) (O0 ++ O1)) by eauto using Deq_app_l_not_Deq.
        bs (~ List.In (c, R, v) (O0 ++ O1)).
    Qed.

    Lemma SRPC_M_net_in_net_Q_out_uniq_M0 [N : MNet] [ n c v v' MQ0 MQ1 M S] :
      well_formed N ->
      NetMod.get n N = mserv (MQ0 ++ MqSend (c, R) v :: MQ1) M S ->
      ~ List.In (MqSend (c, R) v') MQ0.
    Proof.
      intros. destruct S as [I P O].
      assert (~ List.In (c, R, v') (retract_send (MQ0 ++ MQ1) ++ &O)) by eauto using SRPC_M_net_in_net_Q_out_uniq_M.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_out_uniq_M1 [N : MNet] [ n c v v' MQ0 MQ1 M S] :
      well_formed N ->
      NetMod.get n N = mserv (MQ0 ++ MqSend (c, R) v :: MQ1) M S ->
      ~ List.In (MqSend (c, R) v') MQ1.
    Proof.
      intros. destruct S as [I P O].
      assert (~ List.In (c, R, v') (retract_send (MQ0 ++ MQ1) ++ &O)) by eauto using SRPC_M_net_in_net_Q_out_uniq_M.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_out_uniq_MP [N : MNet] [ n c v v' MQ0 MQ1 M I P O] :
      well_formed N ->
      NetMod.get n N = mserv (MQ0 ++ MqSend (c, R) v :: MQ1) M (serv I P O) ->
      ~ List.In (c, R, v') O.
    Proof.
      intros.
      assert (~ List.In (c, R, v') (retract_send (MQ0 ++ MQ1) ++ &O)) by eauto using SRPC_M_net_in_net_Q_out_uniq_M.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_out_uniq_P [N : MNet] [ n c v v' MQ M I P O O'] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (c, R) v O O' ->
      ~ (List.In (c, R, v') (retract_send MQ ++ O')).
    Proof.
      intros.
      kill H. specialize (H_wf_SRPC n) as [srpc H].
      hsimpl in *.
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      remember (retract_send MQ) as O1 eqn:x; clear x.

      destruct (Deq_dec' O1 (c, R)); hsimpl in *.
      - rename Q' into O1'.
        assert (Deq (c, R) v0 (O1 ++ &O) (O1' ++ &O)) by attac.
        assert (~ List.In (c, R, v) (O1' ++ &O)) by attac.
        bs (List.In (c, R, v) &O) by attac.
      - assert (Deq (c, R) v (O1 ++ &O) (O1 ++ O')) by eauto using Deq_app_l_not_Deq.
        bs (~ List.In (c, R, v) (O1 ++ O')).
    Qed.

    Lemma SRPC_M_net_in_net_Q_out_uniq_PM [N : MNet] [ n c v v' MQ M I P O O'] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (c, R) v O O' ->
      ~ (List.In (MqSend (c, R) v') MQ).
    Proof.
      intros.
      assert (~ (List.In (c, R, v') (retract_send MQ ++ O'))) by eauto using SRPC_M_net_in_net_Q_out_uniq_P.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_out_uniq_PP [N : MNet] [ n c v v' MQ M I P O O'] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      Deq (c, R) v O O' ->
      ~ (List.In (c, R, v') O').
    Proof.
      intros.
      assert (~ (List.In (c, R, v') (retract_send MQ ++ O'))) by eauto using SRPC_M_net_in_net_Q_out_uniq_P.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_Q_M [N : MNet] [ n s v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (MqRecv (s, R) v) MQ ->
      ~ (List.In (s, Q, v') (retract_send MQ ++ O)).
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_Q_MM [N : MNet] [ n s v v' MQ M S] :
      well_formed N ->
      NetMod.get n N = mserv MQ M S ->
      List.In (MqRecv (s, R) v) MQ ->
      ~ (List.In (MqSend (s, Q) v') MQ).
    Proof.
      intros. destruct S as [I P O].
      assert ( ~ (List.In (s, Q, v') (retract_send MQ ++ &O))) by eauto using SRPC_M_net_in_net_R_Q_M.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_Q_MP [N : MNet] [ n s v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (MqRecv (s, R) v) MQ ->
      ~ (List.In (MqSend (s, Q) v') MQ).
    Proof.
      intros.
      assert ( ~ (List.In (s, Q, v') (retract_send MQ ++ &O))) by eauto using SRPC_M_net_in_net_R_Q_M.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_Q_P [N : MNet] [ n s v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (s, R, v) I ->
      ~ (List.In (s, Q, v') (retract_send MQ ++ O)).
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_Q_PM [N : MNet] [ n s v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (s, R, v) I ->
      ~ (List.In (MqSend (s, Q) v') MQ).
    Proof.
      intros.
      assert ( ~ (List.In (s, Q, v') (retract_send MQ ++ &O))) by eauto using SRPC_M_net_in_net_R_Q_P.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_Q_PP [N : MNet] [ n s v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (s, R, v) I ->
      ~ (List.In (s, Q, v') O).
    Proof.
      intros.
      assert (~ (List.In (s, Q, v') (retract_send MQ ++ &O))) by eauto using SRPC_M_net_in_net_R_Q_P.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_R_M [N : MNet] [ n s v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (MqSend (s, Q) v) MQ ->
      ~ (List.In (s, R, v') (I ++ retract_recv MQ)).
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_R_MM [N : MNet] [ n s v v' MQ M S] :
      well_formed N ->
      NetMod.get n N = mserv MQ M S ->
      List.In (MqSend (s, Q) v) MQ ->
      ~ (List.In (MqRecv (s, R) v') MQ).
    Proof.
      intros. destruct S as [I P O].
      assert ( ~ (List.In (s, R, v') (&I ++ retract_recv MQ))) by eauto using SRPC_M_net_in_net_Q_R_M.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_R_MP [N : MNet] [ n s v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (MqSend (s, Q) v) MQ ->
      ~ (List.In (s, R, v') I).
    Proof.
      intros.
      assert ( ~ (List.In (s, R, v') (&I ++ retract_recv MQ))) by eauto using SRPC_M_net_in_net_Q_R_M.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_R_P [N : MNet] [ n s v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (s, Q, v) O ->
      ~ (List.In (s, R, v') (I ++ retract_recv MQ)).
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_R_PM [N : MNet] [ n s v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (s, Q, v) O ->
      ~ (List.In (MqRecv (s, R) v') MQ).
    Proof.
      intros.
      assert ( ~ (List.In (s, R, v') (&I ++ retract_recv MQ))) by eauto using SRPC_M_net_in_net_Q_R_P.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_R_PP [N : MNet] [ n s v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (s, Q, v) O ->
      ~ (List.In (s, R, v') I).
    Proof.
      intros.
      assert ( ~ (List.In (s, R, v') (&I ++ retract_recv MQ))) by eauto using SRPC_M_net_in_net_Q_R_P.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_excl_R_M [N : MNet] [ n c v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (MqRecv (c, Q) v) MQ ->
      ~ List.In (c, R, v') (retract_send MQ ++ O).
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_excl_R_MM [N : MNet] [ n c v v' MQ M S] :
      well_formed N ->
      NetMod.get n N = mserv MQ M S ->
      List.In (MqRecv (c, Q) v) MQ ->
      ~ List.In (MqSend (c, R) v') MQ.
    Proof.
      intros. destruct S as [I P O].
      assert (~ List.In (c, R, v') (retract_send MQ ++ &O)) by eauto using SRPC_M_net_in_net_Q_excl_R_M.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_excl_R_MP [N : MNet] [ n c v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (MqRecv (c, Q) v) MQ ->
      ~ List.In (c, R, v') O.
    Proof.
      intros.
      assert (~ List.In (c, R, v') (retract_send MQ ++ &O)) by eauto using SRPC_M_net_in_net_Q_excl_R_M.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_excl_R_P [N : MNet] [ n c v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (c, Q, v) I ->
      ~ List.In (c, R, v') (retract_send MQ ++ O).
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_excl_R_PM [N : MNet] [ n c v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (c, Q, v) I ->
      ~ List.In (MqSend (c, R) v') MQ.
    Proof.
      intros.
      assert (~ List.In (c, R, v') (retract_send MQ ++ &O)) by eauto using SRPC_M_net_in_net_Q_excl_R_P.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_Q_excl_R_PP [N : MNet] [ n c v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (c, Q, v) I ->
      ~ List.In (c, R, v') O.
    Proof.
      intros.
      assert (~ List.In (c, R, v') (retract_send MQ ++ &O)) by eauto using SRPC_M_net_in_net_Q_excl_R_P.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_excl_c_M [N : MNet] [ n c v MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (MqRecv (c, Q) v) MQ ->
      ~ proc_client c P.
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_Q_excl_c_P [N : MNet] [ n c v MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (c, Q, v) I ->
      ~ proc_client c P.
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_excl_Q_M [N : MNet] [ n c v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (MqSend (c, R) v) MQ ->
      ~ List.In (c, Q, v') (I ++ retract_recv MQ).
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_excl_Q_MM [N : MNet] [ n c v v' MQ M S] :
      well_formed N ->
      NetMod.get n N = mserv MQ M S ->
      List.In (MqSend (c, R) v) MQ ->
      ~ List.In (MqRecv (c, Q) v') MQ.
    Proof.
      intros. destruct S as [I P O].
      assert (~ List.In (c, Q, v') (&I ++ retract_recv MQ)) by eauto using SRPC_M_net_in_net_R_excl_Q_M.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_excl_Q_MP [N : MNet] [ n c v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (MqSend (c, R) v) MQ ->
      ~ List.In (c, Q, v') I.
    Proof.
      intros.
      assert (~ List.In (c, Q, v') (&I ++ retract_recv MQ)) by eauto using SRPC_M_net_in_net_R_excl_Q_M.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_excl_Q_P [N : MNet] [ n c v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (c, R, v) O ->
      ~ List.In (c, Q, v') (I ++ retract_recv MQ).
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_excl_Q_PM [N : MNet] [ n c v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (c, R, v) O ->
      ~ List.In (MqRecv (c, Q) v') MQ.
    Proof.
      intros.
      assert (~ List.In (c, Q, v') (&I ++ retract_recv MQ)) by eauto using SRPC_M_net_in_net_R_excl_Q_P.
      attac.
    Qed.
    Lemma SRPC_M_net_in_net_R_excl_Q_PP [N : MNet] [ n c v v' MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (c, R, v) O ->
      ~ List.In (c, Q, v') I.
    Proof.
      intros.
      assert (~ List.In (c, Q, v') (&I ++ retract_recv MQ)) by eauto using SRPC_M_net_in_net_R_excl_Q_P.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_excl_c_M [N : MNet] [ n c v MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (MqRecv (c, Q) v) MQ ->
      ~ proc_client c P.
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_R_excl_c_P [N : MNet] [ n c v MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      List.In (c, Q, v) I ->
      ~ proc_client c P.
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      attac.
    Qed.

    Lemma SRPC_M_net_in_net_c_excl_Q_M [N : MNet] [ n c v MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      proc_client c P ->
      ~ List.In (MqRecv (c, Q) v) MQ.
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      enough (~ In (c, Q, v) (&I ++ retract_recv MQ)) by attac.
      eattac.
    Qed.

    Lemma SRPC_M_net_in_net_c_excl_Q_P [N : MNet] [ n c v MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      proc_client c P ->
      ~ List.In (c, Q, v) (I).
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      enough (~ In (c, Q, v) (&I ++ retract_recv MQ)) by attac.
      iattac.
    Qed.

    Lemma SRPC_M_net_in_net_c_excl_R [N : MNet] [ n c v MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      proc_client c P ->
      ~ List.In (c, R, v) (retract_send MQ ++ O).
    Proof.
      intros. kill H. specialize (H_wf_SRPC n) as [srpc H].
      unfold deinstr, serv_deinstr in *; hsimpl in *.
      iattac.
    Qed.

    Lemma SRPC_M_net_in_net_c_excl_R_M [N : MNet] [ n c v MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      proc_client c P ->
      ~ List.In (MqSend (c, R) v) MQ.
    Proof.
      intros.
      assert (~ List.In (c, R, v) (retract_send MQ ++ &O)) by eauto using SRPC_M_net_in_net_c_excl_R.
      iattac.
    Qed.

    Lemma SRPC_M_net_in_net_c_excl_R_P [N : MNet] [ n c v MQ M I P O] :
      well_formed N ->
      NetMod.get n N = mserv MQ M (serv I P O) ->
      proc_client c P ->
      ~ List.In (c, R, v) O.
    Proof.
      intros.
      assert (~ List.In (c, R, v) (retract_send MQ ++ &O)) by eauto using SRPC_M_net_in_net_c_excl_R.
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
    SRPC_M_net_in_net_R_in_locked
    SRPC_M_net_in_net_Q_out_locked
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


  Definition sends_to (MN : MNet) n0 n1 p := sends_to_mon (mserv_m (MN n0)) n1 p.
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

  Definition no_Q_probe_in (MN : MNet) n := no_Q_probe (mserv_m (MN n)).


  Inductive KIS (MN : MNet) :=
    KIS_
      (* We are well_formed *)
      (H_wf_S : well_formed '' MN)
      (* `self` is correct *)
      (H_self_S : forall n0, self (MN n0) = n0)
      (* Monitor correctly judges the lock, unless there is a reply incoming it is about to see *)
      (H_lock_S : forall n0 n1, locked (MN n0) = Some n1 -> lock '' MN n0 n1 \/ exists v, List.In (MqRecv (n1, R) v) (mserv_i (MN n0)))
      (* All members of the waiting list are locked on us *)
      (H_wait_S : forall n0 n1, List.In n0 (wait (MN n1)) -> lock '' MN n0 n1)
      (* Monitors send probes only to those locked. *)
      (H_sendp_S : forall n0 n1 p, sends_to MN n1 n0 p -> lock '' MN n0 n1)
      (* All sent probes have their lock_id no higher than the locked id of the initiator *)
      (H_lock_id_send_S : forall n0 n1 p, sends_to MN n0 n1 p -> (lock_id p <= lock_count (MN (origin p)))%nat)
      (* All received probes have their lock_id no higher than the locked id of the initiator *)
      (H_lock_id_recvp_S : forall n0 n1 p, List.In (MqProbe (n1, R) p) (mserv_i (MN n0)) -> (lock_id p <= lock_count (MN (origin p)))%nat)
      (* If we are about to receive a active probe of someone whose monitor considers locked, then we depend on them. *)
      (H_sendp_active_S : forall n0 n1 n2, sends_to MN n1 n0 (active_probe_of MN n2) -> locked (MN n2) <> None -> trans_lock '' MN n0 n2)
      (* If we received a active probe of someone whose monitor considers locked, then we depend on them. *)
      (H_recvp_active_S : forall n0 n1 n2, List.In (active_ev_of MN n2 n0) (mserv_i (MN n1)) -> locked (MN n0) <> None -> trans_lock '' MN n1 n0)
      (* No false alarms: if anyone screams, they are indeed deadlocked *)
      (H_alarm_S : forall n, alarm (MN n) = true -> trans_lock '' MN n n)
      : KIS MN.


  Lemma KIS_well_formed [MN] : KIS MN -> well_formed '' MN.
  Proof. intros; consider (KIS _). Qed.

  Lemma KIS_self [MN] : KIS MN -> forall n0, self (MN n0) = n0.
  Proof. intros; consider (KIS _). Qed.

  Lemma KIS_locked [MN] : KIS MN -> forall n0 n1, locked (MN n0) = Some n1 -> lock '' MN n0 n1 \/ exists v, List.In (MqRecv (n1, R) v) (mserv_i (MN n0)).
  Proof. intros; consider (KIS _). Qed.

  Lemma KIS_wait [MN] : KIS MN -> forall n0 n1, List.In n0 (wait (MN n1)) -> lock '' MN n0 n1.
  Proof. intros; consider (KIS _). Qed.

  Lemma KIS_sendp [MN] : KIS MN -> forall n0 n1 p, sends_to MN n1 n0 p -> lock '' MN n0 n1.
  Proof. intros; consider (KIS _). eauto. Qed.

  Lemma KIS_lock_id_sendp [MN] : KIS MN -> forall n0 n1 p, sends_to MN n0 n1 p -> (lock_id p <= lock_count (MN (origin p)))%nat.
  Proof. intros; consider (KIS _). eauto. Qed.

  Lemma KIS_lock_id_recvp [MN] : KIS MN -> forall n0 n1 p, List.In (MqProbe (n1, R) p) (mserv_i (MN n0)) -> (lock_id p <= lock_count (MN (origin p)))%nat.
  Proof. intros; consider (KIS _). eauto. Qed.

  Lemma KIS_sendp_active [MN] : KIS MN -> forall n0 n1 n2, sends_to MN n1 n0 (active_probe_of MN n2) -> locked (MN n2) <> None -> trans_lock '' MN n0 n2.
  Proof. intros; consider (KIS _). eauto. Qed.

  Lemma KIS_recvp_active [MN] : KIS MN -> forall n0 n1 n2, List.In (active_ev_of MN n2 n0) (mserv_i (MN n1)) -> locked (MN n0) <> None -> trans_lock '' MN n1 n0.
  Proof. intros; consider (KIS _). eauto. Qed.

  Lemma KIS_alarm [MN] : KIS MN -> forall n, alarm (MN n) = true -> trans_lock '' MN n n.
  Proof. intros; consider (KIS _). Qed.

  #[export] Hint Immediate
    KIS_well_formed
    KIS_self
    KIS_locked
    KIS_wait
    KIS_sendp
    KIS_lock_id_sendp
    KIS_lock_id_recvp
    KIS_sendp_active
    KIS_recvp_active
    KIS_alarm : LTS.


  Lemma KIS_self_get [MN n0] [MQ s S] [self'] :
    KIS MN ->
    NetMod.get n0 MN = mserv MQ (s) S ->
    self (next_state s) = self' ->
    self' = n0.

  Proof. intros. assert (self (MN n0) = n0) by eauto with LTS.
         ltac1:(autounfold with LTS_get in * ); hsimpl in * |-; auto.
  Qed.


  Lemma KIS_lock_get [MN n0 n1] [MQ s S] :
    KIS MN ->
    NetMod.get n0 MN = mserv MQ (s) S ->
    locked (next_state s) = Some n1 ->
    lock '' MN n0 n1 \/ exists v, List.In (MqRecv (n1, R) v) MQ.

  Proof. intros.
         assert (locked (MN n0) = Some n1) by (ltac1:(autounfold with LTS_get in * ); attac).
         assert (lock '' MN n0 n1 \/ exists v, List.In (MqRecv (n1, R) v) (mserv_i (MN n0))) by attac.
         ltac1:(autounfold with LTS_get in * ); hsimpl in * |-; auto.
  Qed.


  Lemma KIS_wait_get [MN n0 n1] [MQ s S] :
    KIS MN ->
    NetMod.get n1 MN = mserv MQ (s) S ->
    List.In n0 (wait (next_state s)) ->
    lock '' MN n0 n1.

  Proof. intros.
         assert (List.In n0 (wait (MN n1))) by (ltac1:(autounfold with LTS_get in * ); attac).
         assert (lock '' MN n0 n1) by attac.
         ltac1:(autounfold with LTS_get in * ); hsimpl in * |-; auto.
  Qed.


  Lemma KIS_lock_id_sendp_get [MN n0 n1 n2 p] [MQ0 MQ2 s0 s2 S0 S2] [lock_id' lock_count'] :
    KIS MN ->
    NetMod.get n0 MN = mserv MQ0 (s0) S0 ->
    NetMod.get n2 MN = mserv MQ2 (s2) S2 ->
    sends_to_mon s0 n1 p ->
    lock_id p = lock_id' ->
    origin p = n2 ->
    lock_count (next_state s2) = lock_count' ->
    lock_id' <= lock_count'.

  Proof. intros.
         assert (sends_to MN n0 n1 p) by (ltac1:(autounfold with LTS_get in * ); attac).
         assert (lock_id p <= lock_count (MN (origin p))) by attac.
         destruct p; simpl in *.
         ltac1:(autounfold with LTS_get in * ); attac.
         attac.
  Qed.


  Lemma KIS_lock_id_recvp_get [MN n0 n1 n2 p] [MQ0 MQ2 s0 s2 S0 S2] [lock_id' lock_count'] :
    KIS MN ->
    NetMod.get n0 MN = mserv MQ0 (s0) S0 ->
    NetMod.get n2 MN = mserv MQ2 (s2) S2 ->
    List.In (MqProbe (n1, R) p) MQ0 ->
    lock_id p = lock_id' ->
    origin p = n2 ->
    lock_count (next_state s2) = lock_count' ->
    lock_id' <= lock_count'.

  Proof. intros.
         assert (List.In (MqProbe (n1, R) p) (mserv_i (MN n0))) by (ltac1:(autounfold with LTS_get in * ); attac).
         assert (lock_id p <= lock_count (MN (origin p))) by attac.
         destruct p; simpl in *.
         ltac1:(autounfold with LTS_get in * ); attac.
         attac.
  Qed.


  Lemma KIS_sendp_active_get [MN n0 n1 n2 p] [MQ1 MQ2 s1 s2 S1 S2] [lock_count'] :
    KIS MN ->
    NetMod.get n1 MN = mserv MQ1 (s1) S1 ->
    NetMod.get n2 MN = mserv MQ2 (s2) S2 ->
    sends_to_mon s1 n0 p ->
    lock_id p = lock_count (next_state s2) ->
    origin p = n2 ->
    lock_count (next_state s2) = lock_count' ->
    locked (next_state s2) <> None ->
    trans_lock '' MN n0 n2.

  Proof. intros.
         destruct p.
         assert (sends_to MN n1 n0 (active_probe_of MN n2)) by (unfold active_probe_of in *; ltac1:(autounfold with LTS_get in * ); attac).
         assert (locked (MN n2) <> None) by (ltac1:(autounfold with LTS_get in * ); attac).
         eauto with LTS.
  Qed.


  Lemma KIS_recvp_active_get [MN n0 n1 n2 p] [MQ0 MQ2 s0 s2 S0 S2] [lock_count'] :
    KIS MN ->
    NetMod.get n0 MN = mserv MQ0 (s0) S0 ->
    NetMod.get n2 MN = mserv MQ2 (s2) S2 ->
    List.In (MqProbe (n1, R) p) MQ0 ->
    lock_id p = lock_count (next_state s2) ->
    origin p = n2 ->
    lock_count (next_state s2) = lock_count' ->
    locked (next_state s2) <> None ->
    trans_lock '' MN n0 n2.

  Proof. intros.
         destruct p.
         assert (List.In (active_ev_of MN n1 n2) (mserv_i (MN n0))) by (unfold active_ev_of, active_probe_of in *; ltac1:(autounfold with LTS_get in * ); attac).
         assert (locked (MN n2) <> None) by (ltac1:(autounfold with LTS_get in * ); attac).
         eauto with LTS.
  Qed.


  Lemma KIS_alarm_get [MN n0] [MQ s S] :
    KIS MN ->
    NetMod.get n0 MN = mserv MQ (s) S ->
    alarm (next_state s) = true ->
    trans_lock '' MN n0 n0.

  Proof. intros.
         enough (alarm (MN n0) = true) by attac.
         ltac1:(autounfold with LTS_get in * ); attac.
  Qed.

  Hint Resolve
    KIS_self_get
    KIS_lock_get
    KIS_wait_get
    KIS_lock_id_sendp_get
    KIS_lock_id_recvp_get
    KIS_sendp_active_get
    KIS_recvp_active_get
    KIS_alarm : LTS.


  Lemma KIS_invariant_well_formed [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    well_formed '' MN1.

  Proof.
    intros.
    assert (well_formed '' MN0) by eauto with LTS.
    destruct (MNAct_to_PNAct a) eqn:?.
    - eauto using deinstr_act_do with LTS.
    - now replace ('' MN1) with ('' MN0) by eauto using deinstr_act_skip with LTS.
  Qed.

  Hint Immediate KIS_invariant_well_formed : LTS.


  Lemma KIS_invariant_self [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n0, self (MN1 n0) = n0.

  Proof.
    intros.
    assert (self (MN0 n0) = n0) by attac.
    enough (self (MN0 n0) = self (MN1 n0)) by attac.
    eauto using net_preserve_self with LTS.
  Qed.

  Hint Immediate KIS_invariant_self : LTS.


  Ltac2 Notation "destruct_mna" a(constr) :=
      destruct $a as [? [[[? [|]]|[? [|]]|]|[[? ?]|[? ?]|]|[[? ?]|[? ?]|]] | ? ? [|] [?|?]]; doubt.

  Lemma M_lock_set [MN0 MN1 a n0 n1] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    locked (MN0 n0) = None ->
    locked (MN1 n0) = Some n1 ->
    exists v, a = NComm n0 n1 Q (MValP v).

  Proof.
    intros.
    destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; doubt.

    all:
      destruct s; hsimpl in *; simpl in *; doubt.

    - destruct n2 as [? [|]]; simpl in *; doubt.
    - eattac.
    - eattac.
  Qed.


  Lemma M_lock_unset [MN0 MN1 a n0 n1] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    locked (MN0 n0) = Some n1 ->
    locked (MN1 n0) = None ->
    exists v, a = NTau n0 (MActP (Recv (n1, R) v)).

  Proof.
    intros.
     destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; doubt.

    all:
      destruct s; hsimpl in *; simpl in *; doubt.

    - smash_eq n2 n1; eattac.
    - destruct n2 as [? [|]]; eattac.
      smash_eq n n1; eattac.
      destruct (NAME.eqb (origin msg) &self); attac.
      destruct (&lock_count =? lock_id msg); compat_hsimpl in *; attac.
      rewrite next_state_Send_all in *; attac.
  Qed.


  Lemma M_lock_no_send [MN0 MN1 n0 n1 m0 m1 t v] :
    KIS MN0 ->
    locked (MN0 n0) = Some n1 ->
    (MN0 =(NComm m0 m1 t (MValP v))=> MN1) ->
    n0 <> m0.

  Proof.
    intros.
    assert (lock '' MN0 n0 n1 \/ exists v, List.In (MqRecv (n1, R) v) (mserv_i (MN0 n0))) as [|]
        by eauto with LTS.
    1: eauto using locked_M_no_send with LTS.

    intros ?; subst.
    hsimpl in *.
    unfold NetGet in *.

    destruct (NetMod.get m0 '' MN0) as [I0 P0 O0] eqn:?.
    assert (List.In (n1, R, v0) I0).
    {
      destruct (NetMod.get m0 MN0) as [MQ0 M0 [I0' P0' O0']] eqn:?.
      unfold deinstr, serv_deinstr in *. hsimpl in *.
      attac.
    }

    consider (O0 = []).
    {
      consider (well_formed '' MN0) by eauto with LTS.
      specialize (H_wf_SRPC m0) as [srpc Hsrpc].
      hrewrite NetMod.get in *.
      replace O0 with (serv_o (serv I0 P0 O0)) by auto.
      eauto using service_wf_R_in_out_nil with LTS.
    }

    consider (_ =(_)=> _).
    compat_hsimpl in *.
    unfold deinstr, serv_deinstr in *.
    hsimpl in *.
    destruct P1.
    bs.
  Qed.


  Lemma M_lock_no_reset [MN0 MN1 a n0 n1 n1'] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    locked (MN0 n0) = Some n1 ->
    locked (MN1 n0) = Some n1' ->
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
       destruct s; hsimpl in *; simpl in *; doubt.

    - blast_cases; iattac.
    - destruct n2 as [? [|]]; eattac.
      smash_eq n n1; eattac.
      destruct (NAME.eqb (origin msg) &self); attac.
      destruct (&lock_count =? lock_id msg); attac.
      rewrite next_state_Send_all in *; attac.
    - bs (NComm n1' n1' Q # v <> NComm n1' n1' Q # v).
    - bs (NComm n0 n1' Q # v <> NComm n0 n1' Q # v).
  Qed.


  Lemma M_lock_set_act [MN0 MN1 n0 n1 v] :
    KIS MN0 ->
    (MN0 =(NComm n0 n1 Q (MValP v))=> MN1) ->
    locked (MN0 n0) = None /\ locked (MN1 n0) = Some n1.

  Proof.
    intros.
    consider (~ lock '' MN0 n0 n1 /\ lock '' MN1 n0 n1)
      by (eauto using SRPC_M_net_query_new_lock with LTS).

    split.
    - enough (forall n, locked (MN0 n0) <> Some n) by (destruct (locked (MN0 n0)); attac). intros ? ?.
      apply `(~ lock '' MN0 _ _).
      assert (lock '' MN0 n0 n \/ exists v, List.In (MqRecv (n, R) v) (mserv_i (MN0 n0))) as [|]
          by eauto with LTS.
      + consider (n = n1) by eauto using SRPC_M_net_no_immediate_relock with LTS.
      + hsimpl in *.

        destruct (NetMod.get n0 '' MN0) as [I0 P0 O0] eqn:?.
        assert (List.In (n, R, v0) I0).
        {
          unfold NetGet in *.
          destruct (NetMod.get n0 MN0) as [MQ0 M0 [I0' P0' O0']] eqn:?.
          unfold deinstr, serv_deinstr in *. hsimpl in *.
          attac.
        }

        consider (O0 = []).
        {
          consider (well_formed '' MN0) by eauto with LTS.
          specialize (H_wf_SRPC n0) as [srpc Hsrpc].
          rewrite `(NetMod.get n0 _ = _) in *.
          replace (O0) with (serv_o (serv I0 P0 O0)) by auto. (* TODO seek and destroy this bs *)
          eauto using service_wf_R_in_out_nil with LTS.
        }

        consider (_ =(_)=> _).
        compat_hsimpl in *.
        unfold deinstr, serv_deinstr in *.
        hsimpl in *.
        destruct P1.
        bs.
    - consider (_ =(_)=> _).
      compat_hsimpl in *.
      unfold deinstr, serv_deinstr in *.
      hsimpl in *.
      destruct s.
      simpl in *.
      unfold NetGet in *.
      smash_eq n0 n1; compat_hsimpl in *; attac.
  Qed.


  Lemma M_R_in_no_send [MN0 n0 n1 v MQ M I P O] :
    KIS MN0 ->
    NetMod.get n0 MN0 = mserv MQ M (serv I P O) ->
    List.In (n1, R, v) (I ++ retract_recv MQ)  ->
    (retract_send MQ ++ O) = [].

  Proof.
    intros.

    destruct (NetMod.get n0 '' MN0) as [I0 P0 O0] eqn:?.
    assert (List.In (n1, R, v) I0).
    {
      unfold NetGet in *.
      unfold deinstr, serv_deinstr in *. hsimpl in *.
      attac.
    }

    consider (O0 = []).
    {
      consider (well_formed '' MN0) by eauto with LTS.
      specialize (H_wf_SRPC n0) as [srpc Hsrpc].
      rewrite `(NetMod.get n0 _ = _) in *.
      replace (O0) with (serv_o (serv I0 P0 O0)) by auto. (* TODO seek and destroy this bs *)
      eauto using service_wf_R_in_out_nil with LTS.
    }

    unfold deinstr, serv_deinstr in *.
    attac.
  Qed.


  Lemma M_R_in_no_send_MM [MN0 n0 n1 v] :
    KIS MN0 ->
    List.In (MqRecv (n1, R) v) (mserv_i (MN0 n0))  ->
    retract_send (mserv_i (MN0 n0)) = [].

  Proof.
    intros.
    destruct (NetMod.get n0 MN0) as [MQ0 M0 [I0 P0 O0]] eqn:?.
    unfold NetGet in *; hsimpl in *.
    assert (List.In (n1, R, v) (I0 ++ retract_recv MQ0)) by attac.
    assert ((retract_send MQ0 ++ O0) = []) by eauto using M_R_in_no_send with LTS.
    apply app_eq_nil in H2.
    attac.
  Qed.
  Lemma M_R_in_no_send_MP [MN0 n0 n1 v MQ M I P O] :
    KIS MN0 ->
    NetMod.get n0 MN0 = mserv MQ M (serv I P O) ->
    List.In (n1, R, v) (I ++ retract_recv MQ)  ->
    O = [].
  Proof.
    intros.
    destruct (NetMod.get n0 MN0) as [MQ0 M0 [I0 P0 O0]] eqn:?.
    assert (List.In (n1, R, v) (I0 ++ retract_recv MQ0)) by attac.
    assert ((retract_send MQ0 ++ O0) = []) by eauto using M_R_in_no_send with LTS.
    apply app_eq_nil in H3.
    attac.
  Qed.
  Lemma M_R_in_no_send_PM [MN0 n0 n1 v MQ M I P O] :
    KIS MN0 ->
    NetMod.get n0 MN0 = mserv MQ M (serv I P O) ->
    List.In (n1, R, v) (I ++ retract_recv MQ)  ->
    retract_send MQ = [].
  Proof.
    intros.
    destruct (NetMod.get n0 MN0) as [MQ0 M0 [I0 P0 O0]] eqn:?.
    assert (List.In (n1, R, v) (I0 ++ retract_recv MQ0)) by attac.
    assert ((retract_send MQ0 ++ O0) = []) by eauto using M_R_in_no_send with LTS.
    apply app_eq_nil in H3.
    attac.
  Qed.
  Lemma M_R_in_no_send_PP [MN0 n0 n1 v MQ M I P O] :
    KIS MN0 ->
    NetMod.get n0 MN0 = mserv MQ M (serv I P O) ->
    List.In (n1, R, v) (I ++ retract_recv MQ)  ->
    O = [].
  Proof.
    intros.
    destruct (NetMod.get n0 MN0) as [MQ0 M0 [I0 P0 O0]] eqn:?.
    assert (List.In (n1, R, v) (I0 ++ retract_recv MQ0)) by attac.
    assert ((retract_send MQ0 ++ O0) = []) by eauto using M_R_in_no_send with LTS.
    apply app_eq_nil in H3.
    attac.
  Qed.

  #[export] Hint Resolve M_R_in_no_send_MM M_R_in_no_send_MP M_R_in_no_send_PM M_R_in_no_send_PP : LTS.


  Lemma M_wait_add [MN0 MN1 a n0 n1] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    ~ List.In n1 (wait (MN0 n0)) ->
    List.In n1 (wait (MN1 n0)) ->
    exists v, a = NTau n0 (MActP (Recv (n1, Q) v)).

  Proof.
    intros.

    destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; doubt.

    all:
      destruct s; hsimpl in *; simpl in *; doubt.

    - assert (List.In n1 (n2::&wait)) by (blast_cases; attac).
      attac.
    - assert (List.In n1 &wait) by (blast_cases; attac).
      bs.
    - assert (List.In n1 &wait) by (blast_cases; compat_hsimpl in *; attac).
      bs.
    - bs (List.In n1 &wait /\ n1 <> n0) by eauto using in_remove.
    - bs (List.In n1 &wait /\ n1 <> n2) by eauto using in_remove.
  Qed.


  Lemma M_wait_remove [MN0 MN1 a n0 n1] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    List.In n1 (wait (MN0 n0)) ->
    ~ List.In n1 (wait (MN1 n0)) ->
    exists v, a = NComm n0 n1 R v.

  Proof.
    intros.

    destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; doubt.

    all:
      destruct s; hsimpl in *; simpl in *; doubt.

    all: blast_cases; compat_hsimpl in *; eattac.
    - smash_eq n1 n0; compat_hsimpl in *; attac.
      bs (List.In n1 (List.remove NAME.eq_dec n0 &wait)) by eauto using in_in_remove.
    - smash_eq n1 n2; compat_hsimpl in *; attac.
      bs (List.In n1 (List.remove NAME.eq_dec n2 &wait)) by eauto using in_in_remove.
  Qed.


  Lemma M_lock_count_update [MN0 MN1 a n0] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    lock_count (MN0 n0) <> lock_count (MN1 n0) ->
    exists n1 v, a = NComm n0 n1 Q (MValP v).

  Proof.
    intros.

    destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; doubt.

    all:
      destruct s; hsimpl in *; simpl in *; doubt.

    all: blast_cases; compat_hsimpl in *; eattac.
  Qed.


  Lemma M_lock_count_incr [MN0 MN1 a n0] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    lock_count (MN1 n0) = lock_count (MN0 n0) \/ lock_count (MN1 n0) = S (lock_count (MN0 n0)).

  Proof.
    intros.

    destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; doubt.

    all: eattac.

    all: try (smash_eq n n0); try (smash_eq n1 n0); compat_hsimpl in *; doubt.
    all: try (rewrite `(NetMod.get _ _ = _)); simpl in *; auto.
    all: blast_cases; compat_hsimpl in *; eattac.
  Qed.


  Lemma M_lock_count_update_act [MN0 MN1 n0 n1 v] :
    KIS MN0 ->
    (MN0 =(NComm n0 n1 Q (MValP v))=> MN1) ->
    lock_count (MN1 n0) = S (lock_count (MN0 n0)).

  Proof.
    intros.
    consider (_ =(_)=> _).
    compat_hsimpl in *.
    ltac1:(autounfold with LTS_get in * ).
    hsimpl_net; compat_hsimpl in *; attac.
  Qed.


  Lemma M_alarm_set [MN0 MN1 a n0] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    alarm (MN0 n0) = false ->
    alarm (MN1 n0) = true ->
    a = NTau n0 (MActM Tau) /\
      exists n1, List.In (MqProbe (n1, R) {|origin:=n0; lock_id:=lock_count (MN0 n0)|}) (mserv_i (MN0 n0)).

  Proof.
    intros.

    assert (self (MN1 n0) = n0) by eauto using KIS_invariant_self.

    destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; doubt.

    all: try (destruct msg).

    all:
      destruct s; hsimpl in *; simpl in *; doubt.

    all: blast_cases; eattac.

    consider (&lock_count = &lock_id) by (apply PeanoNat.Nat.eqb_eq; auto).
    eauto with LTS.
    compat_hsimpl in *.
    bs.
  Qed.


  Lemma KIS_invariant_locked [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n0 n1, locked (MN1 n0) = Some n1 -> lock '' MN1  n0 n1 \/ exists v, List.In (MqRecv (n1, R) v) (mserv_i (MN1 n0)).

  Proof.
    intros.

    destruct (well_formed_lock_dec '' MN1 n0 n1); eauto using KIS_invariant_well_formed with LTS.
    right.

    destruct (well_formed_lock_dec '' MN0 n0 n1); eauto with LTS.
    - consider (exists v, a = NComm n1 n0 R (MValP v))
        by eauto using SRPC_M_net_unlock_reply with LTS.
      unfold NetGet in *.
      consider (_ =(_)=> _).
      compat_hsimpl in *; eattac.
    - assert (well_formed '' MN0) by eauto with LTS.
      assert (well_formed '' MN1) by eauto with LTS.

      assert ((exists v, List.In (MqRecv (n1, R) v) (mserv_i (MN1 n0)))
                              \/ forall v, ~ List.In (MqRecv (n1, R) v) (mserv_i (MN1 n0))
             ) as [|]; auto.
      {
        generalize (mserv_i (MN1 n0)) as Q0. clear.
        intros.
        induction Q0; attac.
        destruct `(_ \/ _); attac.
        destruct a; attac.
        destruct (NameTag_eq_dec n (n1, R)); attac.
      }
      exfalso.

      destruct (locked (MN0 n0)) as [n1'| ] eqn:?.
      + consider (n1' = n1) by (symmetry; eauto using M_lock_no_reset).
        assert (lock '' MN0 n0 n1 \/ exists v, List.In (MqRecv (n1, R) v) (mserv_i (MN0 n0))) by eauto with LTS.
        hsimpl in *.
        unfold NetGet in *.

        destruct (NetMod.get n0 MN0) as [MQ0 M0 [I0 P0 O0]] eqn:?.
        destruct (NetMod.get n0 MN1) as [MQ1 M1 [I1 P1 O1]] eqn:?.

        destruct_mna a; hsimpl in *.

        all: smash_eq n n0; compat_hsimpl in *.

        par: doubt.

        all: compat_hsimpl in *; unfold NetGet in *.
        * bs (~ In (MqRecv (n1, R) v) (_ ++ [MqSend _ _])) by eauto.
        * bs (~ In (MqRecv (n1, R) v) (_ ++ [MqSend _ _])) by eauto.
        * bs.
        * destruct `(_ \/ _); hsimpl in *; doubt.
          ltac1:(autounfold with LTS_get in * ).
          hsimpl in *.
          simpl in H1.
          destruct s.
          hsimpl in *; bs.
        * bs.
        * assert (~ In (MqRecv (n1, R) v) MQ1) by eauto.
          consider (MN0 =(_)=> _); compat_hsimpl in *.
          hsimpl_net; bs.
        * assert (~ In (MqRecv (n1, R) v) MQ1) by eauto.
          consider (MN0 =(_)=> _); compat_hsimpl in *.
          hsimpl_net; bs.
        * assert (~ In (MqRecv (n1, R) v) MQ1) by eauto.
          consider (MN0 =(_)=> _); compat_hsimpl in *.
          hsimpl_net; bs.
        * assert (~ In (MqRecv (n1, R) v) MQ1) by eauto.
          consider (MN0 =(_)=> _); compat_hsimpl in *.
          hsimpl_net; bs.
        * assert (~ In (MqRecv (n1, R) v) MQ1) by eauto.
          consider (MN0 =(_)=> _); compat_hsimpl in *.
          hsimpl_net; bs.
        * assert (~ In (MqRecv (n1, R) v) MQ1) by eauto.
          consider (MN0 =(_)=> _); compat_hsimpl in *.
          hsimpl_net; bs.
        * assert (~ In (MqRecv (n1, R) v) MQ1) by eauto.
          consider (MN0 =(_)=> _); compat_hsimpl in *.
          hsimpl_net; bs.
        * assert (~ In (MqRecv (n1, R) v) MQ1) by eauto.
          consider (MN0 =(_)=> _); compat_hsimpl in *.
          hsimpl_net; bs.

      + enough (exists v, a = NComm n0 n1 Q (MValP v))
          by (compat_hsimpl in *; consider (~ lock '' MN0 n0 n1 /\ lock '' MN1 n0 n1) by eauto using SRPC_M_net_query_new_lock).

        eauto using M_lock_set.
  Qed.


  Lemma KIS_invariant_wait [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n0 n1, List.In n0 (wait (MN1 n1)) -> lock '' MN1 n0 n1.

  Proof.
    intros.
    destruct (well_formed_lock_dec '' MN1 n0 n1); eauto with LTS.
    exfalso.

    destruct (in_dec NAME.eq_dec n0 (wait (MN0 n1))).
    - assert (lock '' MN0 n0 n1) by eauto with LTS.
      consider (exists v, a = NComm n1 n0 R (MValP v)) by eauto using SRPC_M_net_unlock_reply with LTS.

      consider (_ =(_)=> _).
      compat_hsimpl in *.
      ltac1:(autounfold with LTS_get in * ).
      destruct s.
      hsimpl_net.
      + bs (~ List.In n0 (List.remove NAME.eq_dec n0 &wait)) by eauto using remove_In.
      + bs (~ List.In n0 (List.remove NAME.eq_dec n0 &wait)) by eauto using remove_In.

    - rename n into Hn.
      assert (exists v, a = NTau n1 (MActP (Recv (n0, Q) v))) by eauto using M_wait_add with LTS.

      enough (lock '' MN0 n0 n1).
      {
        consider (exists v, a = NComm n1 n0 R (MValP v)) by eauto using SRPC_M_net_unlock_reply with LTS.
        bs.
      }

      destruct (NetMod.get n1 '' MN0) as [I0' P0' O0'] eqn:?.
      destruct (NetMod.get n1 MN0) as [MQ0 M0 [I0 P0 O0]] eqn:?.

      enough (serv_client n0 (NetMod.get n1 '' MN0)) by eauto with LTS.
      enough (exists v, List.In (n0, Q, v) I0') by iattac.
      enough (exists v, List.In (MqRecv (n0, Q) v) MQ0)
        by (compat_hsimpl in *; exists v0; unfold deinstr, serv_deinstr in *; ieattac).
      compat_hsimpl in *; eattac.
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

    destruct (NetMod.get n0 MN0) as [MQ0 s0 S0] eqn:?.
    destruct (NetMod.get n0 MN1) as [MQ1 s1 S1] eqn:?.

    destruct_mna a; compat_hsimpl in *.

    all: ltac1:(autounfold with LTS_get in * ); hsimpl_net; blast_cases; eattac.

    - consider (MN0 =(_)=> _); hsimpl in *.
      hsimpl_net; doubt.
    - consider (MN0 =(_)=> _); compat_hsimpl in *.
      hsimpl_net; doubt.
    - consider (MN0 =(_)=> _); compat_hsimpl in *.
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
    - consider (MN0 =(_)=> _); compat_hsimpl in *.
      hsimpl_net; compat_hsimpl in *; doubt.
  Qed.


  Lemma KIS_invariant_sendp [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n0 n1 p, sends_to MN1 n1 n0 p -> lock '' MN1 n0 n1.

  Proof.
    intros.

    destruct (NetMod.get n1 MN0) as [MQ0 s0 S0] eqn:?.
    destruct (NetMod.get n1 MN1) as [MQ1 s1 S1] eqn:?.

    destruct (well_formed_lock_dec '' MN1 n0 n1); eauto with LTS.

    destruct (sends_to_dec MN0 n1 n0 p).
    - assert (lock '' MN0 n0 n1) by eauto with LTS.

      consider (exists v, a = NComm n1 n0 R (MValP v)) by eauto using SRPC_M_net_unlock_reply with LTS.

      consider (_ =(_)=> _); compat_hsimpl in *.
      ltac1:(autounfold with LTS_get in * ); attac.

    - assert ((exists v, a = NTau n1 (MActP (Recv (n0, Q) v))) \/ a = NTau n1 (MActM Tau)) as [|]
          by eauto using M_sends_to_send_set with LTS.
      + hsimpl in *.
        enough (lock '' MN0 n0 n1).
        {
          consider (exists v', NTau n1 (MActP (Recv (n0, Q) v)) = NComm n1 n0 R (MValP v')) by (eapply SRPC_M_net_unlock_reply; attac; constructor; attac).
          bs.
        }

        enough (serv_client n0 (NetMod.get n1 '' MN0)) by eauto with LTS.
          enough (List.In (MqRecv (n0, Q) v) (mserv_i (MN0 n1)))
          by (ltac1:(autounfold with LTS_get in * ); unfold deinstr, serv_deinstr in *; attac).
        ltac1:(autounfold with LTS_get in * ); compat_hsimpl in *.
        blast_cases; attac.
      + enough (List.In n0 (wait (MN1 n1))) by eauto using KIS_invariant_wait.
        consider (MN0 =(_)=> _).
        compat_hsimpl in *.

        blast_cases; attac.
        par: unfold sends_to in *; ltac1:(autounfold with LTS_get in * ); compat_hsimpl in *; try (rewrite next_state_Send_all in * ); attac.
  Qed.


  Lemma KIS_invariant_lock_id_sendp [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n0 n1 p, sends_to MN1 n0 n1 p -> (lock_id p <= lock_count (MN1 (origin p)))%nat.

  Proof.
    intros.

    destruct (NetMod.get n0 MN0) as [MQ0 s0 S0] eqn:?.
    destruct (NetMod.get n0 MN1) as [MQ1 s1 S1] eqn:?.

    destruct (sends_to_dec MN0 n0 n1 p).
    - assert ((lock_id p <= lock_count (MN0 (origin p)))%nat) by eauto with LTS.
      unfold sends_to in *.

      destruct p.

      destruct (NetMod.get &origin MN0) as [MQp0 sp0 Sp0] eqn:?.
      destruct (NetMod.get &origin MN1) as [MQp1 sp1 Sp1] eqn:?.

      destruct_mna a;
        consider (MN0 =(_)=> _);
        ltac1:(autounfold with LTS_get in * );
        hsimpl in *; hsimpl_net; compat_hsimpl in *; doubt.

      par: simpl in *; blast_cases; compat_hsimpl in *; ieattac.

    - destruct (NetMod.get (origin p) MN0) as [MQp0 sp0 Sp0] eqn:?.
      destruct (NetMod.get (origin p) MN1) as [MQp1 sp1 Sp1] eqn:?.

      assert ((exists v, a = NTau n0 (MActP (Recv (n1, Q) v))) \/ a = NTau n0 (MActM Tau)) as [|]
          by eauto using M_sends_to_send_set with LTS.
      + hsimpl in *.
        ltac1:(autounfold with LTS_get in * ).
        hsimpl_net; compat_hsimpl in *.
        all: blast_cases; compat_hsimpl in *; attac.

        consider (&self = n0) by eauto with LTS.
        bs.

      + hsimpl in *.

        unfold sends_to in *; ltac1:(autounfold with LTS_get in * ); hsimpl in *; doubt.
        all: blast_cases; compat_hsimpl in *; attac.


        hsimpl_net; compat_hsimpl in *.
        * enough (lock_id p <= lock_count (MN0 (origin p)))
            by (ltac1:(autounfold with LTS_get in * ); hsimpl in *; eattac).
          enough (List.In (MqProbe (n1, R) p) (mserv_i (MN0 (origin p)))) by eauto with LTS.

          absurd (&self = origin p); auto.
          enough (self (MN0 (origin p)) = (origin p)) by (ltac1:(autounfold with LTS_get in * ); attac).
          eauto with LTS.
        * enough (lock_id p <= lock_count (MN0 (origin p)))
            by (ltac1:(autounfold with LTS_get in * ); hsimpl in *; eattac).
          eenough (List.In (MqProbe (_, R) p) (mserv_i (MN0 n0))) by eauto with LTS.

          ltac1:(autounfold with LTS_get in * ).
          rewrite Heqm.
          enough (&self = n0) by (ltac1:(autounfold with LTS_get in * ); compat_hsimpl in *; ieattac).

          enough (self (MN0 n0) = n0) by (ltac1:(autounfold with LTS_get in * ); attac).
          eauto with LTS.
  Qed.


  Lemma M_recv_ev_act [MN0 MN1 a n0 n1 t p] :
    KIS MN0 ->
    (MN0 =(a)=> MN1) ->
    ~ List.In (MqProbe (n1, t) p) (mserv_i (MN0 n0)) ->
    List.In (MqProbe (n1, t) p) (mserv_i (MN1 n0)) ->
    a = NComm n1 n0 t ^ p.

  Proof.
    intros.

    destruct (NetMod.get n0 MN0) as [MQ0 s0 S0] eqn:?.

    destruct_mna a;
      Control.enter (fun _ => consider (_ =(_)=> _));
      ltac1:(autounfold with LTS_get in * );
      compat_hsimpl in *; hsimpl_net; hsimpl in *; doubt.

    all: auto.
  Qed.


  Lemma KIS_invariant_lock_id_recvp [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n0 n1 p, List.In (MqProbe (n1, R) p) (mserv_i (MN1 n0)) ->
                                      (lock_id p <= lock_count (MN1 (origin p)))%nat.

  Proof.
    intros.

    assert (In (MqProbe (n1, R) p) (mserv_i (MN0 n0)) \/ ~ In (MqProbe (n1, R) p) (mserv_i (MN0 n0))) as [|].
    - induction (mserv_i (MN0 n0)); attac.
      destruct `(_ \/ _); attac.
      destruct a0; attac.
      destruct n.
      destruct (MProbe_eq_dec p m); attac.
      destruct t; attac.
      smash_eq n n1; attac.
    - assert (lock_id p <= lock_count (MN0 (origin p))) by eauto with LTS.
      destruct (PeanoNat.Nat.eq_dec (lock_count (MN1 (origin p))) (lock_count (MN0 (origin p)))).
      1: attac.

      consider (exists n1' v, a = NComm (origin p) n1' Q (MValP v)) by eauto using M_lock_count_update.

      consider (locked (MN0 (origin p)) = None /\ locked (MN1 (origin p)) = Some n1') by eauto using M_lock_set_act.
      consider (_ =(_)=> _); compat_hsimpl in *.
      ltac1:(autounfold with LTS_get in * ); hsimpl in *.
      hsimpl_net; hsimpl in *; doubt.
      all: blast_cases; attac.
    - assert (a = NComm n1 n0 R ^ p) by eauto using  M_recv_ev_act.
      destruct (PeanoNat.Nat.eq_dec (lock_count (MN1 (origin p))) (lock_count (MN0 (origin p)))).
      2: consider (exists n1' v, a = NComm (origin p) n1' Q (MValP v)) by (eauto using M_lock_count_update; hsimpl in * ); bs.
      enough (sends_to MN0 n1 n0 p) by (rewrite `(lock_count (MN1 _) = _) in *; eauto with LTS).

      subst.
      consider (_ =(_)=> _); compat_hsimpl in *.
      unfold sends_to in *; ltac1:(autounfold with LTS_get in * ); hsimpl in *.
      attac.
  Qed.


  Lemma dep_dec_after : forall N0 N1 a n0 n1,
      well_formed N0 ->
      trans_lock N0 n0 n1 ->
      (N0 =(a)=> N1) ->
      trans_lock N1 n0 n1 \/ ~ trans_lock N1 n0 n1.

  Proof.
    intros.
    apply dep_lock_chain in H0 as [L [? ?]].
    generalize dependent n0.
    induction L; intros; hsimpl in *.
    - destruct (well_formed_lock_dec N1 n0 n1); eauto with LTS.
      right; intros ?.
      consider (trans_lock N1 n0 _).
      consider (n1 = n2) by eauto using SRPC_net_no_relock with LTS.
    - specialize (IHL ltac:(auto) a0 ltac:(auto)) as [|].
      + destruct (well_formed_lock_dec N1 n0 a0); eauto with LTS.
        right; intros ?.
        consider (trans_lock N1 _ _).
        * consider (a0 = n1) by eauto using SRPC_net_no_relock with LTS.
        * consider (a0 = n2) by eauto using SRPC_net_no_relock with LTS.
      + right; intros ?.
        consider (trans_lock N1 n0 n1).
        * consider (a0 = n1) by eauto using SRPC_net_no_relock with LTS.
        * consider (a0 = n2) by eauto using SRPC_net_no_relock with LTS.
  Qed.

  Lemma dep_dec_after_M : forall MN0 MN1 ma n0 n1,
      well_formed '' MN0 ->
      trans_lock '' MN0 n0 n1 ->
      (MN0 =(ma)=> MN1) ->
      trans_lock '' MN1 n0 n1 \/ ~ trans_lock '' MN1 n0 n1.

  Proof.
    intros.
    destruct (MNAct_to_PNAct ma) as [a|] eqn:?.
    - assert ('' MN0 =(a)=> '' MN1) by eauto using deinstr_act_do with LTS.
      now eauto using dep_dec_after.
    - replace ('' MN1) with ('' MN0) by eauto using deinstr_act_skip with LTS.
      now left.
  Qed.


  Lemma KIS_invariant_recvp_active [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n0 n1 n2, List.In (active_ev_of MN1 n1 n2) (mserv_i (MN1 n0)) ->
                                  locked (MN1 n2) <> None ->
                                  trans_lock '' MN1 n0 n2.

  Proof.
    intros.

    destruct (NetMod.get n0 MN0) as [MQ00 s00 S00] eqn:?.
    destruct (NetMod.get n0 MN1) as [MQ01 s01 S01] eqn:?.

    destruct (NetMod.get n1 MN0) as [MQ10 s10 S10] eqn:?.
    destruct (NetMod.get n1 MN1) as [MQ11 s11 S11] eqn:?.

    destruct (NetMod.get n2 MN0) as [MQ20 s20 S20] eqn:?.
    destruct (NetMod.get n2 MN1) as [MQ21 s21 S21] eqn:?.

    assert (In (active_ev_of MN1 n1 n2) (mserv_i (MN0 n0)) \/ ~ In (active_ev_of MN1 n1 n2) (mserv_i (MN0 n0))) as [|].
    {
      unfold active_ev_of. clear.
      induction (mserv_i (MN0 n0)); attac.
      destruct `(_ \/ _); attac.
      destruct a; attac.
      destruct n.
      destruct (MProbe_eq_dec (active_probe_of MN1 n2) m); attac.
      destruct t; attac.
      smash_eq n n1; attac.
    }
    2: {
      unfold active_ev_of in *.
      consider (a = NComm n1 n0 R ^ (active_probe_of MN1 n2)) by eauto using M_recv_ev_act.
      assert (sends_to MN0 n1 n0 (active_probe_of MN1 n2)).
      {
        remember (active_probe_of MN1 n2) as p; clear - H.
        consider (_ =(_)=> _); compat_hsimpl in *.
        unfold sends_to; ltac1:(autounfold with LTS_get in * ); attac.
      }
      consider (lock '' MN0 n0 n1 /\ lock '' MN1 n0 n1).
      {
        assert (lock '' MN0 n0 n1) by eauto with LTS.
        split; auto.
        destruct (well_formed_lock_dec '' MN1 n0 n1); eauto with LTS.
        consider (exists v, NComm n1 n0 R ^ (active_probe_of MN1 n2) = NComm n1 n0 R (MValP v)) by eauto using SRPC_M_net_unlock_reply with LTS.
        bs.
      }
      assert (locked (MN0 n2) <> None).
      {
        intros ?.
        destruct (locked (MN1 n2)) as [n3|] eqn:?; doubt.
        consider (exists v, NComm n1 n0 R ^ (active_probe_of MN1 n2) = NComm n2 n3 Q (MValP v)) by eauto using M_lock_set.
      }
      assert (active_probe_of MN1 n2 = active_probe_of MN0 n2).
      {
        enough (lock_count (MN1 n2) = lock_count (MN0 n2)) by (unfold active_probe_of; attac).
        destruct (PeanoNat.Nat.eq_dec (lock_count (MN1 n2)) (lock_count (MN0 n2))); auto.
        consider (exists n3' v, NComm n1 n0 R ^ (active_probe_of MN1 n2) = NComm n2 n3' Q (MValP v)) by eauto using M_lock_count_update.
        bs.
      }
      rewrite `(active_probe_of _ _ = _) in *.

      assert (trans_lock '' MN0 n0 n2) by eauto with LTS.

      enough ('' MN0 = '' MN1) by attac.
      eapply deinstr_act_skip; attac.
    }

    destruct (locked (MN1 n2)) as [n3|] eqn:?. 2: doubt.

    assert ((exists v, a = NComm n2 n3 Q (MValP v)) \/ forall v, a <> NComm n2 n3 Q (MValP v)) as [|].
    {
      clear.
      destruct_mna a; try (solve [left; eexists; eattac | right; eattac ]).
      smash_eq n n0 n2 n3; try (solve [left; eexists; eattac | right; eattac ]).
    }
    - assert (lock_count (MN0 n2) < lock_count (MN1 n2)).
      {
        hsimpl in *.
        assert (lock_count (MN1 n2) = S (lock_count (MN0 n2))) by eauto using M_lock_count_update_act.
        lia.
      }

      enough (lock_count (MN1 n2) <= lock_count (MN0 n2)) by lia.
      enough (lock_id (active_probe_of MN1 n2) <= lock_count (MN0 (origin (active_probe_of MN1 n2)))) by (simpl in *; lia).
      eauto with LTS.

    - assert (lock_count (MN0 n2) = lock_count (MN1 n2)).
      {
        destruct (PeanoNat.Nat.eq_dec (lock_count (MN0 n2)) (lock_count (MN1 n2))) as [He|He]; auto.
        consider (exists n3' v, a = NComm n2 n3' Q (MValP v)) by eauto using M_lock_count_update.
        consider (locked (MN0 n2) = None /\ locked (MN1 n2) = Some n3') by eauto using M_lock_set_act.
        attac.
      }
      replace (active_ev_of MN1 n1 n2) with (active_ev_of MN0 n1 n2) by (unfold active_ev_of, active_probe_of; attac).
      assert (locked (MN0 n2) = Some n3).
      {
        destruct (locked (MN0 n2)) as [n3'|] eqn:?.
        - enough (n3 = n3') by attac.
          eauto using M_lock_no_reset.
        - consider (exists v, a = NComm n2 n3 Q (MValP v)) by eauto using M_lock_set.
          bs.
      }
      assert (trans_lock '' MN0 n0 n2) by (assert (locked (MN0 n2) <> None) by attac; eauto with LTS).
      assert (trans_lock '' MN1 n0 n2 \/ ~ trans_lock '' MN1 n0 n2) as [|]; eauto using dep_dec_after_M with LTS.

      consider (exists n0' v, (n0 = n0' \/ trans_lock '' MN1 n0 n0') /\ a = NComm n2 n0' R (MValP v)).
      {
        destruct (MNAct_to_PNAct a) eqn:?.
        - assert ('' MN0 =(p)=> '' MN1) by eauto using deinstr_act_do with LTS.
          consider (exists n0' v, p = NComm n2 n0' R v /\ (n0' = n0 \/ trans_lock '' MN1 n0 n0')).
          {
            eapply net_trans_lock_unlock with (n0:=n0)(n1:=n2)(N1:=''MN1)(N0:=''MN0); eauto with LTS.
          }

          exists n0', v.
          split.
          1: { destruct `(_ \/ _); eauto using eq_sym. }
          destruct_mna a; doubt.
          attac.
        - replace ('' MN1) with ('' MN0) by eauto using deinstr_act_skip with LTS.
          bs.
      }

      bs (n2 <> n2) by eauto using M_lock_no_send.
  Qed.


  Lemma KIS_invariant_sendp_active [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    (forall n0 n1 n2, sends_to MN1 n1 n0 (active_probe_of MN1 n2) -> locked (MN1 n2) <> None -> trans_lock '' MN1 n0 n2).

  Proof.
    intros.

    destruct (NetMod.get n0 MN0) as [MQ00 s00 S00] eqn:?.
    destruct (NetMod.get n0 MN1) as [MQ01 s01 S01] eqn:?.

    destruct (NetMod.get n1 MN0) as [MQ10 s10 S10] eqn:?.
    destruct (NetMod.get n1 MN1) as [MQ11 s11 S11] eqn:?.

    destruct (NetMod.get n2 MN0) as [MQ20 s20 S20] eqn:?.
    destruct (NetMod.get n2 MN1) as [MQ21 s21 S21] eqn:?.

    assert (lock '' MN1 n0 n1) by eauto using KIS_invariant_sendp.

    destruct (sends_to_dec MN0 n1 n0 (active_probe_of MN1 n2)) as [|].
    2: {
      assert ((exists v, a = NTau n1 (MActP (Recv (n0, Q) v))) \/ a = NTau n1 (MActM Tau))
        by eauto using M_sends_to_send_set with LTS.

      assert (locked (MN0 n2) <> None).
      {
        intros ?.
        destruct (locked (MN1 n2)) as [n3|] eqn:?; doubt.
        consider (exists v, a = NComm n2 n3 Q (MValP v)) by eauto using M_lock_set.
        destruct `(_ \/ _); bs.
      }
      assert (active_probe_of MN1 n2 = active_probe_of MN0 n2).
      {
        enough (lock_count (MN1 n2) = lock_count (MN0 n2)) by (unfold active_probe_of; attac).
        destruct (PeanoNat.Nat.eq_dec (lock_count (MN1 n2)) (lock_count (MN0 n2))); auto.
        consider (exists n3' v, a = NComm n2 n3' Q (MValP v)) by eauto using M_lock_count_update.
        destruct `(_ \/ _); bs.
      }
      rewrite `(active_probe_of _ _ = _) in *.

      assert (lock '' MN0 n0 n1).
      {
        destruct (well_formed_lock_dec '' MN0 n0 n1); auto with LTS.
        consider (exists v, a = NComm n0 n1 Q (MValP v)) by eauto using SRPC_M_net_new_lock_query with LTS.
        destruct `(_ \/ _); bs.
      }

      destruct `(_ \/ _).
      - hsimpl in *.
        enough (n2 = n1) by attac 2.
        consider (_ =(_)=> _); compat_hsimpl in * |-.
        assert (self (MN0 n1) = n1) by eauto with LTS.
        unfold active_ev_of, active_probe_of in *; ltac1:(autounfold with LTS_get in * ).
        destruct s.
        destruct &locked.
        consider (sends_to_mon _ _ _); attac 2.
        consider (sends_to_mon _ _ _).
        bs.
      - assert (trans_lock '' MN0 n0 n2).
        {
          enough (trans_lock '' MN0 n1 n2) by attac.
          enough (exists n', List.In (active_ev_of MN0 n' n2) (mserv_i (MN0 n1))) by (hsimpl in *; eauto with LTS).
          unfold active_ev_of, active_probe_of, sends_to in *.
          ltac1:(autounfold with LTS_get in * ); hsimpl in *.
          consider (_ =(_)=> _); compat_hsimpl in *.
          blast_cases; compat_hsimpl in *; attac.
        }

        assert (trans_lock '' MN1 n0 n2 \/ ~ trans_lock '' MN1 n0 n2) as [|] by eauto using dep_dec_after_M with LTS; auto.

        assert (exists m0 m1 v, (n0 = m0 \/ trans_lock '' MN0 n0 m0) /\ NTau n1 (MActM Tau) = NComm m1 m0 R (MValP v)).
        {
          subst.
          destruct (MNAct_to_PNAct (NTau n1 (MActM Tau))) eqn:?.
          - assert ('' MN0 =(p)=> '' MN1) by eauto using deinstr_act_do with LTS.
            consider (exists n0' v, p = NComm n2 n0' R v /\ (n0' = n0 \/ trans_lock '' MN1 n0 n0')).
            {
              eapply net_trans_lock_unlock with (n0:=n0)(n1:=n2)(N1:=''MN1)(N0:=''MN0); eauto with LTS.
            }
            bs.
          - replace ('' MN1) with ('' MN0) by eauto using eq_sym, deinstr_act_skip.
            bs.
        }
        hsimpl in *; bs.
    }

    destruct (locked (MN1 n2)) as [n3|] eqn:?. 2: doubt.

    assert ((exists v, a = NComm n2 n3 Q (MValP v)) \/ forall v, a <> NComm n2 n3 Q (MValP v)) as [|].
    {
      clear.
      destruct_mna a; try (solve [left; eexists; eattac | right; eattac ]).
      smash_eq n n0 n2 n3; try (solve [left; eexists; eattac | right; eattac ]).
    }
    - assert (lock_count (MN0 n2) < lock_count (MN1 n2)).
      {
        hsimpl in *.
        assert (lock_count (MN1 n2) = S (lock_count (MN0 n2))) by eauto using M_lock_count_update_act.
        lia.
      }

      enough (lock_count (MN1 n2) <= lock_count (MN0 n2)) by lia.
      enough (lock_id (active_probe_of MN1 n2) <= lock_count (MN0 (origin (active_probe_of MN1 n2)))) by (simpl in *; lia).
      eauto with LTS.
    - assert (lock_count (MN0 n2) = lock_count (MN1 n2)).
      {
        destruct (PeanoNat.Nat.eq_dec (lock_count (MN0 n2)) (lock_count (MN1 n2))) as [He|He]; auto.
        consider (exists n3' v, a = NComm n2 n3' Q (MValP v)) by eauto using M_lock_count_update.
        consider (locked (MN0 n2) = None /\ locked (MN1 n2) = Some n3') by eauto using M_lock_set_act.
        attac.
      }
      replace (active_probe_of MN1 n2) with (active_probe_of MN0 n2) by (unfold active_probe_of; attac).
      assert (locked (MN0 n2) = Some n3).
      {
        destruct (locked (MN0 n2)) as [n3'|] eqn:?.
        - enough (n3 = n3') by attac.
          eauto using M_lock_no_reset.
        - consider (exists v, a = NComm n2 n3 Q (MValP v)) by eauto using M_lock_set.
          bs.
      }
      assert (trans_lock '' MN0 n0 n2) by (assert (locked (MN0 n2) <> None) by attac; eauto with LTS).

      assert (trans_lock '' MN1 n0 n2 \/ ~ trans_lock '' MN1 n0 n2) as [|] by eauto using dep_dec_after_M with LTS; auto.

      consider (exists n0' v, (n0 = n0' \/ trans_lock '' MN1 n0 n0') /\ a = NComm n2 n0' R (MValP v)).
      {
        destruct (MNAct_to_PNAct a) eqn:?.
        - assert ('' MN0 =(p)=> '' MN1) by eauto using deinstr_act_do with LTS.
          consider (exists n0' v, p = NComm n2 n0' R v /\ (n0' = n0 \/ trans_lock '' MN1 n0 n0')).
          {
            eapply net_trans_lock_unlock with (n0:=n0)(n1:=n2)(N1:=''MN1)(N0:=''MN0); eauto with LTS.
          }

          exists n0', v.
          split.
          1: { destruct `(_ \/ _); eauto using eq_sym. }
            destruct_mna a; doubt.
          attac.
        - replace ('' MN1) with ('' MN0) by eauto using deinstr_act_skip with LTS.
          bs.
      }

      bs (n2 <> n2) by eauto using M_lock_no_send.
  Qed.


  Lemma KIS_invariant_alarm [MN0 MN1 a] :
    (MN0 =(a)=> MN1) ->
    KIS MN0 ->
    forall n, alarm (MN1 n) = true -> trans_lock '' MN1 n n.

  Proof.
    intros.
    destruct (NetMod.get n MN0) as [MQ s S] eqn:?.

    enough (trans_lock '' MN0 n n).
    {
      assert (deadlocked n '' MN0) by (eauto using dep_self_deadlocked with LTS).
      eauto 3 using deadlocked_M_dep_invariant1 with LTS.
    }

    destruct (alarm (MN0 n)) eqn:?; eauto 2 with LTS.

    consider (a = NTau n (MActM Tau) /\
                exists n1, List.In (MqProbe (n1, R) {|origin:=n; lock_id:=lock_count (MN0 n)|}) (mserv_i (MN0 n))) by eauto using M_alarm_set.

    assert (List.In (active_ev_of MN0 n1 n) (mserv_i (MN0 n))) by eauto with LTS.

    enough (locked (MN0 n) <> None) by eauto with LTS.

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
        KIS_invariant_well_formed
      , KIS_invariant_self
      , KIS_invariant_locked
      , KIS_invariant_wait
      , KIS_invariant_sendp
      , KIS_invariant_lock_id_sendp
      , KIS_invariant_lock_id_recvp
      , KIS_invariant_recvp_active
      , KIS_invariant_sendp_active
      , KIS_invariant_alarm.
  Qed.

  Hint Resolve KIS_invariant : LTS inv.
  Hint Extern 0 (KIS _) => solve_invariant : LTS.


  Lemma KIS_detection [MN n] :
    KIS MN ->
    alarm (MN n) = true ->
    exists DS, dead_set DS '' MN /\ In n DS.

  Proof.
    intros.
    enough (deadlocked n MN) by (consider (deadlocked _ _); attac).
    enough (trans_lock '' MN n n) by eauto using dep_self_deadlocked with LTS.
    consider (KIS MN).
  Qed.


  Theorem detection_soundness : forall (i0 : instr) N0 MN1 mpath n,
    KIS (i0 N0) ->
    (i0 N0 =[mpath]=> MN1) ->
    alarm (MN1 n) = true ->
    exists DS, dead_set DS '' MN1 /\ In n DS.

  Proof.
    intros.
    eauto using KIS_detection with LTS.
  Qed.


  Lemma MNPath_do : forall mpath (MN0 MN1 : MNet),
      (MN0 =[mpath]=> MN1) ->
      (deinstr MN0 =[mpath]=> deinstr MN1).

  Proof.
    induction mpath; intros.
    1: attac.
    hsimpl in *.
    destruct (MNAct_to_PNAct a) eqn:?.
    - apply path_seq1 with (middle:=''N1).
      2: eauto.
      destruct a; kill Heqo; blast_cases; doubt; compat_hsimpl in |- *.
      + assert ('' MN0 =(p)=> '' N1). eapply deinstr_act_do. 2: eauto. simpl in *. eauto.
        attac.
        {
          constructor. eauto with LTS.
          unfold deinstr in *.
          rewrite NetMod.put_map in *.
          constructor.
          rewrite NetMod.get_map in *.
          compat_hsimpl in *.
          subst.
          rewrite H.
          attac.
          kill H2.
          kill H3.
          econstructor 2; eattac.
          econstructor 3; eattac.
          eapply STTau.
          eauto.
        }

      + assert ('' MN0 =(p)=> '' N1). eapply deinstr_act_do. 2: eauto. simpl in *. eauto.
        attac.
        kill H2.
        kill H1.
        kill H3.
        unfold deinstr in *.
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
    - replace ('' MN0) with ('' N1) by eauto using deinstr_act_skip, eq_sym.
      eapply path_seq1 with (middle:=N1).
      2: eauto.
      destruct a; kill Heqo; blast_cases; doubt; hsimpl in |- *.
      + eapply NTrans_Tau_inv.
        kill H; hsimpl in *.
        unfold deinstr.
        rewrite NetMod.put_map in *.
        hsimpl.
        eexists; eattac.
      + eapply NTrans_Tau_inv.
        kill H; hsimpl in *.
        unfold deinstr.
        rewrite NetMod.put_map in *.
        hsimpl.
        eexists; eattac.
      + eapply NTrans_Tau_inv.
        kill H; hsimpl in *.
        unfold deinstr.
        rewrite NetMod.put_map in *.
        hsimpl.
        eexists; eattac.
      + eapply NTrans_Tau_inv.
        kill H; hsimpl in *.
        unfold deinstr.
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


  Corollary detection_soundness_instr : forall N0 (i0 : instr) MN1 mpath0 n,
    KIS (i0 N0) ->
    (i0 N0 =[ mpath0 ]=> MN1) ->
    alarm (MN1 n) = true ->
    exists mpath1 (i1 : instr) N1 DS,
      (MN1 =[mpath1]=> i1 N1)
      /\ (N0 =[ mpath0 ++ mpath1 ]=> N1)
      /\ In n DS
      /\ dead_set DS N1.

  Proof.
    intros.

    consider (exists mpath1 path (i2 : instr) N2, (MN1 =[ mpath1 ]=> i2 N2) /\ (N0 =[ path ]=> N2)) by eauto using transp_sound_instr.
    assert ('' (i0 N0) =[mpath0 ++ mpath1]=> '' (i2 N2)) by eauto using MNPath_do with LTS.

    hsimpl in *.

    consider (exists DS, dead_set DS '' MN1 /\ In n DS) by eauto using detection_soundness.

    assert (dead_set DS '' (i2 N2)).
    {
      consider (exists ppath, '' MN1 =[ppath]=> '' (i2 N2)) by eauto using transp_sound.
      attac.
    }

    exists mpath1, i2, N2, DS.
    eattac.
  Qed.
End SOUND_F.

Module Type SOUND(Conf : DETECT_CONF) := Conf <+ DETECT_PARAMS(Conf) <+ SOUND_F.
