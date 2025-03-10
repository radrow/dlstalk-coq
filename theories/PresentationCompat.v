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

Module DetConf <: Compl.DETECT_CONF.
  Parameter Val : Set.

  Declare Module NAME : UsualDecidableSet.
  Module TAG := Locks.Tag_.

  Declare Module NetMod : Network.NET_MOD(NAME).

  Definition Msg := @Compl.MProbe' NAME.t'.
  Definition MState := @Compl.MState' NAME.t'.
End DetConf.

Module Import Theory := ModelData.Empty <+ Sound.SOUND(DetConf).
Import SrpcDefs.

Module Paper.
  Definition serv_lock (n : Name) (S : Serv) :=
    (forall v E, ~ Deq (n, R) v (serv_i S) E) /\ (exists c, SRPC (Lock c n) (serv_p S)) /\ (serv_o S = []).

  Definition dead_set (DS : list Name) N :=
    DS <> []  /\  (forall n0, In n0 DS -> exists n1, net_lock_on N n0 n1 /\ In n1 DS).
End Paper.


Fact serv_lock_eq : forall S n, AnySRPC_serv S -> pq_lock [n] S <-> Paper.serv_lock n S.
Proof.
  split; intros.
  - consider (pq_lock _ _).
    repeat split; repeat (intros ?); simpl in *.
    + bs (In (n, R, v) &I).
    + eauto using lock_SRPC_Lock with LTS.
  - destruct S.
    consider (Paper.serv_lock _ _).
    hsimpl in *.
    repeat split; repeat (intros ?); simpl in *; eauto with LTS.
    assert (exists v' E, Deq (n0, R) v' serv_i0 E) by eauto using In_Deq.
    hsimpl in *.
    bs.
Qed.


Fact deadset_eq : forall N DS, SRPC_net N -> DeadSet DS N <-> Paper.dead_set DS N.

Proof.
  unfold Paper.dead_set.
  split; intros; repeat constructor; intros.
  - attac.
  - consider (DeadSet _ _).
    consider (exists L, net_lock N L n0 /\ incl L DS).
    unfold net_lock, net_lock_on in *.
    consider (exists n1, pq_lock [n1] (NetMod.get n0 N)) by eauto with LTS.
    exists n1.
    eattac.
  - attac.
  - hsimpl in *.
    consider (exists n1, net_lock_on N n n1 /\ _) by eauto.
    exists [n1].
    unfold incl, net_lock_on in *.
    attac.
Qed.
