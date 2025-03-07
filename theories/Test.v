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

Module DetConf <: Compl.DETECT_CONF.
  Parameter Val : Set.

  Declare Module NAME : UsualDecidableSet.
  Module TAG := Locks.Tag_.

  Declare Module NetMod : Network.NET_MOD(NAME).

  Definition Msg := @Compl.MProbe' NAME.t'.
  Definition MState := @Compl.MState' NAME.t'.
End DetConf.

Module Import Sound := ModelData.Empty <+ Sound.SOUND(DetConf). (* TODO fix separation: this includes Compl *)


Inductive ifun : Set := mk_instr (a : mon_assg) :> ifun. (* wtf is this `:>` *)

Parameter xd :> Funclass.

Definition apply_ifun (i : ifun) :=
  match i with mk_instr a => net_instr a end.

Coercion apply_ifun : ifun >-> Funclass.

Check (fun (N : PNet) (i : ifun) => i N).
Check (fun (T : Set) (N : NetMod.t T) n => N n).


Hint Transparent NetGet : LTS_concl rewrite.
Goal forall (T : Set) (N : NetMod.t T) S m n, (NetMod.put n S N) n = S \/ NetMod.put n S N m <> N n.
  intros.
  ltac1:(rewrite_strat bottomup (eval compute [NetGet]; hints LTS_concl)).
  ltac1:(rewrite_strat bottomup (eval compute [NetGet]; hints LTS_concl)).


Definition apply_net (N : PNet) : Name -> Serv := fun n => NetMod.get n N.
