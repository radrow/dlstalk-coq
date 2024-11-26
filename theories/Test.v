(* -*- company-coq-local-symbols: (("pi" . ?π)); -*- *)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Std.

From Ltac2 Require Fresh.
From Ltac2 Require Import Control.
From Ltac2 Require Import Message.
From Ltac2 Require Import Std.
From Ltac2 Require Import Printf.

Import Ltac2.Notations.

Require LTS.
Require ModelData.
Require Network.
Require LTSTactics.
Require Locks.
Require Misra.
Require Sound.

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

Declare Module Name : ModelData.UsualDecidableSet.
Declare Module NetModF : Network.NET.

Require dpdgraph.dpdgraph.

Module M := Sound.Soundness(Name)(NetModF).

Check M.KIS_invariant.

Print DependGraph M.KIS_invariant File "KIS_invariant.dpd".
Print DependGraph M.KIS_invariant_KIC File "KIS_invariant_KIC.dpd".
Print DependGraph M.KIS_invariant_lock File "KIS_invariant_lock.dpd".
Print DependGraph M.KIS_invariant_wait File "KIS_invariant_wait.dpd".
Print DependGraph M.KIS_invariant_Q_in File "KIS_invariant_Q_in.dpd".
Print DependGraph M.KIS_invariant_R_in File "KIS_invariant_R_in.dpd".
Print DependGraph M.KIS_invariant_recvp File "KIS_invariant_recvp.dpd".
Print DependGraph M.KIS_invariant_recvp_hot File "KIS_invariant_recvp_hot.dpd".
Print DependGraph M.KIS_invariant_send_hot File "KIS_invariant_send_hot.dpd".
Print DependGraph M.KIS_invariant_sendp_wait File "KIS_invariant_sendp_wait.dpd".
Print DependGraph M.KIS_invariant_sendp_lock File "KIS_invariant_sendp_lock.dpd".
Print DependGraph M.KIS_invariant_probe_R File "KIS_invariant_probe_R.dpd".
Print DependGraph M.KIS_invariant_index_send File "KIS_invariant_index_send.dpd".
Print DependGraph M.KIS_invariant_index_recv File "KIS_invariant_index_recv.dpd".
Print DependGraph M.KIS_invariant_no_Q_probe_send File "KIS_invariant_no_Q_probe_send.dpd".
Print DependGraph M.KIS_invariant_alarm File "KIS_invariant_alarm.dpd".
