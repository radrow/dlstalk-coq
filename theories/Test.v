(* -*- company-coq-local-symbols: (("pi" . ?π) ("btw" . ?🤔)); -*- *)

(* From Ltac2 Require Import Ltac2. *)
(* From Ltac2 Require Import Std. *)
Module Empty. End Empty.

From Coq Require Import Structures.Equalities.

Require Import DlStalk.Tactics.

Close Scope nat.


Module Type WRAP.
  Parameter t : Set.
End WRAP.

Module Type PARAMS.
  Declare Module Arg : WRAP.
End PARAMS.

Module JOKER.
End JOKER.

Module Type COMBINED := PARAMS <+ JOKER.

Module Inst <: WRAP.
  Inductive t_ := Q | R. (* Fix 2: Move this definition away *)
  Definition t := t_.
End Inst.

Module Type RECOMBINED := COMBINED with Module Arg := Inst.

Module LOCK_DEFS(Mod : RECOMBINED).
  Goal Mod.Arg.t -> Inst.t.
    intros.
    assert (Mod.Arg.t = Inst.t). exact eq_refl.
    destruct (H : Inst.t). (* Error: Anomaly "Uncaught exception Not_found." Please report at http://coq.inria.fr/bugs/. *)



Fail "".







(** ***************** *)

Module Type NAME.
  Parameter t : Set.
End NAME.

Module Type TAG.
  Parameter t : Set.
End TAG.

Module Type MODEL_DATA.
  Declare Module Name : NAME.
  Declare Module Tag : TAG.
  Parameter MState : Set.
End MODEL_DATA.

Module Type MODEL(ModelData : MODEL_DATA).
  Inductive P := p : ModelData.Name.t -> P.
  Inductive M := m : P -> ModelData.MState -> M.
End MODEL.

Module Type NET_MOD(ModelData : MODEL_DATA).
  Parameter t : Set -> Set.
  Parameter get : forall [A : Set], ModelData.Name.t -> t A -> A.
End NET_MOD.

Module Type NET(MD : MODEL_DATA)(NetMod : NET_MOD(MD)).
  Inductive NTrans (A : Set) : NetMod.t A -> Prop :=
    NT (x : NetMod.t A) : (forall n0 n1, NetMod.get n0 x = NetMod.get n1 x) -> NTrans A x.
End NET.

Module Tag : TAG.
  Definition t := bool.
End Tag.

Module Type LOCKS_MD := MODEL_DATA
                        with Module Tag := Tag
                        with Definition MState := unit.

Module Type LOCKS(LocksMD : LOCKS_MD).
End LOCKS.

Module Type AA(MD : LOCKS_MD).
  Declare Module NetMod : NET_MOD(MD).
End AA.
Module Type NET_LOCKS_PARAMS := LOCKS_MD <+ AA.

Module Type NET_LOCKS(P : NET_LOCKS_PARAMS).
  Import P.
End NET_LOCKS.

Module MyParams : NET_LOCKS_PARAMS.
  Module Name. Definition t := nat. End Name.
  Module Tag := Tag.
  Definition MState := unit.
  Module NetMod. Definition t := fun x : Set => x.
                 Lemma get : forall [A : Set], Name.t -> t A -> A. auto. Qed.
  End NetMod.
End MyParams.

Module NetLocks := Empty <+ NET_LOCKS(MyParams).



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
