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
Require Import DlStalk.PresentationCompat.
Require Import DlStalk.GenFramework.

From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Structures.Equalities.
Import ListNotations.
Open Scope string_scope.

Import Theory.
Import SrpcDefs.

(** * Introduction *)

(** This module iterates through the major theorems, lemmas, definitions and
notations that are used in or relevant to the paper. Some definitions have been
edited in the paper for readability --- those which were simplified
significantly have been proven to be equivalent to their counterparts used in
this mechanisation.

The project uses [Ltac2] as the proof language. [DlStalk.Tactics] contains
definitions of custom tactics. *)

(** Generic predicate for invariants over transitions. *)
Print trans_invariant.
(** Helper to mark unconditional invariants. *)
Print always.

(** * Modelling Networks of RPC Services *)

(** ** Syntax of Processes, Queues, and Services *)

(** Basic (see [DlStalk.ModelData]) *)
Print Tag.
Check Q : Tag.
Check R : Tag.

Check Val : Set.
Check Name : Set.

(** Process and service (see [DlStalk.Model]) *)
Print Proc.
Check Que Val.
Print Serv.

(** We abstract implementation of the network to a module type. Contrary to the
paper, we do not use plain functions to represent networks, because that would
require quite global extensionality which we do not need in general. (see
[DlStalk.Network]) *)

Print NET_MOD.

(**  Creation of networks from functions *)
Check NetMod.init : (Name -> Serv) -> NetMod.t Serv.

(** Access *)
Check NetMod.get : Name -> NetMod.t Serv -> Serv.
(** Modification *)
Check NetMod.put : Name -> Serv -> NetMod.t Serv -> NetMod.t Serv.

(** Initialisation access axiom *)
Check NetMod.init_get :
        forall (f : Name -> Serv) (n : Name),
          NetMod.get n (NetMod.init f) = f n.

(** Fresh access axioms *)
Check NetMod.get_put_eq :
        forall n S N,
          NetMod.get n (NetMod.put n S N) = S.
Check NetMod.get_put_neq :
        forall n n' S N,
          n <> n' ->
          NetMod.get n (NetMod.put n' S N) = NetMod.get n N.

(** Update axioms *)
Check NetMod.put_put_eq :
        forall n S0 S1 N,
          NetMod.put n S1 (NetMod.put n S0 N) = NetMod.put n S1 N.
Check NetMod.put_put_neq :
        forall n n' S0 S1 N,
          n <> n' ->
          NetMod.put n S1 (NetMod.put n' S0 N) = NetMod.put n' S0 (NetMod.put n S1 N).

(** Overwrite axiom *)
Check NetMod.put_get_eq :
        forall n N, NetMod.put n (NetMod.get n N) N = N.

(** Extensionality axiom *)
Check NetMod.extensionality :
        forall N0 N1,
          (forall n, NetMod.get n N0 = NetMod.get n N1) -> N0 = N1.

(** ** Semantics of Processes, Queues, Services, and Networks *)

(** Generic definitions (see [DlStalk.LTS]) *)
Print LTS.
Print ptrans.
Locate "_ =( _ )=> _".
Locate "_ =[ _ ]=> _".

(** Actions (see [DlStalk.Que] and [DlStalk.Model]) *)
Print Act.
Print QAct.

(** Process, Queue and Service transitions. All are instances of the LTS class. *)
Print ProcTrans.
Print QTrans.
Print STrans.

Check trans_Serv : LTS PAct Serv.

(** Network transitions. [NVTrans] is used as a helper to progress nodes within
a network (see [DlStalk.Network]) *)
Print NVTrans.
Print NTrans.

(** ** Locks and Deadlocks *)

(** Paper-compatible definition of a service lock and dead_set (see [DlStalk.Locks] and [DlStalk.NetLocks]) *)
Print Paper.serv_lock.
Print Paper.dead_set.

(** Definitions used in the project *)
Print proc_lock.
Print serv_lock.
Print lock_set.
Print lock.
Print dead_set.

Check dead_set_invariant : forall DS, trans_invariant (dead_set DS) always.

(** Compatibility of project and paper definitions (for SRPC services; see
[DlStalk.SRPCNet]) *)
Check serv_lock_eq : forall S n, (exists srpc, SRPC_serv srpc S) -> serv_lock [n] S <-> Paper.serv_lock n S.
Check dead_set_eq : forall (N : Net) (DS : Names), SRPC_net N -> dead_set DS N <-> Paper.dead_set DS N.

(** Deadset-cycle equivalence (see [DlStalk.NetLocks]) *)
Check dead_set_cycle : forall N : Net,
          lock_uniq_type N -> lock_neq_nil_type N -> locks_dec_in N ->
          forall DS, dead_set DS N -> exists n, In n DS /\ trans_lock N n n.
Check cycle_dead_set : forall N : Net,
          lock_uniq_type N -> lock_neq_nil_type N ->
          forall n, trans_lock N n n -> exists DS, In n DS /\ dead_set DS N.

(** Well formed SRPC networks fulfill the prerequisites for dead_set-cycle
equivalence. (see [DlStalk.SRPCNet]) *)
Import SrpcNet.
Check SRPC_lock_set_uniq : forall [N : Net], SRPC_net N -> lock_uniq_type N.
Check SRPC_lock_set_neq_nil : forall [N : Net], SRPC_net N -> lock_neq_nil_type N.
Print locks_dec_in.
Check well_formed_lock_dec  : forall (N : Net) n0 n1, well_formed N -> lock N n0 n1 \/ ~ lock N n0 n1.

(** ** Single-Threaded RPC (SRPC) Services *)

(** SRPC Working and SRPC Locked are stored separately from SRPC Ready (see [DlStalk.SRPC]) *)
Print SRPC_State.
Print SRPC_Busy_State.

(** Paper-compatible definitions (see [DlStalk.PresentationCompat]) *)
Print Paper.SRPCC.
Print Paper.SRPCI.

(**  Original SRPC property is defined slightly differently *)
Check SRPC_eq.

(** ** A Coq Framework for Modelling Erlang/OTP-Style SRPC Networks *)

Section Framework.
  (** The name "Thomas" does not refer to any of the authors. *)
  Import Thomas.
  Import Sound.
  Import SrpcDefs.

  (** Types for generic network configuration (see [DlStalk.GenFramework]) *)
  Print ServiceConf.
  Print InitConf.
  Print NetConf.

  (** The network is SRPC! *)
  Check gen_net_SRPC : forall conf n, exists srpc, SRPC_serv srpc (NetMod.get n (gen_net conf)).

  (** Example services and network *)
  Print echo.
  Print service.
  Print example_net.

  (** Can deadlock *)
  Check can_deadlock : exists path N, (example_net =[ path ]=> N) /\ dead_set ["A"; "B"; "C"; "D"]%list N.
End Framework.

(** * Monitors, Instrumentation, and Transparency *)

(** Probes. [MProbe] is an alias for a slightly more generic [MProbe'] (see [DlStalk.Compl]) *)
Locate MProbe.
Print MProbe'.
Check origin : MProbe -> Name.
Check lock_id : MProbe -> nat.

(** Monitor messages (stored in the monitor queue) (see [DlStalk.Model]) *)
Print EMsg.
Locate MQue.

(** Monitor state (see [DlStalk.Compl]) *)
Locate MState.
Print MState'.
Check self : MState -> Name.
Check locked : MState -> option Name.
Check wait : MState -> list Name.
Check lock_count : MState -> nat.
Check alarm : MState -> bool.

(** Monitor process (see [DlStalk.Model]) *)
Print MProc.
Check MRecv : MState -> MProc.
Check MSend : (Name * Tag) -> MProbe -> MProc -> MProc.

(** Monitored service (see [DlStalk.Model]) *)
Print MServ.
Check mserv_q.
Check mserv_m.
Check mserv_s.

(** Transition of monitored services (see [DlStalk.Model]) *)
Print MTrans.

(** Instrumentation (see [DlStalk.Model]) *)
Print mon_assg.
Print instr.
Check apply_instr.

(** De-instrumentation (see [DlStalk.Model]) *)
Print retract_recv.
Print retract_send.
Print serv_deinstr.
Print deinstr.

Check instr_inv : forall (i : instr) N, deinstr (i N) = N.

(** Networks are generic, thus work for monitored services too (see [DlStalk.Network] and [DlStalk.Transp]) *)
Check (NetMod.get : Name -> MNet -> MServ).
Check (NetMod.get : Name -> Net  -> Serv).

(** Transparency (see [DlStalk.Transp]) *)
Check transp_sound : forall mnpath (MN0 MN1 : MNet),
          MN0 =[ mnpath ]=> MN1 -> exists pnpath, deinstr MN0 =[ pnpath ]=> deinstr MN1.
Check @transp_complete : forall path (i0 : instr) (N0 N1 : Net),
          N0 =[ path ]=> N1 -> exists mpath (i1 : instr), i0 N0 =[ mpath ]=> i1 N1.


(** * A Black-Box Distributed Deadlock Detection Algorithm *)

Module Type Alg. (* We need to backdoor it a bit... *)
  Declare Module Conf : DETECT_CONF.
  Declare Module Params : MON_PARAMS(Conf).
  Include Mh(Conf)(Params).

  (** Implementation of the algorithm (see [DlStalk.Compl]) *)
  Check mon_handle : EMsg -> MState -> MProc.
  Print mon_handle.
End Alg.

(** * Correctness of Black-Box Distributed Deadlock Detection *)

(** ** Monitor Correctness Criteria *)

Section Correct.
  Import Thomas.

  (** Definition of correctness (see [DlStalk.GenFramework]) *)
  Print detect_sound.
  Print detect_complete.
  Print detect_correct.
End Correct.

(** ** Finding and Proving Invariants *)

(** *** Well-Formed SRPC Networks  *)

(** Definition of the client relation and compatibility between the project and the paper (see [DlStalk.PresentationCompat]) *)
Print Paper.client.
Print serv_client.
Check client_eq : forall n S, serv_client n S <-> Paper.client n S.

(**  Well-formedness at the greatest detail (see [DlStalk.SRPCNet]) *)
Print service_wf.

Check service_wf_SRPC_inv : forall [srpc : SRPC_State] [S],
    service_wf srpc S -> SRPC_serv srpc S.
Check service_wf_Q_in_inv : forall [srpc : SRPC_State] [c v v' I I' P O],
    service_wf srpc (serv I P O) ->
    Deq (c, Q) v I I' ->
    not (List.In (c, Q, v') I').
Check service_wf_R_in_inv : forall [srpc : SRPC_State] [s s' v v' I I' P O],
    service_wf srpc (serv I P O) ->
    Deq (s, R) v I I' ->
    not (List.In (s', R, v') I').
Check service_wf_R_in_lock_inv : forall [srpc : SRPC_State] [s v I P O],
    service_wf srpc (serv I P O) ->
    In (s, R, v) I ->
    exists c, srpc = Locked c s.
Check service_wf_Q_out_lock_inv : forall [srpc : SRPC_State] [s v I P O],
    service_wf srpc (serv I P O) ->
    In (s, Q, v) O ->
    exists c, srpc = Locked c s.
Check service_wf_Q_out_last_inv : forall [srpc : SRPC_State] [s v I P O],
    service_wf srpc (serv I P O) ->
    ~ (In (s, Q, v) (List.removelast O)).
Check service_wf_Q_out_uniq_inv : forall [srpc : SRPC_State] [c v v' I P O O'],
    service_wf srpc (serv I P O) ->
    Deq (c, R) v O O' ->
    ~ (In (c, R, v') O').
Check service_wf_R_Q_inv : forall [srpc : SRPC_State] [s v v' I P O],
    service_wf srpc (serv I P O) ->
    In (s, R, v) I -> not (In (s, Q, v') O).
Check service_wf_Q_R_inv : forall [srpc : SRPC_State] [s v v' I P O],
    service_wf srpc (serv I P O) ->
    In (s, Q, v) O -> not (In (s, R, v') I).
Check service_wf_lock_Q_inv : forall [c s I P O],
    service_wf (Locked c s) (serv I P O) ->
    O <> [] ->
    exists v, In (s, Q, v) O.
Check service_wf_Q_excl_R_inv : forall [srpc : SRPC_State] [c v v' I P O],
    service_wf srpc (serv I P O) ->
    In (c, Q, v) I ->
    ~ In (c, R, v') O.
Check service_wf_Q_excl_c_inv : forall [srpc : SRPC_State] [c v I P O],
    service_wf srpc (serv I P O) ->
    In (c, Q, v) I ->
    ~ proc_client c P.
Check service_wf_R_excl_Q_inv : forall [srpc : SRPC_State] [c v v' I P O],
    service_wf srpc (serv I P O) ->
    In (c, R, v) O ->
    ~ In (c, Q, v') I.
Check service_wf_R_excl_c_inv : forall [srpc : SRPC_State] [c v I P O],
    service_wf srpc (serv I P O) ->
    In (c, Q, v) I ->
    ~ proc_client c P.
Check service_wf_c_excl_Q_inv : forall [srpc : SRPC_State] [c v I P O],
    service_wf srpc (serv I P O) ->
    proc_client c P ->
    ~ In (c, Q, v) I.
Check service_wf_c_excl_R_inv : forall [srpc : SRPC_State] [c v I P O],
    service_wf srpc (serv I P O) ->
    proc_client c P ->
    ~ In (c, R, v) O.

Print well_formed.
Check well_formed_invariant : trans_invariant well_formed always.

(** *** Monitor Knowledge Invariant for Sound Deadlock Detection  *)

(** (see [DlStalk.Sound]) *)
Print sends_to.
Print sends_to_mon.
Check stm_find : forall n p M, sends_to_mon (MSend (n, R) p M) n p.
Check stm_seek : forall n nc' p p' M,
    nc' <> (n, R) \/ p <> p' ->
    sends_to_mon M n p ->
    sends_to_mon (MSend nc' p' M) n p.

Print KIS.

Check KIS_well_formed : forall [MN], KIS MN -> well_formed '' MN.
Check KIS_self : forall [MN], KIS MN -> forall n0, self (MN n0) = n0.
Check KIS_locked : forall [MN], KIS MN -> forall n0 n1, locked (MN n0) = Some n1 -> lock '' MN n0 n1 \/ exists v, List.In (MqRecv (n1, R) v) (mserv_q (MN n0)).
Check KIS_wait : forall [MN], KIS MN -> forall n0 n1, List.In n0 (wait (MN n1)) -> lock '' MN n0 n1.
Check KIS_sendp : forall [MN], KIS MN -> forall n0 n1 p, sends_to MN n1 n0 p -> lock '' MN n0 n1.
Check KIS_lock_id_sendp : forall [MN], KIS MN -> forall n0 n1 p, sends_to MN n0 n1 p -> (lock_id p <= lock_count (MN (origin p)))%nat.
Check KIS_lock_id_recvp : forall [MN], KIS MN -> forall n0 n1 p, List.In (MqProbe (n1, R) p) (mserv_q (MN n0)) -> (lock_id p <= lock_count (MN (origin p)))%nat.
Check KIS_sendp_active : forall [MN], KIS MN -> forall n0 n1 n2, sends_to MN n1 n0 (active_probe_of MN n2) -> locked (MN n2) <> None -> trans_lock '' MN n0 n2.
Check KIS_recvp_active : forall [MN], KIS MN -> forall n0 n1 n2, List.In (active_ev_of MN n2 n0) (mserv_q (MN n1)) -> locked (MN n0) <> None -> trans_lock '' MN n1 n0.
Check KIS_alarm : forall [MN], KIS MN -> forall n, alarm (MN n) = true -> trans_lock '' MN n n.

Check KIS_invariant : trans_invariant KIS always.
Check KIS_detection_sound : forall (i0 : instr) N0 MN1 mpath n,
    KIS (i0 N0) -> (i0 N0 =[ mpath ]=> MN1) -> alarm (MN1 n) = true ->
    exists DS, dead_set DS '' MN1 /\ In n DS.

(** Monitor message (in monitor queue) holding an active probe *)
Print active_ev_of.

(** *** Monitor Knowledge Invariant for Complete Deadlock Detection  *)

(**  (see [DlStalk.Compl]) *)

Print sends_probe.
Print alarm_condition. (* TODO rename *)
Print KIC.

Check KIC_invariant : trans_invariant KIC always.
Check ac_to_alarm : forall MN0 n,
    KIC MN0 ->
    alarm_condition n MN0 ->
    trans_lock '' MN0 n n ->
    exists DS mpath MN1,
      (MN0 =[ mpath ]=> MN1) /\ dead_set DS '' MN0 /\ detect_path DS mpath /\ alarm (MN1 n) = true.

Check KIC_detection_complete : forall (i0 : instr) N0 MN1 mpath0 DS,
    KIC (i0 N0) ->
    (i0 N0 =[ mpath0 ]=> MN1) ->
    dead_set DS '' MN1 ->
    exists mpath1 MN2 n,
      (MN1 =[ mpath1 ]=> MN2) /\ In n DS /\ alarm (MN2 n) = true.

(** ** Correct Monitoring for Erlang << gen_server >> -Style Applications  *)

Section Correct.
  Import Thomas. Import Sound.

  (** The framework is correct (see [DlStalk.GenFramework]) *)
  Print gen_instr.

  Check gen_net_well_formed : forall conf, well_formed (gen_net conf).
  Check gen_KIS : forall conf : NetConf, KIS (gen_instr (gen_net conf)).
  Check gen_KIC : forall conf : NetConf, KIC (gen_instr (gen_net conf)).

  Check gen_correct : forall conf, detect_correct (gen_net conf) gen_instr.

  (** Let's say it again *)
  Check gen_correct : forall conf,
      let N0 := gen_net conf in
      and
        (forall path' MN1 n,
            (gen_instr N0 =[ path' ]=> MN1) /\ alarm (MN1 n) = true ->
            exists DS, In n DS /\ dead_set DS '' MN1
        )
        (forall path0' MN1 DS,
            (gen_instr N0 =[ path0' ]=> MN1) -> dead_set DS '' MN1 ->
            exists path1' MN2 n, (MN1 =[ path1' ]=> MN2) /\ In n DS /\ alarm (MN2 n) = true
        ).
End Correct.
