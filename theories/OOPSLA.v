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
Require Import DlStalk.GenFramework.
Require Import DlStalk.PresentationCompat.

From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Structures.Equalities.
Import ListNotations.
Open Scope string_scope.

Import Theory.
Import SrpcDefs.

(** * Introduction *)

(** Generic definitions (see [DlStalk.LTS]) *)
Print LTS.
Print ptrans.
Locate "_ =( _ )=> _".
Locate "_ =[ _ ]=> _".


(** * Correctness Criteria for Deadlock Detection Monitors in Distributed Systems *)

Module CorrectnessCriteria.
  Import GenServerNet.
  Import SrpcNet.NetLocks.

  (** ** Transparency *)
  Definition transp_completeness (N0 : Net) (i0 : instr) :=
    forall path N1, (N0 =[ path ]=> N1) ->
    exists mpath (i1 : instr), i0 N0 =[ mpath ]=> i1 N1.

  Definition transp_soundness (N0 : Net) (i0 : instr) :=
    forall mnpath0 (MN1 : MNet), (i0 N0 =[ mnpath0 ]=> MN1) ->
    exists mnpath1 pnpath (i2 : instr) (N2 : Net),
      (MN1 =[ mnpath1 ]=> i2 N2) /\ (N0 =[ pnpath ]=> N2).

  (** ** Preciseness *)

  Definition detect_soundness N0 (i0 : instr) :=
    forall path' MN1 n,
      (i0 N0 =[ path' ]=> MN1) /\ alarm (MN1 n) = true ->
      exists DS, In n DS /\ dead_set DS (deinstr MN1).

  Definition detect_completeness N0 (i0 : instr) :=
    forall path0' (MN1 : MNet) (DS : list Name),
      (i0 N0 =[ path0' ]=> MN1) ->
      dead_set DS (deinstr MN1) ->
      exists path1' (MN2 : MNet) (n : Name),
        (MN1 =[ path1' ]=> MN2)
        /\ In n DS /\ alarm (MN2 n) = true.

  (** ** Correctness *)

  Definition detect_correct (N : Net) (i : instr) :=
      transp_completeness N i
    /\ transp_soundness N i
    /\ detect_soundness N i
    /\ detect_completeness N i.
End CorrectnessCriteria.

(** * A Formal Model of Networks of RPC-Based Services *)

(** ** Services: Syntax and Semantics *)

(** We do not support casts, because they are irrelevant to deadlock detection
(and the algorithm does not care about them). *)

Print Tag.
Check Q : Tag.
Check R : Tag.

Check Val : Set.
Check Name : Set.

(** *** Queues and Services  *)

Check ((_ : Que Val) : list (Name * Tag * Val)).

Print Serv.
Check serv_i : Serv -> Que Val.
Check serv_p : Serv -> Proc.
Check serv_o : Serv -> Que Val.

(** *** Concrete processes *)
(** The mechanisation operates on concrete processes ([Proc]) programmed
coinductively in Gallina (see [DlStalk.Model]). *)
Print Proc.

(** [STau], [PSend], [PRecv] are constructors of concrete processes. The first
two are rather standard to process calculi. The receive operator is more tricky:
to avoid explicit substitutions, it stores a semantic message selector function
that filters received messages based on [Name] and [Tag]: if the message is
rejected, the function returns [None]; otherwise, it returns [Some c] where [c]
is a continuation function parameterised by the payload [Val] of the message.
(see [DlStalk.Model]) *)
Check STau : Proc -> Proc.
Check PSend : (Name * Tag) -> Val -> Proc -> Proc.
Check PRecv : ((Name * Tag) -> option (Val -> Proc)) -> Proc.

(** *** SRPC processes (see [DlStalk.SRPC]) *)
(** The generic SRPC process is captured under the [SRPC_State] type. *)

Print SRPC_State.
Print SRPC_Busy_State.

(** We characterise concrete SRPC processes via a coinductive property [SRPCC]
to describe the simulation relation, and [SRPCI] for inductive features such as
weak termination of each query. (see [DlStalk.PresentationCompat]) *)

Print Paper.SRPCC.
Print Paper.SRPCI.

(** Internally, the mechanisation uses a bit more messy [SRPC] property. We
prove both equivalent. (see [DlStalk.SRPC] and [DlStalk.PresentationCompat] for
compatibility lemma) *)

Print SRPC.
Print SRPC_Busy.

Check SRPC_eq : forall (P : Proc) (srpc : SRPC_State), SRPC srpc P <-> Paper.SRPCC srpc P.

(** *** Semantics of services *)

(** Actions (see [DlStalk.Que] and [DlStalk.Model]) *)
Print Act.
Print QAct.

(** Process, Queue and Service transitions. All are instances of the LTS class.
*)
Print ProcTrans.
Print QTrans.
Print STrans.

Check trans_Serv : LTS PAct Serv.

(** *** Networks *)
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
Check NetMod.init_get : forall (f : Name -> Serv) (n : Name),
    NetMod.get n (NetMod.init f) = f n.

(** Fresh access axioms *)
Check NetMod.get_put_eq : forall n S N,
    NetMod.get n (NetMod.put n S N) = S.
Check NetMod.get_put_neq : forall n n' S N,
    n <> n' ->
    NetMod.get n (NetMod.put n' S N) = NetMod.get n N.

(** Update axioms *)
Check NetMod.put_put_eq : forall n S0 S1 N,
    NetMod.put n S1 (NetMod.put n S0 N) = NetMod.put n S1 N.
Check NetMod.put_put_neq : forall n n' S0 S1 N,
    n <> n' ->
    NetMod.put n S1 (NetMod.put n' S0 N) = NetMod.put n' S0 (NetMod.put n S1 N).

(** Overwrite axiom *)
Check NetMod.put_get_eq :
  forall n N, NetMod.put n (NetMod.get n N) N = N.

(** Extensionality axiom *)
Check NetMod.extensionality :
  forall N0 N1,
    (forall n, NetMod.get n N0 = NetMod.get n N1) -> N0 = N1.


(** Network semantics. [NVTrans] is used as a helper to progress nodes within a
network (see [DlStalk.Network]). *)
Print NVTrans.
Print NTrans.

Goal Net = NetMod.t Serv. reflexivity. Qed.

(** ** Locks and Deadlocks *)
(** Definition of a service lock and dead_set (see [DlStalk.Locks] and
[DlStalk.NetLocks]) *)
Print Paper.serv_lock.
Print Paper.dead_set.

(** Definitions used in the mechanisation are slightly different (i.e. more
general to aim at compatibility with the OR model). *)
Print proc_lock.
Print serv_lock.
Print lock_set.
Print lock.
Print dead_set.

(** _Lemma 3.8_ *)
Check dead_set_invariant : forall DS, trans_invariant (dead_set DS) always.

(** Compatibility of definitions between the submission and the mechanisation
(for SRPC services; see [DlStalk.SRPCNet]). Note that [proc_lock] is more
generic and uses lock lists --- for future compatibility with the OR model. In
case of SRPC this is always a singleton (modulo duplicates). Additionally,
[serv_lock] relies on an additional predicate [Decisive], which asserts that the
process does not receive queries and responses at the same time --- in the
submission, this problem is irrelevant as it is prevented by the syntax, thus
not mentioned there to avoid confusion. *)
Print Decisive.
Check serv_lock_eq : forall S n,
    (exists srpc, SRPC_serv srpc S) ->
    serv_lock [n] S <-> Paper.serv_lock n S.
Check dead_set_eq : forall (N : Net) (DS : Names),
    SRPC_net N ->
    dead_set DS N <-> Paper.dead_set DS N.

(** * A Model of Generic Distributed Black-Box Outline Monitors *)

(** ** Monitored Services and Networks *)

(** Probes. [MProbe] is an alias for a slightly more generic [MProbe'] (see
[DlStalk.Compl]) *)
Locate MProbe.
Print MProbe'.
Check origin  : MProbe -> Name.
Check lock_id : MProbe -> nat.

(** Monitor messages (stored in the monitor queue) (see [DlStalk.Model]) *)
Print EMsg.
Locate MQue.

(** Monitor state (see [DlStalk.Compl]) *)
Locate MState.
Print MState'.
Check self       : MState -> Name.
Check locked     : MState -> option Name.
Check wait       : MState -> list Name.
Check lock_count : MState -> nat.
Check alarm      : MState -> bool.

(** Monitor process (see [DlStalk.Model]) *)
Print MProc.
Check MRecv : MState -> MProc.
Check MSend : (Name * Tag) -> MProbe -> MProc -> MProc.

(** Monitored service (see [DlStalk.Model]) *)
Print MServ.
Check mserv_q : MServ -> MQue.
Check mserv_m : MServ -> MProc.
Check mserv_s : MServ -> Serv.

(** Transition of monitored services (see [DlStalk.Model]) *)
Print MTrans.

(** ** Instrumentation of Services and Transparency *)

(** Instrumentation (see [DlStalk.Model]) *)
Print mon_assg.
Print instr.
Check apply_instr : instr -> Net -> MNet.

(** De-instrumentation (see [DlStalk.Model]) *)
Print retract_recv.
Print retract_send.
Print serv_deinstr.
Print deinstr.

(** _Proposition 4.6_ *)
Check instr_inv : forall (i : instr) N, deinstr (i N) = N.

(** Networks are generic, thus work for monitored services too (see [DlStalk.Network] and [DlStalk.Transp]) *)
Check (NetMod.get : Name -> MNet -> MServ).
Check (NetMod.get : Name -> Net  -> Serv).

(** Transparency (see [DlStalk.Transp]) *)
Check transp_sound : forall mnpath (MN0 MN1 : MNet),
    MN0 =[ mnpath ]=> MN1 -> exists pnpath, deinstr MN0 =[ pnpath ]=> deinstr MN1.

Check @transp_complete : forall path (i0 : instr) (N0 N1 : Net),
    N0 =[ path ]=> N1 -> exists mpath (i1 : instr), i0 N0 =[ mpath ]=> i1 N1.

(** _Theorem 4.8_ *)
Goal forall N0 i0, CorrectnessCriteria.transp_completeness N0 i0.
  unfold CorrectnessCriteria.transp_completeness.
  eauto using transp_complete.
Qed.

(** _Theorem 4.11_ *)
Goal forall N0 i0, CorrectnessCriteria.transp_soundness N0 i0.
  unfold CorrectnessCriteria.transp_soundness.
  eauto using transp_sound_instr.
Qed.

(** * A Distributed Black-Box Monitoring Algorithm for Deadlock Detection *)

(** _Proposition 5.1_ : Deadset-cycle equivalence (see [DlStalk.NetLocks]) *)
Check dead_set_cycle : forall N : Net,
    lock_uniq_type N -> lock_neq_nil_type N -> locks_dec_in N ->
    forall DS, dead_set DS N -> exists n, In n DS /\ trans_lock N n n.

Check cycle_dead_set : forall N : Net,
    lock_uniq_type N -> lock_neq_nil_type N ->
    forall n, trans_lock N n n -> exists DS, In n DS /\ dead_set DS N.

Module Type Alg.
  (* It needs to be a bit backdoored to instantiate abstract parameters *)
  Declare Module Conf : DETECT_CONF.
  Declare Module Params : MON_PARAMS(Conf).
  Include Mh(Conf)(Params).

  (** _Definition 5.2_ Implementation of the algorithm (see [DlStalk.Compl]) *)
  Check mon_handle : EMsg -> MState -> MProc.
  Print mon_handle.
End Alg.

(** * Proving the Preciseness of Our Distributed Deadlock Detection Monitors *)

(** ** Invariant Properties of Well-Formed SRPC Networks *)

(** _Definition 6.2_ : The client relation. (see [DlStalk.NetLocks] and [DlStalk.PresentationCompat] for compatibility lemmas) *)
Print Paper.client.
Print serv_client.
Check client_eq : forall n S, serv_client n S <-> Paper.client n S.

(** _Definition 6.3_ : Well-formedness at the greatest detail (see [DlStalk.SRPCNet]) *)
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

(** _Definition 6.4_ *)
Print well_formed.

(** _Theorem 6.5_ *)
Check well_formed_invariant : trans_invariant well_formed always.

(** ** Monitor Knowledge Invariant for Complete Deadlock Detection  *)

(**  (see [DlStalk.Compl]) *)

Print sends_probe.

(** _Definition 6.8_ TODO compatibility *)
Print alarm_condition.

(** _Definition 6.7_ *)
Print KIC.

(** _Lemma 6.9_ *)
Check ac_to_alarm : forall MN0 n,
    KIC MN0 ->
    alarm_condition n MN0 ->
    trans_lock '' MN0 n n ->
    exists DS mpath MN1,
      (MN0 =[ mpath ]=> MN1)
      /\ dead_set DS '' MN0
      /\ detect_path DS mpath
      /\ alarm (MN1 n) = true.

(** _Theorem 6.10_ *)
Check KIC_invariant : trans_invariant KIC always.


(** ** Monitor Knowledge Invariant for Sound Deadlock Detection  *)

(** (see [DlStalk.Sound]) *)
Print sends_to.
Print sends_to_mon.
Check stm_find : forall n p M, sends_to_mon (MSend (n, R) p M) n p.
Check stm_seek : forall n nc' p p' M,
    nc' <> (n, R) \/ p <> p' ->
    sends_to_mon M n p ->
    sends_to_mon (MSend nc' p' M) n p.

(** _Definition 6.11_ *)
Print KIS.

Check KIS_well_formed : forall [MN], KIS MN -> well_formed '' MN.
Check KIS_self : forall [MN],
    KIS MN -> forall n0,
      self (MN n0) = n0.
Check KIS_locked : forall [MN],
    KIS MN -> forall n0 n1,
      locked (MN n0) = Some n1 ->
      lock '' MN n0 n1 \/ exists v, List.In (MqRecv (n1, R) v) (mserv_q (MN n0)).
Check KIS_wait : forall [MN],
    KIS MN -> forall n0 n1,
      List.In n0 (wait (MN n1)) ->
      lock '' MN n0 n1.
Check KIS_sendp : forall [MN],
    KIS MN -> forall n0 n1 p,
      sends_to MN n1 n0 p ->
      lock '' MN n0 n1.
Check KIS_lock_id_sendp : forall [MN],
    KIS MN -> forall n0 n1 p,
      sends_to MN n0 n1 p -> (lock_id p <= lock_count (MN (origin p)))%nat.
Check KIS_lock_id_recvp : forall [MN],
    KIS MN -> forall n0 n1 p,
      List.In (MqProbe (n1, R) p) (mserv_q (MN n0)) ->
      (lock_id p <= lock_count (MN (origin p)))%nat.
Check KIS_sendp_active : forall [MN],
    KIS MN -> forall n0 n1 n2,
      sends_to MN n1 n0 (active_probe_of MN n2) ->
      locked (MN n2) <> None -> trans_lock '' MN n0 n2.
Check KIS_recvp_active : forall [MN],
    KIS MN -> forall n0 n1 n2,
      List.In (active_ev_of MN n2 n0) (mserv_q (MN n1)) ->
      locked (MN n0) <> None ->
      trans_lock '' MN n1 n0.
Check KIS_alarm : forall [MN],
    KIS MN -> forall n,
      alarm (MN n) = true ->
      trans_lock '' MN n n.

(** _Theorem 6.12_ *)
Check KIS_invariant : trans_invariant KIS always.


Check KIC_detection_complete : forall (i0 : instr) N0 MN1 mpath0 DS,
    KIC (i0 N0) ->
    (i0 N0 =[ mpath0 ]=> MN1) ->
    dead_set DS '' MN1 ->
    exists mpath1 MN2 n,
      (MN1 =[ mpath1 ]=> MN2) /\ In n DS /\ alarm (MN2 n) = true.

Check KIS_detection_sound : forall (i0 : instr) N0 MN1 mpath n,
    KIS (i0 N0) -> (i0 N0 =[ mpath ]=> MN1) ->
    alarm (MN1 n) = true ->
    exists DS, dead_set DS '' MN1 /\ In n DS.

(** Monitor message (in monitor queue) holding an active probe *)
Print active_ev_of.


(** * DDMon, a Prototype Monitoring Tool for Distributed Deadlock Detection *)
