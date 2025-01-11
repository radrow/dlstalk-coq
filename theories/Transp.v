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

Require Import DlStalk.LTS.
Require Import DlStalk.Tactics.
Require Import DlStalk.Model.
Require Import DlStalk.ModelData.
Require Import DlStalk.Que.
Require Import DlStalk.Network.

Module Type MON_NET_PARAMS <: NET_PARAMS := MODEL_DATA <+ NET_PARAMS_F.
Module Type MON_NET := MON_NET_PARAMS <+ QUE <+ PROC <+ MON_F <+ NET_F.

Module MonNetTactics(M : MON_NET).
  Ltac2 destruct_mna_ a :=
    first
      [destruct $a as [? [[[? [|]]|[? [|]]|]|[[? ?]|[? ?]|]|[[? ?]|[? ?]|]] | ? ? [|] [?|?]] (* Q/R tags *)
      |destruct $a as [? [[[? ?]|[? ?]|]|[[? ?]|[? ?]|]|[[? ?]|[? ?]|]] | ? ? ? [?|?]] (* Anon tags *)
      ]; doubt.

  Ltac2 Notation "destruct_mna" a(constr) := destruct_mna_ a.
End MonNetTactics.


Module Type TRANSP(Import Params : MON_NET).

  Module Import Tactics := MonNetTactics(Params).

  (** Not-monitored network *)
  Definition PNet := NetMod.t PQued.
  (** Monitored network *)
  Definition MNet := NetMod.t MQued.

  #[export] Hint Transparent PNet MNet : LTS typeclass_instances.


  Lemma pq_I_net_inv : forall I P O n [N : PNet],
      NetMod.get n N = pq I P O ->
      pq_I (NetMod.get n N) = I.
  Proof. intros. rewrite H. attac. Qed.

  Lemma pq_P_net_inv : forall I P O n N,
      NetMod.get n N = pq I P O ->
      pq_P (NetMod.get n N) = P.
  Proof. intros. rewrite H. attac. Qed.

  Lemma pq_O_net_inv : forall I P O n N,
      NetMod.get n N = pq I P O ->
      pq_O (NetMod.get n N) = O.
  Proof. intros. rewrite H. attac. Qed.

  #[export] Hint Rewrite -> pq_I_net_inv pq_P_net_inv pq_O_net_inv using spank : LTS LTS_concl.
  #[export] Hint Resolve pq_I_net_inv pq_P_net_inv pq_O_net_inv : LTS LTS_concl.


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


  Section Completeness.
    Declare Custom Entry put.
    Notation "n := S" := (NetMod.put n S) (in custom put at level 10, n constr, S constr).
    Notation "N ::: [ f0 ] [ .. ] [ f1 ]" := (f1 (.. (f0 N) ..)) (at level 10, f0 custom put, f1 custom put).

    Notation "N ::: [ n0 := S0 ]" :=
      (NetMod.put n0 S0 N)
        ( at level 10,
          only printing,
          format "N  :::  [  n0  :=  S0  ]"
        ).

    Notation "N ::: [ n0 := S0 ] [ n1 := S1 ]" :=
      (NetMod.put n1 S1 (NetMod.put n0 S0 N))
        ( at level 10,
          only printing,
          format "N  :::  '[hv' '/' '[' [  n0  :=  S0  ] ']'  '/' '[' [  n1  :=  S1  ] ']' ']'"
        ).

    Notation "N ::: [ n0 := S0 ] [ n1 := S1 ] [ n2 := S2 ]" :=
      (NetMod.put n2 S2 (NetMod.put n1 S1 (NetMod.put n0 S0 N)))
        ( at level 10,
          only printing,
          format "N  :::  '[hv' '/' '[' [  n0  :=  S0  ] ']'  '/' '[' [  n1  :=  S1  ] ']' '/' '[' [  n2  :=  S2  ] ']' ']'"
        ).

    Notation "N ::: [ n0 := S0 ] [ n1 := S1 ] [ n2 := S2 ] [ n3 := S3 ]" :=
      (NetMod.put n3 S3 (NetMod.put n2 S2 (NetMod.put n1 S1 (NetMod.put n0 S0 N))))
        ( at level 10,
          only printing,
          format "N  :::  '[hv' '/' '[' [  n0  :=  S0  ] ']'  '/' '[' [  n1  :=  S1  ] ']' '/' '[' [  n2  :=  S2  ] ']' '/' '[' [  n3  :=  S3  ] ']' ']'"
        ).


    Definition MVal_to_Event (origin : NChan) (mv : MVal) : Event :=
      match mv with
      | MValP v => TrRecv origin v
      | MValM e => EvRecv origin e
      end.

    Fixpoint flushing_M_artifact (self : Name) (M : MCode) (n : Name) : list Event :=
      match M with
      | MRecv _ => []
      | MSend (n', t) e M' =>
          let MQ := flushing_M_artifact self M' n in
          if NAME.eqb n n' then EvRecv (self, t) e :: MQ else MQ
      end.


    Fixpoint flushing_M_artifacts (self : Name) (M : MCode) : list (Name * Event) :=
      match M with
      | MRecv _ => []
      | MSend (n, t) e M' =>
          (n, MVal_to_Event (self, t) (MValM e)) :: flushing_M_artifacts self M'
      end.

    Fixpoint flushing_artifacts (self : Name) (MQ : list Event) (M : Mon) : list (Name * Event) :=
      match MQ with
      | [] => flushing_M_artifacts self (state M)
      | e :: MQ' =>
          let l0 := flushing_M_artifacts self (state M) in
          let l1 := flushing_artifacts self MQ' {|handle:=handle M; state:=handle M e (next_state (state M))|} in
          l0 ++ match e with
            | TrSend (n, t) v => (n, MVal_to_Event (self, t) (MValP v)) :: l1
            | _ => l1
            end
      end.


    Definition Net_flushing_M_artifacts (origin : Name) (MN : MNet) : list (Name * Event) :=
      match NetMod.get origin MN with
      | mq _ M _ => flushing_M_artifacts origin (state M)
      end.

    Definition Net_flushing_artifacts (origin : Name) (MN : MNet) : list (Name * Event) :=
      match NetMod.get origin MN with
      | mq MQ M _ => flushing_artifacts origin MQ M
      end.


    Fixpoint Net_path_artifacts (origin : Name) (mpath : list MNAct) : list (Name * Event) :=
      match mpath with
      | [] => []
      | NTau _ _ :: mpath => Net_path_artifacts origin mpath
      | NComm n0 n1 t v :: mpath =>
          if NAME.eqb n0 origin
          then (n1, MVal_to_Event (origin, t) v) :: Net_path_artifacts origin mpath
          else Net_path_artifacts origin mpath
      end.

    Lemma Net_path_artifacts_app_inv : forall n mpath0 mpath1,
        Net_path_artifacts n (mpath0 ++ mpath1) = Net_path_artifacts n mpath0 ++ Net_path_artifacts n mpath1.
    Proof.
      induction mpath0; attac.
      destruct a; attac.
      smash_eq n0 n; attac.
      f_equal.
      attac.
    Qed.


    Definition apply_artifact_to (origin : Name) (n : Name) (e : Event)  (MN : MNet) :=
      match NetMod.get n MN with
      | mq MQ0 M0 S0 => MN ::: [n := mq (MQ0 ++ [e]) M0 S0]
      end.

    Definition apply_artifact (origin : Name) (MN : MNet) (art : Name * Event) :=
      match art with
      | (n, e) => apply_artifact_to origin n e MN
      end.

    Definition apply_artifacts (origin : Name) := List.fold_left (apply_artifact origin).

    Definition Net_flush_M_path (n : Name) (MN : MNet) : list MNAct :=
      match NetMod.get n MN with
      | mq _ M _ => lift_path n (flush_mcode (state M))
      end.


    Definition Net_flush_path (n : Name) (MN : MNet) : list MNAct :=
      lift_path n (flush_path (NetMod.get n MN)).


    Definition Net_flush_target (n : Name) (MN : MNet) : MNet :=
      apply_artifacts n (Net_flushing_artifacts n MN)
        (NetMod.put n (flush_MS (NetMod.get n MN)) MN).


    Definition Net_flush_M_target (n : Name) (MN : MNet) : MNet :=
      match NetMod.get n MN with
      | mq MQ0 M0 S0 => apply_artifacts n (Net_flushing_M_artifacts n MN)
                         (NetMod.put n (mq MQ0 ({|handle:=handle M0; state:=MRecv (next_state (state M0))|}) S0) MN)
      end.


    Hint Transparent Net_flushing_artifacts MVal_to_Event apply_artifact_to apply_artifact Net_flush_path  Net_flush_target : LTS.


    Fixpoint flushing_artifact_of (n : Name) (l : list (Name * Event)) : list Event :=
      match l with
      | [] => []
      | (m, e)::l =>
          if NAME.eqb n m then e :: flushing_artifact_of n l
          else flushing_artifact_of n l
      end.

    Lemma flushing_artifact_of_app_inv : forall n l0 l1,
        flushing_artifact_of n (l0 ++ l1) = flushing_artifact_of n l0 ++ flushing_artifact_of n l1.

    Proof.
      induction l0; attac.
      smash_eq n n0; attac.
      f_equal.
      eapply IHl0.
    Qed.

    Lemma flushing_artifact_of_M_eq : forall n0 n1 M0,
        flushing_M_artifact n0 M0 n1 = flushing_artifact_of n1 (flushing_M_artifacts n0 M0).

    Proof.
      intros.
      induction M0; attac.
    Qed.

    Lemma flushing_arifact_of_eq : forall n0 n1 MQ0 M0,
        flushing_artifact n0 MQ0 M0 n1 = flushing_artifact_of n1 (flushing_artifacts n0 MQ0 M0).

    Proof.
      intros.
      generalize dependent M0.
      induction MQ0; intros.
      - eauto using flushing_artifact_of_M_eq.
      - simpl.
        replace (flushing_M_artifact n0 (state M0) n1)
          with (flushing_artifact_of n1 (flushing_M_artifacts n0 (state M0))) by eauto using flushing_artifact_of_M_eq.
        rewrite flushing_artifact_of_app_inv.
        rewrite flushing_artifact_of_M_eq.
        apply app_inv_r.
        destruct a; attac.
        smash_eq n1 n2; attac.
        f_equal.
        attac.
    Qed.

    Lemma Net_path_flushing_M_artifacts_of_eq' : forall n0 n1 M0,
        flushing_artifact_of n1 (Net_path_artifacts n0 (lift_path n0 (flush_mcode M0))) =
          flushing_artifact_of n1 (flushing_M_artifacts n0 M0).
    Proof.
      induction M0; attac.
      attac.
    Qed.

    Lemma Net_path_flushing_M_artifacts_of_eq : forall n0 n1 MN0,
        flushing_artifact_of n1 (Net_path_artifacts n0 (Net_flush_M_path n0 MN0)) = flushing_artifact_of n1 (Net_flushing_M_artifacts n0 MN0).

    Proof.
      intros.
      unfold Net_flushing_M_artifacts, Net_flush_M_path.

      destruct (NetMod.get n0 MN0) as [MQ0 [h M0] S0].
      eauto using Net_path_flushing_M_artifacts_of_eq'.
    Qed.

    Lemma lift_path_app_inv : forall n mpath0 mpath1,
        lift_path n (mpath0 ++ mpath1) = lift_path n mpath0 ++ lift_path n mpath1.
    Proof.
      induction mpath0; attac.
      destruct_ma a; try (rewrite <- app_comm_cons); f_equal; attac.
    Qed.

    Lemma Net_path_flushing_artifacts_of_eq : forall n0 n1 MN0,
        flushing_artifact_of n1 (Net_path_artifacts n0 (Net_flush_path n0 MN0)) = flushing_artifact_of n1 (Net_flushing_artifacts n0 MN0).

    Proof.
      intros.
      unfold Net_flushing_artifacts, Net_flush_path.
      destruct (NetMod.get n0 MN0) as [MQ0 M0 S0].
      clear MN0.

      rewrite <- flushing_arifact_of_eq.

      generalize dependent M0.
      induction MQ0; intros.
      - simpl.
        rewrite Net_path_flushing_M_artifacts_of_eq'.
        now rewrite flushing_artifact_of_M_eq.
      - simpl.
        rewrite <- IHMQ0; clear IHMQ0.
        rewrite lift_path_app_inv.
        rewrite flushing_artifact_of_M_eq.
        rewrite Net_path_artifacts_app_inv.
        rewrite flushing_artifact_of_app_inv.
        rewrite Net_path_flushing_M_artifacts_of_eq'.
        destruct a; attac.
        apply app_inv_r; attac.
    Qed.


    Lemma Net_path_flushing_M_artifacts_eq : forall n0 MN0,
        Net_path_artifacts n0 (Net_flush_M_path n0 MN0) = Net_flushing_M_artifacts n0 MN0.

    Proof.
      intros.

      unfold Net_flush_M_path, Net_flushing_M_artifacts in *.
      destruct (NetMod.get n0 MN0) as [MQ0 [h M0] S0].
      induction M0; attac.
      attac.
    Qed.

    Lemma Net_path_flushing_M_artifacts_eq' : forall n0 M,
        Net_path_artifacts n0 (lift_path n0 (flush_mcode (state M))) = flushing_M_artifacts n0 (state M).

    Proof.
      intros.
      destruct M as [h M].
      unfold Net_flush_M_path, Net_flushing_M_artifacts in *.
      induction M; attac.
      attac.
    Qed.


    Lemma Net_path_flushing_artifacts_eq : forall n0 MN0,
        Net_path_artifacts n0 (Net_flush_path n0 MN0) = Net_flushing_artifacts n0 MN0.

    Proof.
      intros.

      unfold Net_flush_path, Net_flushing_artifacts in *.
      destruct (NetMod.get n0 MN0) as [MQ0 M0 S0].

      generalize dependent M0 S0.
      clear MN0.
      induction MQ0; intros.
      - attac.
        apply Net_path_flushing_M_artifacts_eq'.
      - simpl.
        rewrite <- Net_path_flushing_M_artifacts_eq'.
        rewrite lift_path_app_inv.
        rewrite Net_path_artifacts_app_inv.
        apply app_inv_r.

        destruct a; attac; attac.
        f_equal.
        attac.
    Qed.


    Lemma lift_path_app_trans : forall MN0 MN1 n mpath0 mpath1,
        (MN0 =[lift_path n (mpath0 ++ mpath1)]=> MN1) ->
        (MN0 =[lift_path n mpath0 ++ lift_path n mpath1]=> MN1).

    Proof.
      intros.
      generalize dependent MN0.
      induction mpath0; attac.

      destruct_ma a; attac.

      all:
        try
          (solve [edestruct (IHmpath0 _ `(_ =[lift_path n (_ ++ _)]=> _)) as [MN0' [? ?]];
                  attac;
                  eapply path_seq1 > [|eattac 15];
                  eattac; econstructor; eattac 15]
          ).
    Qed.


    Lemma lift_path_app_trans' : forall MN0 MN1 n mpath0 mpath1,
        (MN0 =[lift_path n mpath0 ++ lift_path n mpath1]=> MN1) ->
        (MN0 =[lift_path n (mpath0 ++ mpath1)]=> MN1).

    Proof.
      intros.
      generalize dependent MN0.
      induction mpath0; intros.
      1: { attac. }

      rewrite <- app_comm_cons in *.

      destruct_ma a; try (solve [attac]); hsimpl in H |- *.

      all: specialize (IHmpath0 _ (path_seq `(_ =[lift_path n mpath0]=> _) `(_ =[lift_path n mpath1]=> _)));
          eapply path_seq1 > [|eattac]; econstructor; eattac 15.
    Qed.


    Lemma Net_flush_M_go : forall n MN0,
        MN0 =[Net_flush_M_path n MN0]=> Net_flush_M_target n MN0.

    Proof.
      intros.
      unfold Net_flush_M_target.
      rewrite <- Net_path_flushing_M_artifacts_eq.
      unfold Net_flush_M_path.

      destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.

      destruct M0 as [h M0].
      generalize dependent MQ0 MN0.
      induction M0; attac.
      1: { rewrite <- `(NetMod.get n MN0 = _). attac. }

      hsimpl.

      pose (MN0' := NetMod.put n (mq MQ0 {|handle:=h; state:=M0|} S0) MN0).
      destruct (NetMod.get n0 MN0') as [MQ0' M0' S0'] eqn:?.
      pose (MN1 := NetMod.put n0 (mq (MQ0' ++ [EvRecv (n, t) msg]) M0' S0') MN0').

      apply path_seq1 with (N1:=MN1).
      1: { constructor 2 with (N0':=MN0'); attac. }

      destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.
      consider (M1 = {| handle := h; state := M0 |}) by (subst MN0' MN1; smash_eq n n0; attac).
      consider (S1 = S0) by (subst MN0' MN1; smash_eq n n0; attac).

      specialize (IHM0 MN1 MQ1 ltac:(attac)).

      enough (
          apply_artifacts n (Net_path_artifacts n (lift_path n (flush_mcode M0)))
            (MN1 ::: [ n := mq MQ1 {| handle := h; state := MRecv (next_state M0) |} S0 ])

          = apply_artifacts n (Net_path_artifacts n (lift_path n (flush_mcode M0)))
              (apply_artifact_to n n0 (EvRecv (n, t) msg)
                 (MN0 ::: [ n := mq MQ0 {| handle := h; state := MRecv (next_state M0) |} S0 ]))) by (rewrite <- `(apply_artifacts n _ _ = _); attac).
      clear IHM0.

      f_equal.

      subst MN0' MN1; attac.
      unfold apply_artifact_to.
      hsimpl in *.
      smash_eq n n0; attac.
      rewrite NetMod.put_put_neq; attac.
    Qed.


    Lemma apply_artifacts_inv_S : forall n0 n1 MQs MN0 MQ0 M0 S0 MQ1 M1 S1,
        NetMod.get n0 MN0 = mq MQ0 M0 S0 ->
        NetMod.get n0 (apply_artifacts n1 MQs MN0) = mq MQ1 M1 S1 ->
        S1 = S0.

    Proof.
      induction MQs; attac.
      destruct a; simpl in *.
      unfold apply_artifact_to in *.
      smash_eq n n0; attac.
      + eapply IHMQs with (MN0:= (MN0 ::: [ n := mq (MQ0 ++ [e]) M0 S0 ])); attac.
      + destruct (NetMod.get n MN0) as [MQ0' M0' S0'].
        eapply IHMQs with (MN0:= (MN0 ::: [ n := mq (MQ0' ++ [e]) M0' S0' ])); attac.
    Qed.
    Lemma apply_artifacts_inv_M : forall n0 n1 MQs MN0 MQ0 M0 S0 MQ1 M1 S1,
        NetMod.get n0 MN0 = mq MQ0 M0 S0 ->
        NetMod.get n0 (apply_artifacts n1 MQs MN0) = mq MQ1 M1 S1 ->
        M1 = M0.

    Proof.
      induction MQs; attac.
      destruct a; simpl in *.
      unfold apply_artifact_to in *.
      smash_eq n n0; attac.
      + eapply IHMQs with (MN0:= (MN0 ::: [ n := mq (MQ0 ++ [e]) M0 S0 ])); attac.
      + destruct (NetMod.get n MN0) as [MQ0' M0' S0'].
        eapply IHMQs with (MN0:= (MN0 ::: [ n := mq (MQ0' ++ [e]) M0' S0' ])); attac.
    Qed.
    Lemma apply_artifacts_inv_MQ : forall n0 n1 MQs MN0 MQ0 M0 S0 MQ1 M1 S1,
        NetMod.get n0 MN0 = mq MQ0 M0 S0 ->
        NetMod.get n0 (apply_artifacts n1 MQs MN0) = mq MQ1 M1 S1 ->
        MQ1 = MQ0 ++ flushing_artifact_of n0 MQs.

    Proof.
      induction MQs; attac.
      unfold apply_artifact_to in *.
      smash_eq n n0; attac.
      + enough (MQ1 = (MQ0 ++ [e]) ++ flushing_artifact_of n MQs) by attac.
        eapply IHMQs with (MN0:= (MN0 ::: [ n := mq (MQ0 ++ [e]) M0 S0 ])); attac.
      + destruct (NetMod.get n MN0) as [MQ0' M0' S0'].
        eapply IHMQs with (MN0:= (MN0 ::: [ n := mq (MQ0' ++ [e]) M0' S0' ])); attac.
    Qed.

    Hint Rewrite -> apply_artifacts_inv_S apply_artifacts_inv_M apply_artifacts_inv_MQ using spank : LTS LTS_concl.


    Lemma apply_artifacts_app_inv : forall n MQs0 MQs1 MN0,
        apply_artifacts n (MQs0 ++ MQs1) MN0 = apply_artifacts n MQs1 (apply_artifacts n MQs0 MN0).

    Proof.
      intros.
      generalize dependent MN0.
      induction MQs0; attac.
    Qed.


    Lemma flushing_artifact_M_flushed_nil : forall n MN0,
        Net_flushing_M_artifacts n (Net_flush_M_target n MN0) = [].

    Proof.
      intros.
      unfold Net_flushing_M_artifacts, Net_flush_M_target in *.
      destruct (NetMod.get n MN0) as [MQ0 [h s0] S0] eqn:?.
      attac.
      unfold Net_flushing_M_artifacts in *.
      attac.
      generalize dependent l m p MQ0 S0 MN0.
      induction s0; attac.
      destruct to.

      assert (NetMod.get n (MN0 ::: [ n := mq MQ0 {| handle := h; state := MRecv (next_state s0) |} S0 ]) = mq MQ0 {| handle := h; state := MRecv (next_state s0) |} S0). attac.
      assert (p = S0) by eauto using apply_artifacts_inv_S with LTS.
      eassert (m = {|handle:=h; state := _|}) by eauto using apply_artifacts_inv_M with LTS.
      eassert (l = MQ0 ++ flushing_artifact_of n _) by eauto using apply_artifacts_inv_MQ with LTS.
      subst.
      attac.
    Qed.

    Open Scope nat.

    (** How much MQ would be consumed from the front *)
    Definition Net_flush_act_consumption (a : MNAct) :=
      match a with
      | NTau _ _ => 1
      | NComm _ _ _ (MValM _) => 0
      | NComm _ _ _ (MValP _) => 1
      end.

    Fixpoint Net_flush_path_consumption (mpath : list MNAct) :=
      match mpath with
      | [] => 0
      | a :: mpath => Net_flush_act_consumption a + Net_flush_path_consumption mpath
      end.

    Lemma Net_flush_act_split : forall a n MN0 MN1 MQ0 MQ1 M0 S0 M1 S1,
        Flushing_NAct n a ->
        NetMod.get n MN0 = mq MQ0 M0 S0 ->
        NetMod.get n MN1 = mq MQ1 M1 S1 ->
        (MN0 =(a)=> MN1) ->
        exists MQ0' MQ1',
          MQ0 = MQ0' ++ MQ1' /\
          MQ1 = MQ1' ++ flushing_artifact_of n (Net_path_artifacts n [a]) /\
          length MQ0' = Net_flush_act_consumption a.

    Proof.
      intros.
      consider (_ =(_)=> _); attac.
      - destruct a0; attac.
        + destruct p; attac.
          exists [TrRecv n0 v], MQ; attac.
        + destruct a; attac.
          exists [EvRecv n0 msg], MQ; attac.
      - rewrite `(NetMod.get n MN0 = _) in *.
        smash_eq n n'; attac.
        + destruct v; attac.
          * exists [], MQ1; eattac.
          * exists [TrSend (n, t) v], MQ1; eattac.
        + destruct v; attac.
          * exists [], MQ2; eattac.
          * exists [TrSend (n', t) v], MQ2; eattac.
    Qed.


    Lemma Net_flush_act_cont : forall a n MN0 MN1 MQ0 MQ1 M0 S0 M1 S1 MQ' e,
        Flushing_NAct n a ->
        e = flushing_artifact_of n (Net_path_artifacts n [a]) ->
        NetMod.get n MN0 = mq MQ0 M0 S0 ->
        NetMod.get n MN1 = mq (MQ1 ++ e) M1 S1 ->
        (MN0 =(a)=> MN1) ->
        (MN0 ::: [n := mq (MQ0 ++ MQ') M0 S0] =(a)=> MN1 ::: [n := mq (MQ1 ++ MQ' ++ e) M1 S1]).

    Proof.
      intros.
      consider (_ =(a)=> _).
      - hsimpl in *.
        constructor; attac.
        replace (MN0 ::: [ n := mq (MQ1 ++ MQ') M1 S1 ]) with
          (MN0 ::: [ n := mq (MQ0 ++ MQ') M0 S0] ::: [ n := mq (MQ1 ++ MQ') M1 S1 ]) by attac.
        constructor; attac.
        hrewrite (NetMod.get n MN0) in *.
        eauto using Flushing_cont, path_seq0, path_split0 with LTS.
      - destruct (NetMod.get n N0') as [MQ0' M0' S0'] eqn:?.

        pose (MN0' := MN0 ::: [ n := mq (MQ0 ++ MQ') M0 S0 ] ::: [n0 := mq (MQ0' ++ MQ') M0' S0']).
        constructor 2 with (N0':=MN0').
        + assert (mq (MQ0 ++ MQ') M0 S0 =( send (n', t) v )=> mq (MQ0' ++ MQ') M0' S0').
          {
            assert (Flushing_act (send (n', t) v)) by (attac; destruct v; attac).
            assert (mq MQ0 M0 S0 =(send (n', t) v)=> (NetMod.get n N0')) by attac.
            hsimpl in *.
            hsimpl in *.
            eauto using Flushing_cont, path_seq0, path_split0 with LTS.
          }

          subst MN0'; attac.
        + subst MN0'.
          rewrite app_assoc.
          smash_eq n n0; attac.
          hsimpl in *.
          smash_eq n n'; hsimpl in *.
          * replace (MN0 ::: [ n := mq ((MQ1 ++ MQ') ++ [MVal_to_Event (n, t) v]) M1 S1 ])
              with (MN0 ::: [ n := mq (MQ0' ++ MQ') M0' S0' ] ::: [ n := mq ((MQ1 ++ MQ') ++ [MVal_to_Event (n, t) v]) M1 S1 ]) by attac.
            attac.
            destruct v; attac.
          * rewrite NetMod.put_put_neq; auto.
            hsimpl.
            constructor.
            attac.
    Qed.


    Lemma Net_flush_act_retract : forall a n MN0 MN1 MQ0 MQ1 M0 S0 M1 S1 MQ' e,
        Flushing_NAct n a ->
        e = flushing_artifact_of n (Net_path_artifacts n [a]) ->
        NetMod.get n MN0 = mq (MQ0 ++ MQ') M0 S0 ->
        NetMod.get n MN1 = mq (MQ1 ++ MQ' ++ e) M1 S1 ->
        (MN0 =(a)=> MN1) ->
        (MN0 ::: [n := mq MQ0 M0 S0] =(a)=> MN1 ::: [n := mq (MQ1 ++ e) M1 S1]).

    Proof.
      intros.
      consider (_ =(a)=> _).
      - hsimpl in *.
        constructor; attac.
        replace (MN0 ::: [ n := mq MQ1 M1 S1 ]) with
          (MN0 ::: [ n := mq MQ0 M0 S0] ::: [ n := mq MQ1 M1 S1 ]) by attac.
        constructor; attac.
        hrewrite (NetMod.get n MN0) in *.
        eauto using Flushing_retract1.
      - destruct (NetMod.get n N0') as [MQ0' M0' S0'] eqn:?.
        hsimpl in *.
        rewrite `(NetMod.get n MN0 = _) in *.
        hsimpl in *.
        smash_eq n n'; hsimpl in *.
        + replace (MN0 ::: [ n := mq (MQ1 ++ [MVal_to_Event (n, t) v]) M1 S1 ])
            with (MN0::: [ n := mq MQ0 M0 S0 ] ::: [ n := mq (MQ1 ++ [MVal_to_Event (n, t) v]) M1 S1 ]) by attac.
          destruct v.
          * consider (exists MQ0'', MQ0' = MQ0'' ++ MQ') by attac.
            apply NComm_eq with (S:=mq MQ0'' M0' S0'); destruct M0'; attac.
          * consider (exists MQ0'', MQ0' = MQ0'' ++ MQ') by attac.
            apply NComm_eq with (S:=mq MQ0'' M0' S0'); destruct M0'; attac.
        + hsimpl in *.
          rewrite NetMod.put_put_neq in *; auto. attac.
          replace (MN0 ::: [ n := mq MQ1 M1 S1 ] [ n' := &S ])
            with (MN0 ::: [ n := mq MQ0 M0 S0 ] [ n := mq MQ1 M1 S1 ] [ n' := &S ]) by attac.
          apply NComm_neq; attac.
          destruct v; attac.
          * consider (MQ1 = MQ0) by eauto using app_inv_tail.
            destruct M3; attac.
          * rewrite app_comm_cons in *.
            consider (MQ0 = (TrSend (n', t) v :: MQ1)) by eauto using app_inv_tail.
            attac.
    Qed.


    (** Flushing act does not add to the front
     *)
    Lemma Net_flush_act_nihil_novi : forall a n MN0 MN1 MQ0 M0 S0 M1 S1 MQ' MQs,
        Flushing_NAct n a ->
        MQs = flushing_artifact_of n (Net_path_artifacts n [a]) ->
        NetMod.get n MN0 = mq MQ0 M0 S0 ->
        NetMod.get n MN1 = mq (MQ' ++ MQ0 ++ MQs) M1 S1 ->
        (MN0 =(a)=> MN1) ->
        MQ' = [].

    Proof.
      intros.

      destruct MQ'; auto.
      exfalso; simpl in *.
      consider (_ =(_)=> _); hsimpl in *; attac.
      - rewrite `(NetMod.get n MN0 = _) in *.
        consider (_ =(a0)=> _); hsimpl in *; attac.
        + absurd (length MQ = length (e :: MQ' ++ EvRecv n0 v :: MQ)); attac.
        + absurd (length MQ = length (e :: MQ' ++ TrRecv n0 v :: MQ)); attac.
      - smash_eq n n'.
        + hsimpl in *.
          destruct v; attac.
          * destruct MQ1; attac.
            absurd (length MQ1 = length (MQ' ++ e :: MQ1)); attac.
          * destruct MQ1; attac.
            absurd (length MQ1 = length (MQ' ++ TrSend (n, t) v :: e :: MQ1)); attac.
        + hsimpl in *.
          destruct v; attac.
          * destruct MQ1; attac.
            absurd (length MQ1 = length (MQ' ++ e :: MQ1)); attac.
          * destruct MQ1; attac.
            absurd (length MQ1 = length (MQ' ++ TrSend (n', t) v :: e :: MQ1)); attac.
    Qed.


    (* (** Flushing does not add to the front *) *)
    (* Lemma Net_flush_nihil_novi : forall mpath n MN0 MN1 MQ0 M0 S0 M1 S1 MQ' MQs, *)
    (*     Forall (Flushing_NAct n) mpath -> *)
    (*     MQs = flushing_artifact_of n (Net_path_artifacts n mpath) -> *)
    (*     NetMod.get n MN0 = mq MQ0 M0 S0 -> *)
    (*     NetMod.get n MN1 = mq (MQ' ++ MQ0 ++ MQs) M1 S1 -> *)
    (*     (MN0 =[mpath]=> MN1) -> *)
    (*     MQ' = []. *)

    (* Proof. *)
    (*   induction mpath; intros. *)
    (*   1: { destruct MQ'; attac. *)
    (*        destruct MQ0; attac. *)
    (*        absurd (length MQ0 = length (MQ' ++ e :: MQ0)); attac. *)
    (*   } *)

    (*   replace (a::mpath) with ([a] ++ mpath) by auto. *)
    (*   rewrite Net_path_artifacts_app_inv in *. *)
    (*   rewrite flushing_artifact_of_app_inv in *. *)
    (*   subst MQs. *)
    (*   hsimpl in * |-. *)

    (*   rename MN1 into MN2. *)
    (*   rename N1 into MN1. *)
    (*   rename M1 into M2. *)
    (*   rename S1 into S2. *)
    (*   destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?. *)

      (* remember (flushing_artifact_of n (Net_path_artifacts n [a])) as MQe. *)
      (* remember (flushing_artifact_of n (Net_path_artifacts n mpath)) as MQs. *)

      (* consider (exists MQ0' MQ1', MQ0 = MQ0' ++ MQ1' /\ MQ1 = MQ1' ++ MQe) *)
      (*   by (subst; eauto using Net_flush_act_split). *)

    Lemma Net_path_artifact_length : forall mpath n MQ,
        MQ = Net_path_artifacts n mpath ->
        (length MQ <= length mpath)%nat.

    Proof.
      induction mpath; attac.
      destruct a; attac.
      smash_eq n0 n; attac.
      eauto using le_n_S.
    Qed.


    Lemma Flushing_act_NAct : forall a na n,
        Flushing_act a ->
        Some na = lift_act n a ->
        Flushing_NAct n na.

    Proof.
      intros.
      destruct_ma a; attac.
    Qed.

    Lemma Flushing_path_NAct : forall mpath mnpath n,
        Forall Flushing_act mpath ->
        mnpath = lift_path n mpath ->
        Forall (Flushing_NAct n) mnpath.

    Proof.
      induction mpath; attac.
      destruct (lift_act n a) eqn:?; attac.
      - simpl in *.
        rewrite `(_ = Some n0).
        constructor; eauto using Flushing_act_NAct.
      - rewrite `(_ = None).
        attac.
    Qed.


    Lemma lift_flush_mcode_path_Flushing : forall mpath n M,
        mpath = lift_path n (flush_mcode M) ->
        Forall (Flushing_NAct n) mpath.

    Proof.
      intros.
      subst.
      induction M; attac.
      constructor; attac.
    Qed.

    Lemma Event_to_MAct_Flushing : forall e, Flushing_act (Event_to_MAct e).
    Proof. destruct e; attac. Qed.

    Lemma lift_mk_flush_path_Flushing : forall mpath n MQ M,
        mpath = lift_path n (mk_flush_path MQ M) ->
        Forall (Flushing_NAct n) mpath.

    Proof.
      intros. subst.
      destruct M as [h s].
      generalize dependent s.
      induction MQ; attac.
      - eauto using lift_flush_mcode_path_Flushing.
      - simpl in *.
        rewrite lift_path_app_inv in *.
        apply Forall_app.
        split; eauto using lift_flush_mcode_path_Flushing.
        assert (Flushing_act (Event_to_MAct a)) by eauto using Event_to_MAct_Flushing.
        simpl.
        blast_cases; attac; constructor; attac.
    Qed.


    Lemma lift_flush_path_Flushing : forall mpath n MS,
        mpath = lift_path n (flush_path MS) ->
        Forall (Flushing_NAct n) mpath.

    Proof.
      intros.
      destruct MS as [MQ [h s] S].
      simpl in *.
      eauto using lift_mk_flush_path_Flushing.
    Qed.

    Lemma Net_flush_path_Flushing : forall mpath n MN0,
        mpath = Net_flush_path n MN0 ->
        Forall (Flushing_NAct n) mpath.

    Proof.
      intros.
      unfold Net_flush_path in *.
      eauto using lift_flush_path_Flushing.
    Qed.


    Definition sub_flush n MN mpath := exists mpath', mpath ++ mpath' = Net_flush_path n MN.

    Lemma sub_flush_Flushing : forall n MN mpath,
        sub_flush n MN mpath -> Forall (Flushing_NAct n) mpath.
    Proof.
      intros.
      destruct H.
      assert (Forall (Flushing_NAct n) (mpath ++ x)) by eauto using Net_flush_path_Flushing.
      attac.
    Qed.

    Lemma sub_flush_nil : forall n MN0, sub_flush n MN0 [].
    Proof.
      intros.
      exists (Net_flush_path n MN0). attac.
    Qed.

    Lemma sub_flush_inv_l : forall n MN0 mpath0 mpath1,
        sub_flush n MN0 (mpath0 ++ mpath1) ->
        sub_flush n MN0 mpath0.
    Proof.
      intros.
      destruct H.
      exists (mpath1 ++ x).
      rewrite app_assoc. attac.
    Qed.


    Lemma sub_flush_inv_r1 : forall n MN0 MN1 a mpath,
        sub_flush n MN0 (a :: mpath) ->
        (MN0 =(a)=> MN1) ->
        sub_flush n MN1 mpath.

    Proof.
      intros.
      destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.
      destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.
      destruct H as [mpath1 ?].
      assert (Flushing_NAct n a).
      {
        assert (Forall (Flushing_NAct n) ((a :: mpath) ++ mpath1)) by eauto using Net_flush_path_Flushing with LTS.
        attac.
      }

      unfold sub_flush, Net_flush_path in *.
      rewrite `(NetMod.get n MN1 = _) in *.
      rewrite `(NetMod.get n MN0 = _) in *.
      rewrite <- app_comm_cons in *.

      destruct M1 as [h s1].
      destruct a; consider (MN0 =(_)=> _); attac.
      - exists mpath1.
        destruct m; doubt; attac.
        + destruct p; attac.
          destruct n0.
          kill H.
        + destruct a; doubt.
          kill H.
          hsimpl in *.
          simpl in *.
          kill H0.
      - smash_eq n n1.
        + destruct p.
          * kill H.
            hsimpl in *.
            simpl in *.
            rewrite mk_flush_cont_path.
            rewrite lift_path_app_inv.
            kill H0.
            destruct MQ1.
            -- kill H.
               simpl.
               rewrite H0.
               rewrite <- app_assoc.
               eattac.
            -- kill H.
               simpl.
               rewrite H0.
               rewrite <- app_assoc.
               eattac.
          * kill H.
            hsimpl in *.
            simpl in *.
            rewrite mk_flush_cont_path.
            rewrite lift_path_app_inv.
            kill H0.
            destruct MQ1.
            -- kill H.
               simpl.
               rewrite H0.
               rewrite <- app_assoc.
               eattac.
            -- kill H.
               simpl.
               rewrite H0.
               rewrite <- app_assoc.
               eattac.
        + destruct p.
          * kill H.
            hsimpl in *.
            simpl in *.
            destruct MQ1.
            -- kill H0.
               simpl.
               eattac.
            -- kill H0.
               simpl.
               eattac.
          * kill H.
            hsimpl in *.
            simpl in *.
            destruct MQ1.
            -- kill H0.
               simpl.
               eattac.
            -- kill H0.
               simpl.
               eattac.
    Qed.


    Lemma sub_flush_inv_r : forall n MN0 MN1 mpath0 mpath1,
        sub_flush n MN0 (mpath0 ++ mpath1) ->
        (MN0 =[mpath0]=> MN1) ->
        sub_flush n MN1 mpath1.

    Proof.
      intros.
      generalize dependent mpath1 MN0 MN1.
      induction mpath0; attac.
      assert (sub_flush n N1 (mpath0 ++ mpath1)) by eauto using sub_flush_inv_r1.
      eauto.
    Qed.


    Lemma sub_flush_extend : forall n mpath MN0 MN1 MQ0 MQ' M0 S0,
        NetMod.get n MN0 = mq MQ0 M0 S0 ->
        sub_flush n MN0 mpath ->
        sub_flush n (MN1 ::: [n := mq (MQ0 ++ MQ') M0 S0]) mpath.

    Proof.
      induction MQ0; attac.
    Admitted.


    Lemma sub_flush_keep1 : forall n a mpath MN0 MN1 MQ0 MQ1 MQs M0 S0 M1 S1,
        MQs = flushing_artifact_of n (Net_path_artifacts n [a]) ->
        NetMod.get n MN0 = mq (MQ0 ++ MQ1) M0 S0 ->
        NetMod.get n MN1 = mq (MQ1 ++ MQs) M1 S1 ->
        (MN0 =(a)=> MN1) ->
        sub_flush n MN0 (a :: mpath) ->
        sub_flush n (MN1 ::: [n := mq MQ1 M1 S1]) mpath.

    Proof.
      intros.

      assert (Forall (Flushing_NAct n) [a]).
      {
        enough (Forall (Flushing_NAct n) ([a] ++ mpath)) by attac.
        eauto using sub_flush_Flushing.
      }

      assert (Forall (Flushing_NAct n) mpath).
      {
        enough (Forall (Flushing_NAct n) ([a] ++ mpath)) by attac.
        eauto using sub_flush_Flushing.
      }

      unfold sub_flush, Net_flush_path in *.
      rewrite `(NetMod.get n MN0 = _) in *.

      destruct a; consider (MN0 =(_)=> _).
      - hsimpl in *.
        destruct m; attac.
        + destruct p; attac.
          destruct n0.
          destruct MQ0; simpl in *.
          1: absurd (MQ = TrRecv (n0, t) v :: MQ); auto; clear; induction MQ; attac.
          kill H7.
          assert (MQ0 = []). eapply app_self_r'; eauto.
          attac.
        + destruct a; attac.
          destruct MQ0; simpl in *.
          1: absurd (MQ = EvRecv n0 msg :: MQ); auto; clear; induction MQ; attac.
          kill H7.
          assert (MQ0 = []). eapply app_self_r'; eauto.
          attac.
      - hsimpl in *.
        rewrite `(NetMod.get n MN0 = _) in *.
        smash_eq n n1.
        + destruct p; hsimpl in *.
          * assert (MQ0 ++ MQ1 = MQ1). eapply app_inv_l. eauto.
            assert (MQ0 = []). eapply app_self_r'; eauto.
            subst.
            hsimpl in *. simpl in *.
            destruct MQ1; simpl.
            -- simpl in H3.
               kill H3.
               attac.
            -- simpl in H3.
               kill H3.
               attac.
          * rewrite `(TrSend (n, t) v :: MQ1 = [TrSend (n, t) v] ++ MQ1) in H6.
            assert (MQ0 = [TrSend (n, t) v]). eapply app_inv_l. eauto.
            subst.
            simpl in H3.
            kill H3.
            attac.
        + destruct p; hsimpl in *.
          * simpl in *.
            destruct MQ1; simpl in *.
            -- kill H3.
               simpl.
               attac.
            -- kill H3.
               simpl.
               attac.
          * rewrite `(TrSend (n1, t) v :: MQ1 = [TrSend (n1, t) v] ++ MQ1) in H6.
               assert (MQ0 = [TrSend (n1, t) v]). eapply app_inv_l. eauto.
               subst.
               simpl in H3.
               kill H3.
               attac.
    Qed.


    Lemma sub_flush_keep : forall n mpath0 mpath1 MN0 MN1 MQ0 MQs M0 S0 MQ1 M1 S1,
        MQs = flushing_artifact_of n (Net_path_artifacts n mpath0) ->
        NetMod.get n MN0 = mq (MQ0 ++ MQ1) M0 S0 ->
        NetMod.get n MN1 = mq (MQ1 ++ MQs) M1 S1 ->
        (MN0 =[mpath0]=> MN1) ->
        sub_flush n MN0 (mpath0 ++ mpath1) ->
        sub_flush n (MN1 ::: [n := mq MQ1 M1 S1]) mpath1.

    Proof.
      induction mpath0; intros.
      {
        hsimpl in *.
        attac. rewrite <- `(NetMod.get _ _ = _).
        attac.
      }

      assert (Flushing_NAct n a /\ Forall (Flushing_NAct n) (mpath0 ++ mpath1))
        by (eapply Forall_cons_iff; eapply sub_flush_Flushing; eauto).

      replace (a::mpath0) with ([a] ++ mpath0) by auto.
      rewrite Net_path_artifacts_app_inv in *.
      rewrite flushing_artifact_of_app_inv in *.

      subst MQs.

      hsimpl in * |-.
      rename MN1 into MN2.
      rename N1 into MN1.
      rename M1 into M2.
      rename S1 into S2.
      destruct (NetMod.get n MN1) as [MQ1' M1 S1] eqn:?.

      remember (flushing_artifact_of n (Net_path_artifacts n [a])) as MQe.
      remember (flushing_artifact_of n (Net_path_artifacts n mpath0)) as MQs.

      rewrite <- app_comm_cons in *.
      simpl app in *.

      consider (MQ1' = MQ1 ++ MQe). admit.

      (* specialize IHmpath0 with (MN0 := MN1) *)
      (*                          (mpath1 := mpath1) *)
      (*                          (MQs := MQs). *)

      assert (sub_flush n (MN1 ::: [n := mq MQ1 M1 S1]) (mpath0 ++ mpath1)).
      eapply sub_flush_keep1; eauto.

      specialize IHmpath0 with (MN0 := MN1 )(MQ0 := MQ1 ++ MQe)(M0 := M1)(S0 := S1)
                               (MN1 := MN2 )(MQ1 := MQ1)(M1 := M2)(S1 := S2)
                               (MQs := MQs)
                               (mpath1 := mpath1).
      eapply IHmpath0; auto.
    Admitted.


    Lemma Net_flush_cont_iff : forall mpath n MN0 MN1
                                 MQ0 MQ1 M0 S0 M1 S1 MQ' MQa,
        sub_flush n MN0 mpath ->
        MQa = flushing_artifact_of n (Net_path_artifacts n mpath) ->
        NetMod.get n MN0 = mq MQ0 M0 S0 ->
        NetMod.get n MN1 = mq (MQ1 ++ MQa) M1 S1 ->
        (MN0 =[mpath]=> MN1) <->
        (MN0 ::: [n := mq (MQ0 ++ MQ') M0 S0] =[mpath]=> MN1 ::: [n := mq (MQ1 ++ MQ' ++ MQa) M1 S1]).

    Proof.
      induction mpath; intros.
      1: { split; hsimpl in *; attac.
           enough (MN0 = MN1) by attac.
           apply NetMod.extensionality.
           attac.
           enough (NetMod.get n0 (MN0  ::: [ n := mq (MQ0 ++ MQ') M0 S0 ]) = NetMod.get n0 (MN1 ::: [ n := mq (MQ1 ++ MQ') M1 S1 ])).
           {
             smash_eq n n0; attac.
             assert (MQ0 = MQ1). eapply app_inv_l. eauto.
             attac.
           }
           smash_eq n n0; attac.
      }

      assert (Flushing_NAct n a /\ Forall (Flushing_NAct n) mpath)
        by (eapply Forall_cons_iff; eapply sub_flush_Flushing; eauto).

      replace (a::mpath) with ([a] ++ mpath) by auto.
      rewrite Net_path_artifacts_app_inv in *.
      rewrite flushing_artifact_of_app_inv in *.
      subst MQa.

      split; intros.
      - hsimpl in * |-.
        rename MN1 into MN2.
        rename N1 into MN1.
        rename MQ1 into MQ2.
        rename M1 into M2.
        rename S1 into S2.
        destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.

        remember (flushing_artifact_of n (Net_path_artifacts n [a])) as MQe.
        remember (flushing_artifact_of n (Net_path_artifacts n mpath)) as MQs.

        assert (sub_flush n MN0 [a]) by eauto using sub_flush_inv_l.
        assert (sub_flush n MN1 mpath) by eauto using sub_flush_inv_r1.

        consider (exists MQ0' MQ1', MQ0 = MQ0' ++ MQ1' /\ MQ1 = MQ1' ++ MQe /\ length MQ0' = Net_flush_act_consumption a)
          by (subst; eauto using Net_flush_act_split).

        eapply path_seq1 with (N1 := MN1 ::: [n := mq (MQ1' ++ MQ' ++ MQe) M1 S1]).
        1: { eauto using Net_flush_act_cont. }

        replace (MQ2 ++ MQ' ++ MQe ++ MQs) with  (MQ2 ++ (MQ' ++ MQe) ++ MQs) by (now repeat (rewrite app_assoc in * )).

        assert (MN1 ::: [ n := mq (MQ1') M1 S1 ] =[ mpath ]=>
                  MN2 ::: [ n := mq (MQ2 ++ MQs) M2 S2 ]).
        {
          eapply IHmpath with (MQ' := MQe); eauto.
          1: eauto using sub_flush_keep1.
          attac. rewrite app_assoc in H2.
          rewrite NetMod.get_put_eq. eauto.
          repeat (rewrite NetMod.put_put_eq).
          rewrite <- `(NetMod.get n MN1 = _).
          rewrite <- `(NetMod.get n MN2 = _).
          attac.
        }

        assert (MN1 ::: [ n := mq MQ1' M1 S1 ] [ n := mq (MQ1' ++ (MQ' ++ MQe)) M1 S1 ]
                =[ mpath ]=>
                  MN2 ::: [ n := mq (MQ2 ++ MQs) M2 S2 ] [ n := mq (MQ2 ++ (MQ' ++ MQe) ++ MQs) M2 S2 ]
               ).
        {
          eapply IHmpath with
            (MN0 := MN1 ::: [ n := mq MQ1' M1 S1 ])
            (MN1 := MN2 ::: [ n := mq (MQ2 ++ MQs) M2 S2 ]); eauto.
          {
            eauto using sub_flush_keep1.
          }
          attac.
          rewrite NetMod.get_put_eq. repeat (rewrite app_assoc).
          attac.
        }

        attac.

      - hsimpl in * |-.
        rename MN1 into MN2.
        rename N1 into MN1.
        rename MQ1 into MQ2.
        rename M1 into M2.
        rename S1 into S2.
        destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.

        remember (flushing_artifact_of n (Net_path_artifacts n [a])) as MQe.
        remember (flushing_artifact_of n (Net_path_artifacts n mpath)) as MQs.

        assert (sub_flush n MN0 [a]) by eauto using sub_flush_inv_l.
        (* assert (sub_flush n MN1 mpath) by eauto using sub_flush_inv_r1. *)

        consider (exists MQ0' MQ1', MQ0 = MQ0' ++ MQ1' /\ MQ1 = MQ1' ++ MQe /\ length MQ0' = Net_flush_act_consumption a)
          by (subst; eauto using Net_flush_act_split).

        eapply path_seq1 with (N1 := MN1 ::: [n := mq (MQ1' ++ MQ' ++ MQe) M1 S1]).
        1: { eauto using Net_flush_act_cont. }

        replace (MQ2 ++ MQ' ++ MQe ++ MQs) with  (MQ2 ++ (MQ' ++ MQe) ++ MQs) by (now repeat (rewrite app_assoc in * )).

        assert (MN1 ::: [ n := mq (MQ1') M1 S1 ] =[ mpath ]=>
                  MN2 ::: [ n := mq (MQ2 ++ MQs) M2 S2 ]).
        {
          eapply IHmpath with (MQ' := MQe); eauto. admit.
          attac. rewrite app_assoc in H2.
          rewrite NetMod.get_put_eq. eauto.
          repeat (rewrite NetMod.put_put_eq).
          rewrite <- `(NetMod.get n MN1 = _).
          rewrite <- `(NetMod.get n MN2 = _).
          attac.
        }

        assert (MN1 ::: [ n := mq MQ1' M1 S1 ] [ n := mq (MQ1' ++ (MQ' ++ MQe)) M1 S1 ]
                =[ mpath ]=>
                  MN2 ::: [ n := mq (MQ2 ++ MQs) M2 S2 ] [ n := mq (MQ2 ++ (MQ' ++ MQe) ++ MQs) M2 S2 ]
               ).
        {
          eapply IHmpath with
            (MN0 := MN1 ::: [ n := mq MQ1' M1 S1 ])
            (MN1 := MN2 ::: [ n := mq (MQ2 ++ MQs) M2 S2 ]); eauto. admit.
          attac.
          rewrite NetMod.get_put_eq. repeat (rewrite app_assoc).
          attac.
        }

        attac.

          hsimpl.
          hsimpl.
          eapply IHmpath; eauto.
          admit.
          attac.

        eapply IHmpath; eauto.





    Lemma Net_flush_retract : forall mpath n MN0 MN1 MQ0 MQ1 M0 S0 M1 S1 MQ' MQs,
        mpath = Net_flush_path n MN0 ->
        MQs = flushing_artifact_of n (Net_path_artifacts n mpath) ->
        NetMod.get n MN0 = mq (MQ0 ++ MQ') M0 S0 ->
        NetMod.get n MN1 = mq (MQ1 ++ MQ' ++ MQs) M1 S1 ->
        (MN0 =[mpath]=> MN1) ->
        (MN0 ::: [n := mq MQ0 M0 S0] =[mpath]=> MN1 ::: [n := mq (MQ1 ++ MQs) M1 S1]).

    Proof.
      induction mpath; intros.
      {
        hsimpl in *. attac.
      }

      assert (Flushing_NAct n a /\ Forall (Flushing_NAct n) mpath)
        by (eapply Forall_cons_iff; eapply Net_flush_path_Flushing; eauto).

      replace (a::mpath) with ([a] ++ mpath) by auto.
      rewrite Net_path_artifacts_app_inv in *.
      rewrite flushing_artifact_of_app_inv in *.
      subst MQs.

      hsimpl in * |-.
      rename MN1 into MN2.
      rename N1 into MN1.
      rename MQ1 into MQ2.
      rename M1 into M2.
      rename S1 into S2.
      destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.

      remember (flushing_artifact_of n (Net_path_artifacts n [a])) as MQe.
      remember (flushing_artifact_of n (Net_path_artifacts n mpath)) as MQs.

      unfold Net_flush_path in *.
      rewrite `(NetMod.get n MN0 = _) in *.
      simpl flush_path in *.

      destruct MQ0.
      {
        destruct M0 as [h s0].
        consider (exists t n' v, a = NComm n n' t (MValM v)).
        {
          destruct a; attac.
          - destruct s0; attac.
            destruct to; bullshit.
          - destruct p; eattac.
            destruct s0; attac.
            destruct to; bullshit.
        }

        destruct M1 as [h1 s1].
        consider (MQ1 = MQe /\ h1 = h /\ s0 = MSend (n', &t) v s1 /\ S1 = S0).
        {
          consider (MN0 =(_)=> _).
          consider (MN0 ~(_ @ _)~> _).
          consider (_ ~(_ @ _)~> MN1).
          clear IHmpath.
          smash_eq n n'; hsimpl in *.
          - hsimpl. eauto.
          - hsimpl. eauto.
        }

        smash_eq n n'.
        + consider (MQe = [EvRecv (n, t) v]) by attac.
          rewrite `(_ = [EvRecv _ _]) in *.
          apply path_seq1 with (N1:= MN1 ::: [n := mq ([] ++ MQ' ++ [EvRecv (n, t) v]) {|handle:=h; state:=s1|} S0]).
          {
            eauto using Net_flush_act_cont.
          }

      }



    Proof.
      induction mpath; intros.
      1: { hsimpl in *. attac. }

      replace (a::mpath) with ([a] ++ mpath) by auto.
      rewrite Net_path_artifacts_app_inv in *.
      rewrite flushing_artifact_of_app_inv in *.
      subst MQs.

      hsimpl in * |-.
      rename MN1 into MN2.
      rename N1 into MN1.
      rename MQ1 into MQ2.
      rename M1 into M2.
      rename S1 into S2.
      destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.

      remember (flushing_artifact_of n (Net_path_artifacts n [a])) as MQe.
      remember (flushing_artifact_of n (Net_path_artifacts n mpath)) as MQs.


    Lemma Net_flush_cont : forall mpath n MN0 MN1
                             MQ0 MQ1 M0 S0 M1 S1 MQ' MQa,
        mpath = Net_flush_path n MN0 ->
        MQa = flushing_artifact_of n (Net_path_artifacts n mpath) ->
        NetMod.get n MN0 = mq MQ0 M0 S0 ->
        NetMod.get n MN1 = mq (MQ1 ++ MQa) M1 S1 ->
        (MN0 =[mpath]=> MN1) ->
        (MN0 ::: [n := mq (MQ0 ++ MQ') M0 S0] =[mpath]=> MN1 ::: [n := mq (MQ1 ++ MQ' ++ MQa) M1 S1]).

    Proof.
      induction mpath; intros.
      { 1: attac. }

      assert (Flushing_NAct n a /\ Forall (Flushing_NAct n) mpath)
        by (eapply Forall_cons_iff; eapply Net_flush_path_Flushing; eauto).

      replace (a::mpath) with ([a] ++ mpath) by auto.
      rewrite Net_path_artifacts_app_inv in *.
      rewrite flushing_artifact_of_app_inv in *.
      subst MQa.

      hsimpl in * |-.
      rename MN1 into MN2.
      rename N1 into MN1.
      rename MQ1 into MQ2.
      rename M1 into M2.
      rename S1 into S2.
      destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.

      remember (flushing_artifact_of n (Net_path_artifacts n [a])) as MQe.
      remember (flushing_artifact_of n (Net_path_artifacts n mpath)) as MQs.

      unfold Net_flush_path in *.
      rewrite `(NetMod.get n MN0 = _) in *.
      simpl flush_path in *.

      destruct MQ0.
      {
        destruct M0 as [h s0].
        consider (exists t n' v, a = NComm n n' t (MValM v)).
        {
          destruct a; attac.
          - destruct s0; attac.
            destruct to; bullshit.
          - destruct p; eattac.
            destruct s0; attac.
            destruct to; bullshit.
        }

        destruct M1 as [h1 s1].
        consider (MQ1 = MQe /\ h1 = h /\ s0 = MSend (n', &t) v s1 /\ S1 = S0).
        {
          consider (MN0 =(_)=> _).
          consider (MN0 ~(_ @ _)~> _).
          consider (_ ~(_ @ _)~> MN1).
          clear IHmpath.
          smash_eq n n'; hsimpl in *.
          - hsimpl. eauto.
          - hsimpl. eauto.
        }

        smash_eq n n'.
        + consider (MQe = [EvRecv (n, t) v]) by attac.
          rewrite `(_ = [EvRecv _ _]) in *.
          apply path_seq1 with (N1:= MN1 ::: [n := mq ([] ++ MQ' ++ [EvRecv (n, t) v]) {|handle:=h; state:=s1|} S0]).
          {
            eauto using Net_flush_act_cont.
          }

      }

      consider (exists MQ0' MQ1', MQ0 = MQ0' ++ MQ1' /\ MQ1 = MQ1' ++ MQe /\ length MQ0' = Net_flush_act_consumption a)
        by (subst; eauto using Net_flush_act_split).

      eapply path_seq1 with (N1 := MN1 ::: [n := mq (MQ1' ++ MQ' ++ MQe) M1 S1]).
      1: { eauto using Net_flush_act_cont. }

      assert

      assert (MN1 ::: [ n := mq (MQ1' ++ (MQe ++ MQ')) M1 S1 ] =[ mpath ]=>
                MN2 ::: [ n := mq (MQ2 ++ (MQe ++ MQ') ++ MQs) M2 S2 ]).
      eapply IHmpath; eauto.


      eapply IHmpath in H2.
      4: {
        apply Heqm.
      }
      rewrite app_assoc in *.
      eapply H2.

      replace (MQ2 ++ MQ' ++ MQe ++ MQs) with  (MQ2 ++ (MQ' ++ MQe) ++ MQs) by (now repeat (rewrite app_assoc in * )).

      specialize IHmpath with (MQa := MQs)
                              (MQ0 := MQ1')
                              (MQ' := MQ' ++ MQe)
                              (MQ1 := MQ2).
      eapply IHmpath.


      enough (MN1 ::: [n := mq (MQ1') M1 S1] ::: [ n := mq (MQ1' ++ MQ' ++ MQe) M1 S1 ] =[ mpath ]=>
            MN2 ::: [ n := mq (MQ2 ++ MQ' ++ MQe ++ MQs) M2 S2 ]).
      eattac.

      eapply IHmpath; eauto. admit.





      assert (MN0 ::: [n := mq MQ0' M0 S0] =(a)=> MN1 ::: [n := mq ([] ++ MQe) M1 S1]).
      {
        replace (mq (MQ1' ++ MQe) M1 S1) with (mq ([] ++ MQ1' ++ MQe) M1 S1) by auto.
        eauto using Net_flush_act_retract.
      }

      assert (MN0 ::: [n := mq (MQ0' ++ (MQ1' ++ MQ')) M0 S0] =(a)=>
                MN1 ::: [n := mq ([] ++ (MQ1' ++ MQ') ++ MQe) M1 S1]).
      {
        enough (MN0 :::  [ n := mq MQ0' M0 S0 ] ::: [n := mq (MQ0' ++ (MQ1' ++ MQ')) M0 S0]
                =(a)=>
                  MN1 ::: [ n := mq ([] ++ MQe) M1 S1 ] ::: [n := mq ([] ++ (MQ1' ++ MQ') ++ MQe) M1 S1]) by attac.
        eapply Net_flush_act_cont; attac.
      } simpl app in *.




      assert (MN0 ::: [n := mq (MQ0 ++ MQ') M0 S0] =(a)=> MN1 ::: [n := mq (MQ1 ++ MQ') M0 S0]) by eauto using Net_flush_act_cont.


      eapply path_seq1 with (N1 := MN1 ::: [n := mq (MQ1' ++ MQ' ++ MQe) M1 S1]).
      1: { eauto using Net_flush_act_cont. }

      destruct M0 as [h s].

      destruct MQ0'; simpl in *.
      {
        destruct a; hsimpl in *.
        - consider (MN0 =(NTau _ _)=> _).
          destruct m; doubt; attac.
          * destruct p; attac.
            destruct n0.
            absurd (MQ = TrRecv (n0, t) v :: MQ); eauto.
            clear. induction MQ; attac.
          * destruct a; try (contradiction).
            consider (_ =(MActM Tau)=> _).
            absurd (MQ = EvRecv n0 msg :: MQ); eauto.
            clear. induction MQ; attac.
        - consider (MN0 =(NComm _ _ t p)=> MN1).
          smash_eq n n1; attac.
          * rewrite `(NetMod.get n MN0 = _) in *.
            destruct p.
            -- consider (_ =(MActM _)=> _).
               consider (_ =(MActM _)=> _).
               erewrite `(MVal_to_Event (n, t) ^ m :: _ = [MVal_to_Event (n, t) ^ m] ++ _) in *; eauto.
               erewrite `(MVal_to_Event (n, t) ^ m :: _ = [MVal_to_Event (n, t) ^ m] ++ _) in *; eauto.
               eapply IHmpath.
               
               eapply IHmpath.
               absurd (MQ0 = TrSend (n, t) v :: MQ0); eauto.
               clear. induction MQ0; attac.
          * rewrite `(NetMod.get n MN0 = _) in *.


      }

      destruct MQ0', s; simpl in *.
      - destruct a; hsimpl in *.
        + consider (MN0 =(NTau _ _)=> MN1).
          destruct m; doubt; attac.
          * destruct p; attac.
            destruct n0.
            absurd (MQ = TrRecv (n0, t) v :: MQ); eauto.
            clear. induction MQ; attac.
          * destruct a; try (contradiction).
            consider (_ =(MActM Tau)=> _).
            absurd (MQ = EvRecv n0 msg :: MQ); eauto.
            clear. induction MQ; attac.
        + consider (MN0 =(NComm _ _ t p)=> MN1).
          smash_eq n n1; attac.
          * rewrite `(NetMod.get n MN0 = _) in *.
            destruct p.
            -- hsimpl in *; bullshit.
            -- consider (&S =(_)=> _).
               consider (_ =(MActT _)=> _).
               absurd (MQ0 = TrSend (n, t) v :: MQ0); eauto.
               clear. induction MQ0; attac.
          * rewrite `(NetMod.get n MN0 = _) in *.

            destruct p.
            -- hsimpl in *; bullshit.
            -- consider (_ =(MActT _)=> _).
               absurd (MQ = TrSend (n1, t) v :: MQ); eauto.
               clear. induction MQ; attac.
      - destruct a; hsimpl in *.
        + consider (MN0 =(NTau _ _)=> MN1).
          destruct m; doubt; attac.
          * destruct p; attac.
          * destruct a; try (contradiction).
            consider (_ =(MActM Tau)=> _); bullshit.
        + consider (MN0 =(NComm _ _ t p)=> MN1).
          smash_eq n n1; attac.
          * rewrite `(NetMod.get n MN0 = _) in *.
            destruct p.
            -- consider (_ =(MActM _)=> _).
               consider (_ =(MActM _)=> _).

            -- consider (&S =(_)=> _).
               consider (_ =(MActT _)=> _).
               absurd (MQ0 = TrSend (n, t) v :: MQ0); eauto.
               clear. induction MQ0; attac.
          * rewrite `(NetMod.get n MN0 = _) in *.

            destruct p.
            -- hsimpl in *; bullshit.
            -- consider (_ =(MActT _)=> _).
               absurd (MQ = TrSend (n1, t) v :: MQ); eauto.
               clear. induction MQ; attac.


      eapply path_seq1 with (N1 := MN1 ::: [n := mq (MQ1' ++ MQ' ++ MQe) M1 S1]).
      1: { eauto using Net_flush_act_cont. }

      specialize IHmpath with (MQa := MQs)
                              (MQ0 := MQ1')
                              (MQ' := MQ' ++ MQe)
                              (MQ1 := MQ2).

      replace (MQ2 ++ MQ' ++ MQe ++ MQs) with  (MQ2 ++ (MQ' ++ MQe) ++ MQs) by (now repeat (rewrite app_assoc in * )).
      eapply IHmpath; eauto.



      apply IHmpath; eauto.


      destruct MQ0.
      - consider (exists MQ0' MQ1',
                     [] = MQ0' ++ MQ1' /\
                       MQ1 = MQ1' ++ MQe
                 ) by (subst; eauto using Net_flush_act_split).

        eapply path_seq1 with (N1 := MN1 ::: [n := mq (MQ1' ++ MQ' ++ MQe) M1 S1]).
        1: { eauto using Net_flush_act_cont. }

        destruct (app_eq_nil MQ0' MQ1'); auto. subst MQ0' MQ1'.
        simpl app in *.


        replace (MQ2 ++ MQ' ++ MQe ++ MQs) with  (MQ2 ++ (MQ' ++ MQe) ++ MQs) by (now repeat (rewrite app_assoc in * )).

        specialize IHmpath with (MQa := MQs)
                                (MQ0 := [])
                                (MQ' := MQ' ++ MQe)
                                (MQ1 := MQ2).
        simpl app in *.
        eapply IHmpath; eauto.
                                  ()
                                (MQ1 := MQ2 ++ MQe).

                                (MN1 := MN2)
                                (MN0 := MN1).

        replace (MQ2 ++ MQ' ++ MQe ++ MQs) with  (MQ2 ++ (MQ' ++ MQe) ++ MQs) by (now repeat (rewrite app_assoc in * )).


        replace (MQ2 ++ MQe ++ MQs) with ((MQ2 ++ MQe) ++ MQs) by (now rewrite app_assoc).
        eapply IHmpath.

      consider (exists MQ0' MQ1',
                   MQ0 = MQ0' ++ MQ1' /\
                     MQ1 = MQ1' ++ MQe
               ) by (subst; eauto using Net_flush_act_split).

      eapply path_seq1 with (N1 := MN1 ::: [n := mq (MQ1' ++ MQ' ++ MQe) M1 S1]).
      1: { eauto using Net_flush_act_cont. }


      destruct MQ0.
      - hsimpl in *.
        consider (_ =(a)=> _); attac.
        + admit.
        + destruct v; attac.
          smash_eq n n'; attac.




      enough (MN1 ::: [ n := mq (MQ1') M1 S1 ] =[ mpath ]=>
                MN2 ::: [ n := mq (MQ2 ++ MQs) M2 S2 ]).
      eapply IHmpath.

      specialize IHmpath with (MN0 := MN1)(MN1 := MN2)(MQ' := MQ' ++ MQe)(MQa := MQs).
      repeat (rewrite <- app_assoc in IHmpath).
      apply IHmpath; auto.


    Lemma Net_flush_retract : forall mpath n MN0 MN1 MQ0 MQ1 M0 S0 M1 S1 MQ' MQs,
        Forall (Flushing_NAct n) mpath ->
        MQs = flushing_artifact_of n (Net_path_artifacts n mpath) ->
        NetMod.get n MN0 = mq (MQ0 ++ MQ') M0 S0 ->
        NetMod.get n MN1 = mq (MQ1 ++ MQ' ++ MQs) M1 S1 ->
        (MN0 =[mpath]=> MN1) ->
        (MN0 ::: [n := mq MQ0 M0 S0] =[mpath]=> MN1 ::: [n := mq (MQ1 ++ MQs) M1 S1]).

    Proof.
      induction mpath; intros.
      1: { hsimpl in *. attac. }

      replace (a::mpath) with ([a] ++ mpath) by auto.
      rewrite Net_path_artifacts_app_inv in *.
      rewrite flushing_artifact_of_app_inv in *.
      subst MQs.

      hsimpl in * |-.
      rename MN1 into MN2.
      rename N1 into MN1.
      rename MQ1 into MQ2.
      rename M1 into M2.
      rename S1 into S2.
      destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.

      remember (flushing_artifact_of n (Net_path_artifacts n [a])) as MQe.
      remember (flushing_artifact_of n (Net_path_artifacts n mpath)) as MQs.

      destruct MQ0.
      - simpl app in *.
        consider (exists MQ0' MQ1',
                     [] ++ MQ' = MQ0' ++ MQ1' /\
                       MQ1 = MQ1' ++ MQe
                 ) by (subst; eauto using Net_flush_act_split).
        simpl app in *.

        assert (MN0 ::: [n := mq MQ0' M0 S0] =(a)=> MN1 ::: [n := mq ([] ++ MQe) M1 S1]).
        {
          replace (mq (MQ1' ++ MQe) M1 S1) with (mq ([] ++ MQ1' ++ MQe) M1 S1) by auto.
          eauto using Net_flush_act_retract.
        } simpl app in *.


        assert (MQ1 = []).
        {
          consider (exists MQ0' MQ1',
                       [] ++ MQ' = MQ0' ++ MQ1' /\
                         MQ1 = MQ1' ++ MQe
                   ) by (subst; eauto using Net_flush_act_split).
          simpl app in *.

          destruct MQ0'.
          + simpl app in *.
            assert (MQ1' = []). eapply Net_flush_act_nihil_novi; eauto.




      rewrite `(MQ0 ++ _ = _) in *.


      consider (exists MQ0'' MQ1'', MQ0 = MQ0' ++ MQ0'' /\ MQ1' = MQ1'' ++ MQ').
      {
        clear IHmpath.
        assert (MQ0' = [] \/ exists e, MQ0' = [e]) as [|].
        {
          destruct a; hsimpl in *; blast_cases; doubt; attac.
          - consider (_ =(NTau _ _)=> _); hsimpl in *; blast_cases; attac.
            destruct MQ0'; attac.
          - consider (_ =(NTau _ _)=> _); hsimpl in *; blast_cases; attac.
            destruct MQ0'; attac.
          - destruct MQ0'; attac.
            enough (MQ0' = []) by attac.
            consider (MN0 =(NComm _ _ _ _)=> MN1); hsimpl in *; blast_cases; hsimpl in *; attac.
            + absurd (MQ1' = (e :: (MQ0' ++ MQ1'))); try (eapply app_inv_l; attac).
              clear.
              destruct MQ1'; attac.
              replace (e::MQ1') with ([e] ++ MQ1') by auto.
              rewrite app_assoc in *.
              absurd ([] ++ MQ1' = (MQ0' ++ [e]) ++ MQ1'); auto.
              intros ?.
              absurd ([] = (MQ0' ++ [e])); attac.

            + absurd (MQ1' = (e :: (MQ0' ++ MQ1'))); try (eapply app_inv_l; attac).
              clear.
              destruct MQ1'; attac.
              replace (e::MQ1') with ([e] ++ MQ1') by auto.
              rewrite app_assoc in *.
              absurd ([] ++ MQ1' = (MQ0' ++ [e]) ++ MQ1'); auto.
              intros ?.
              absurd ([] = (MQ0' ++ [e])); attac.
        }
        - subst; hsimpl in *.
          exists MQ0, MQ0.
          attac.
        - destruct MQ0.
          2: { attac. }
          hsimpl in *.
          exfalso.
          destruct MQ1'; attac.
          + consider (MN0 =(a)=> MN1); hsimpl in *; attac.
            * destruct a0; attac.
              destruct p; attac.
            consider (&S = mq MQ1' M1 S1) by (consider (NetMod.get n _ =(a0)=> &S); attac).
            consider (NetMod.get n _ =(a0)=> _); attac.


        assert (MQe = [] \/ exists e, MQe = [e]) as [|] by (destruct a; doubt; hsimpl in *; attac; smash_eq n n1; attac).
        - subst.
        destruct a; subst; hsimpl in *.
        - destruct m; attac.
          + destruct p; attac.
            consider (MN0 =(NTau n _)=> MN1); attac.
            replace (TrRecv n0 v :: MQ1') with ([TrRecv n0 v] ++ MQ1') by auto.
            consider (MQ0' = [TrRecv n0 v]) by (eapply app_inv_l; eauto).
            destruct MQ0; attac.
            consider (_ =(NTau n _)=> _); attac.
            admit.
          + consider (MN0 =(NTau n _)=> MN1); attac.
          + consider (MN0 =(NTau n _)=> MN1); attac.
            destruct a; attac.
            replace (EvRecv n0 msg :: MQ) with ([EvRecv n0 msg] ++ MQ) by auto.
            consider (MQ0' = [EvRecv n0 msg]) by (eapply app_inv_l; eauto).
            destruct MQ0; attac.
            admit.
        - consider (_ =(NComm _ _ t p)=> MN1).
          attac.
          destruct p; attac.
          + smash_eq n n1; attac.
            kill H6.
            attac.
            destruct M1; attac.
            destruct M; attac.
            destruct MQ; attac.
          + smash_eq n n1; attac.
            * kill H6; attac.
              destruct MQ0; attac.
              destruct M1; attac.
              destruct M; attac.
              rewrite NetMod.put_put_neq in *; auto.
            hsimpl in *.
            smash_eq n n1.

      }


      assert (MN0 ::: [n := mq MQ0' M0 S0] =(a)=> MN1 ::: [n := mq ([] ++ MQe) M1 S1]).
      {
        replace (mq (MQ1' ++ MQe) M1 S1) with (mq ([] ++ MQ1' ++ MQe) M1 S1) by auto.
        eauto using Net_flush_act_retract.
      } simpl app in *.

      
      assert (MQ0 = MQ0' ++ )

      assert (MN0 ::: [n := mq MQ0' M0 S0] =(a)=> MN1 ::: [n := mq ([] ++ MQe) M1 S1]).
      {
        replace (mq (MQ1' ++ MQe) M1 S1) with (mq ([] ++ MQ1' ++ MQe) M1 S1) by auto.
        eauto using Net_flush_act_retract.
      } simpl app in *.


      rewrite `(MQ0 ++ _ = _) in *.
      assert (MN0 ::: [n := mq MQ0' M0 S0] =(a)=> MN1 ::: [n := mq ([] ++ MQe) M1 S1]).
      {
        replace (mq (MQ1' ++ MQe) M1 S1) with (mq ([] ++ MQ1' ++ MQe) M1 S1) by auto.
        eauto using Net_flush_act_retract.
      } simpl app in *.

      assert (exists MQ0'', MQ1' = MQ0'' ++ MQ').
      {
        destruct a; hsimpl in *; attac.
        - kill H6; attac.
          consider (&S = mq [] M1 S1) by (enough (NetMod.get n (MN1 ::: [ n := mq [] M1 S1 ]) = NetMod.get n (MN0 ::: [ n := &S ])); attac).

          destruct m; attac.
          + kill H9. attac. destruct MQ0; attac.
            kill H3.
            attac.
      }


      assert (MN0 ::: [n := MQ0 M0 S0] =(a)=> MN1 ::: [n := MQ1 ]).


      eapply path_seq1 with (N1 := MN1 ::: [n := mq (MQ0' ++ MQe) M1 S1]).
      1: { eauto using Net_flush_act_retract. }






      replace (flushing_artifact_of n
                 match a with
                 | NTau _ _ => Net_path_artifacts n mpath
                 | NComm n0 n1 t v =>
                     if NAME.eqb n0 n
                     then (n1, MVal_to_Event (n, t) v) :: Net_path_artifacts n mpath
                     else Net_path_artifacts n mpath
                 end) with (MQe ++ MQs).
                           admit. destruct a; subst. attac.

      specialize IHmpath with (MN0 := MN1)(MN1 := MN2).

      assert (MN1 ::: [ n := mq (MQ1' ++ MQe) M1 S1] =[mpath]=> MN2 ::: [ n := mq (MQ2 ++ MQe ++ MQs) M1 S1 ]).
      specialize IHmpath; eauto. subst. auto. attac.

      specialize IHmpath with
        (MQ)


      assert (MN0 ::: [n := mq (MQ0' ++ MQe) M0 S0] =(a)=> MN1 ::: [n := mq (MQ1 ++ MQe) M1 S1]).
      (* { *)
      (*   replace (mq (MQ1' ++ MQe) M1 S1) with (mq ([] ++ MQ1' ++ MQe) M1 S1) by auto. *)
      (*   eauto using Net_flush_act_retract. *)
      (* } *)



      assert (MN0 ::: [n := mq MQ0' M0 S0] =(a)=> MN1 ::: [n := mq ([] ++ MQe) M1 S1]).
      {
        replace (mq (MQ1' ++ MQe) M1 S1) with (mq ([] ++ MQ1' ++ MQe) M1 S1) by auto.
        eauto using Net_flush_act_retract.
      }

      eapply IHmpath in H4.

      specialize IHmpath with (MN0 := MN1 ::: [n := mq MQe M1 S1])
                              (MN1 := MN2)
                              (MQ0 := MQe).

      assert (MN1 ::: [ n := mq MQe M1 S1 ] [ n := mq (MQ0 ++ MQ') M0 S0 ] =[ mpath ]=>
                MN2 ::: [ n0 := mq (MQ1 ++ MQ' ++ MQa) M2 S2 ]).

      assert ((MN0 ::: [n := mq MQ0' M0 S0] =(a)=> MN1 ::: [n := mq ( ++ MQ' ++ e) M1 S1])).



    Lemma Net_flush_split : forall mpath n MN0 MN1 MQ0 MQ1 M0 S0 M1 S1,
        Forall (Flushing_NAct n) mpath ->
        NetMod.get n MN0 = mq MQ0 M0 S0 ->
        NetMod.get n MN1 = mq MQ1 M1 S1 ->
        (MN0 =[mpath]=> MN1) ->
        exists MQ0' MQ1',
          MQ0 = MQ0' ++ MQ1' /\
          MQ1 = MQ1' ++ flushing_artifact_of n (Net_path_artifacts n mpath).

    Proof.
      induction mpath; intros.
      1: { exists []; eattac. }

      replace (a :: mpath) with ([a] ++ mpath) by auto.
      rewrite Net_path_artifacts_app_inv.
      rewrite flushing_artifact_of_app_inv.

      hsimpl in * |-.

      rename MN1 into MN2.
      rename N1 into MN1.
      rename MQ1 into MQ2.
      rename M1 into M2.
      rename S1 into S2.
      destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.

      specialize IHmpath with (MN0 := MN1).

      remember (flushing_artifact_of n (Net_path_artifacts n [a])) as MQe.
      consider (exists MQ0' MQ1',
                   MQ0 = MQ0' ++ MQ1' /\
                     MQ1 = MQ1' ++ MQe
               ) by (subst; eauto using Net_flush_act_split).

      assert (MN0 ::: [n := mq MQ0' M0 S0] =(a)=> MN1 ::: [n := mq ([] ++ MQe) M1 S1]).
      {
        replace (mq (MQ1' ++ MQe) M1 S1) with (mq ([] ++ MQ1' ++ MQe) M1 S1) by auto.
        eauto using Net_flush_act_retract.
      }

      kill H5.
      - attac.
        hsimpl in *.
        assert (&S = mq [] M1 S1).
        enough (NetMod.get n (MN1 ::: [ n := mq [] M1 S1 ]) = NetMod.get n (MN0 ::: [ n := &S ])). attac. attac.
        subst. attac.
        destruct a0; attac.
        + destruct p; attac.


      remember (flushing_artifact_of n (Net_path_artifacts n mpath)) as MQs.
      consider (exists MQ1'' MQ2',
                   MQ1' ++ MQe = MQ1'' ++ MQ2' /\
                     MQ2 = MQ2' ++ MQs) by eattac; clear IHmpath.


      remember (flushing_artifact_of n (Net_path_artifacts n mpath)) as MQs.
      consider (exists MQ1'' MQ2',
                   MQ1' ++ MQe = MQ1'' ++ MQ2' /\
                     MQ2 = MQ2' ++ MQs) by eattac; clear IHmpath.

      enough (exists MQ0'0 MQ1'0, MQ0' ++ MQ1' = MQ0'0 ++ MQ1'0 /\ MQ2' = MQ1'0 ++ MQe) by attac.

      rewrite `(MQ1' ++ MQe = _) in *.
      destruct a; attac; attac.
      smash_eq n n1; attac.
      destruct MQ2'.
      - hsimpl in *; simpl in *.
        assert (MQ0' = []).
        destruct MQ0'; attac.
        consider (_ =(NComm _ _ _ _)=> _); compat_hsimpl in *. attac. destruct p; attac.
      enough (exists X0 X1 X2 X3, MQ0' = X0 ++ X2 )
      (*
        MQ0'  MQ1'    MQ2'
        MQ0'0 MQ1'0   MQ1'0 MQe
       *)

      assert (MN1 ::: [n := mq (MQ0' ++ MQ1' ++ MQ)])


      assert (MN0 ::: [n := mq (MQ0' ++ MQ1') M0 S0] =(a)=> MN1 ::: [n := mq (MQ1' ++ MQ' ++ e) M1 S1]).

      destruct a; attac; attac.
      smash_eq n n1; attac.

      destruct p; attac.
      - destruct MQ2'; attac.
        +
        assert (exists MQ2'', MQ2' = MQ2' ++ [EvRecv (n, t) m])
        generalize dependent MQ1'' MQ2'.
        induction MQ; attac.
        + destruct MQ1'', MQ2'; eattac.
          exists [], [].

        }
        attac.

      consider (exists MQ1'' MQ2',
                   MQ1 = MQ1'' ++ MQ2' /\
                     MQ2 = MQ2' ++ flushing_artifact_of n (Net_path_artifacts n mpath)) by eattac.

      consider (exists MQ0' MQ1',
                   MQ0 = MQ0' ++ MQ1' /\
                     (MQ1'' ++ MQ2') = MQ1' ++ flushing_artifact_of n (Net_path_artifacts n [a])
               ) by eauto using Net_flush_act_split.

      destruct a; attac; attac.
      smash_eq n n1; attac.


      enough (exists MQ0'0 MQ1'0,
                 MQ0' ++ MQ1' = MQ0'0 ++ MQ1'0 /\
                 MQ2' = MQ1'0 ++ flushing_artifact_of n
                                      match a with
                                      | NTau _ _ => []
                                      | NComm n0 n1 t v => if NAME.eqb n0 n then [(n1, MVal_to_Event (n, t) v)] else []
                                      end ) by attac.


      consider (exists MQ1'' MQ2',
                   MQ1 = MQ1'' ++ MQ2' /\
                   MQ2 = MQ2' ++ flushing_artifact_of n (Net_path_artifacts n mpath)) by eattac.

      consider (exists MQ0' MQ1',
                   MQ0 = MQ0' ++ MQ1' /\
                     (MQ1'' ++ MQ2') = MQ1' ++ flushing_artifact_of n (Net_path_artifacts n [a])
               ) by eauto using Net_flush_act_split.

      exists (MQ0'' ++ MQ1').

      eattac.
    Qed.



    Lemma Net_flush_go : forall n MN0,
        MN0 =[Net_flush_path n MN0]=> Net_flush_target n MN0.

    Proof.
      intros.

      destruct (NetMod.get n (Net_flush_target n MN0)) as [MQx Mx Sx] eqn:?.

      unfold Net_flush_target in *.
      rewrite <- Net_path_flushing_artifacts_eq.
      unfold Net_flush_path.

      destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.

      generalize dependent M0 S0 MN0.
      induction MQ0; attac.
      - assert (MN0 =[Net_flush_M_path n MN0]=> Net_flush_M_target n MN0) by eauto using Net_flush_M_go.
        unfold Net_flush_M_target in *.
        rewrite <- Net_path_flushing_M_artifacts_eq in *.
        unfold Net_flush_M_path in *.
        now rewrite `(NetMod.get n MN0 = _) in *.
      - rewrite lift_path_app_inv.
        rewrite Net_path_artifacts_app_inv.
        rewrite apply_artifacts_app_inv.
        (* unfold Net_flushing_artifacts. *)

        pose (MN1 := Net_flush_M_target n MN0).

        apply path_seq with (P2:=MN1).
        + assert (MN0 =[Net_flush_M_path n MN0]=> Net_flush_M_target n MN0) by eauto using Net_flush_M_go.
          unfold Net_flush_M_target in *.
          unfold Net_flush_M_path in *.
          subst MN1.
          now rewrite `(NetMod.get n MN0 = _) in *.
        + destruct M0 as [h s0].
          destruct (NetMod.get n MN1) as [MQ1 [h1 s1] S1] eqn:?.

          assert (S1 = S0 /\ {|handle:=h1; state:=s1|} = {| handle := h; state := MRecv (next_state s0) |} /\ MQ1 = (a :: MQ0) ++ flushing_artifact_of n (Net_flushing_M_artifacts n MN0)).
          {
            subst MN1.
            unfold Net_flushing_M_artifacts, Net_flush_M_target in *.
            hrewrite (NetMod.get n MN0) in *.
            simpl next_state; simpl handle.
            simpl next_state in *. simpl handle in *.

            assert (NetMod.get n (MN0 ::: [ n := mq (a :: MQ0)
                                                    {| handle := h; state := MRecv (next_state s0) |} S0 ])
                    = mq (a :: MQ0)
                         {| handle := h; state := MRecv (next_state s0) |} S0
                   ) by attac.
            assert (S1 = S0) by eauto using apply_artifacts_inv_S with LTS.
            assert ({|handle:=h1; state:=s1|} = {| handle := h; state := MRecv (next_state s0) |}) by eauto using apply_artifacts_inv_M with LTS.
            eassert (MQ1 = (a :: MQ0) ++ flushing_artifact_of n _) by eauto using apply_artifacts_inv_MQ with LTS.
            unfold Net_flushing_M_artifacts, Net_flush_M_target in *.
            repeat split; auto.
            hrewrite (NetMod.get n MN0) in *.
            simpl next_state; simpl handle.
            attac.
          }

          pose (MN1' := NetMod.put n (mq (MQ0 ++ flushing_artifact_of n (flushing_M_artifacts n s0)) {|handle:=h; state:=h1 a (next_state s1) |} S0) MN1).

          destruct a; attac; attac.
          * destruct (NetMod.get n1 MN1') as [MQ1' M1' S1'] eqn:?.
            pose (MN2 := NetMod.put n1 (mq (MQ1' ++ [TrRecv (n, t) v]) M1' S1') MN1').
            unfold Net_flushing_M_artifacts, Net_flush_M_target in *.
            apply path_seq1 with (N1:=MN2).
            1: { constructor 2 with (N0':=MN1'); attac. }

            pose (MN2' := NetMod.put n1 (mq MQ0 M1' S1') MN1').
            specialize (IHMQ0 MN2').
            smash_eq n n1.
            -- specialize (IHMQ0 S1' M1').
               assert (S1' = S0) by (subst MN1 MN1'; attac).
               (* eassert (M1' = {|handle:=_; state:=_|}) by (subst MN1 MN1'; attac). *)
               assert (MQ1' = MQ0 ++ flushing_artifact_of n (flushing_M_artifacts n s0)) by (subst MN1 MN1'; attac).
               subst.
               specialize (IHMQ0 ltac:(subst MN1 MN1' MN2'; attac)).


              assert (Forall Flushing_act (lift_path n (mk_flush_path MQ0 M1'))).
              hsimpl in *.

               subst MN1 MN1' MN2'.
               hsimpl in *.
               simpl in *.
               unfold Net_path_artifacts, Net_flushing_M_artifacts in *.
               hsimpl in *.



               assert (flushing_artifact_of n (flushing_M_artifacts n s0) [TrRecv (n, t) v] = []).
               simpl in *.
               specialize (IHMQ0 ltac:(eattac) ltac:(eattac) ltac:(eattac)).
            -- 






    Definition lift_act (n : Name) (a : MAct) : option MNAct :=
      match a with
      | MActM (Send (n', t) v) => Some (NComm n n' t ^ v)
      | MActT (Send (n', t) v) => Some (NComm n n' t # v)
      | MActP v => Some (NTau n a)
      | MActM Tau => Some (NTau n a)
      | MActT Tau => Some (NTau n a)
      | _ => None
      end.


    Definition lift_path (n : Name) (mpath : )

    Definition lift_flushing (n : Name) (a : MAct) : Flushing_act a -> MNAct.
      intros.
      refine '(
          match a as a' return a = a' -> MNAct with
          | MActM (Send (n', t) v) => fun e => NComm n n' t ^ v
          | MActT (Send (n', t) v) => fun e => NComm n n' t # v
          | MActP v => fun e => NTau n a
          | MActM Tau => fun e => NTau n a
          | MActT Tau => fun e => NTau n a
          | _ => fun e => _
          end eq_refl
        ); bullshit.
    Defined.


    Lemma lift_flushing_Flushing : forall n a (HF : Flushing_act a),
        Flushing_NAct n (lift_flushing n a HF).

    Proof.
      intros.
      destruct_ma a; attac.
    Qed.


    Definition lower_flushing (na : MNAct) : MAct :=
      match na with
      | NComm n n' t (MValM v) => MActM (Send (n', t) v)
      | NComm n n' t (MValP v) => MActT (Send (n', t) v)
      | NTau n a => a
      end.


    Definition lower_flushing_artifact (n : Name) (na : MNAct) : list Event :=
      match na with
      | NComm n0 n1 t (MValM v) => if NAME.eqb n n1 then [EvRecv (n0, t) v] else []
      | NComm n0 n1 t (MValP v) => if NAME.eqb n n1 then [TrRecv (n0, t) v] else []
      | _ => []
      end.


    Lemma lift_flushing_irrelevance : forall n a (HF HF' : Flushing_act a),
        lift_flushing n a HF = lift_flushing n a HF'.

    Proof. intros; destruct_ma a; attac. Qed.

    Hint Resolve lift_flushing_irrelevance : LTS.


    Lemma lower_flushing_Flushing : forall n na,
        Flushing_NAct n na ->
        Flushing_act (lower_flushing na).

    Proof. intros. destruct_mna na; attac. Qed.


    Lemma lower_flushing_path_Flushing : forall n mpath,
        Forall (Flushing_NAct n) mpath ->
        Forall Flushing_act (List.map lower_flushing mpath).

    Proof.
      induction mpath; attac.
      split; eauto using lower_flushing_Flushing with LTS.
    Qed.

    Hint Resolve lower_flushing_Flushing lower_flushing_path_Flushing : LTS.


    Lemma lower_lift_flushing n a (HF : Flushing_act a) :
        lower_flushing (lift_flushing n a HF) = a.
    Proof. intros. destruct_ma a; attac. Qed.

    Lemma lift_lower_flushing n a (HF : Flushing_act (lower_flushing a)) :
      Flushing_NAct n a ->
      lift_flushing n (lower_flushing a) HF = a.
    Proof. intros. destruct_mna a; attac. Qed.

    Hint Rewrite -> @lower_lift_flushing @lift_lower_flushing using spank : LTS LTS_concl.

    Hint Extern 10 (NetMod.get _ _ =(_)=> _) =>
           ltac2:(match! goal with
                  | [h : NetMod.get _ _ = ?c |- _] =>
                      let hh := hyp h in
                      rewrite $hh
                  end
                 ) : LTS.

    (** If a node can perform a flushing action, then the network can too. *)
    Lemma Flushing_act_available : forall [ma] [MS1] n MN0 (HF : Flushing_act ma),
        (NetMod.get n MN0 =(ma)=> MS1) ->
        exists MN1, (MN0 =(lift_flushing n ma HF)=> MN1).

    Proof.
      intros.
      destruct MS1 as [MQ1 M1 S1].
      consider (_ =(_)=> _); attac.
      - smash_eq n n1.
        + exists (NetMod.put n ( mq (MQ1 ++ [EvRecv (n, t) msg]) M1 S1) MN0).
          destruct M1.
          eapply NTrans_Comm_eq_inv; eattac.
        + destruct (NetMod.get n1 MN0) as [MQ' M' S'] eqn:?.
          exists (NetMod.put n1 (mq (MQ' ++ [EvRecv (n, t) msg]) M' S') (NetMod.put n (mq MQ1 M1 S1) MN0)); eattac.
          destruct M1.
          eapply NTrans_Comm_neq_inv; eattac.
      - eexists (NetMod.put n (mq MQ1 {|handle:=h; state:=h (EvRecv n0 v) s|} S1) MN0); eattac 15.
      - smash_eq n n1; attac.
        + exists (NetMod.put n (mq (MQ1 ++ [TrRecv (n, t) v]) {|handle:=h; state:=h (TrSend (n, t) v) s|} S1) MN0); eattac.
          eapply NTrans_Comm_eq_inv.
          eexists _, _.
          rewrite `(NetMod.get _ _ = _).
          eattac.
        + destruct (NetMod.get n1 MN0) as [MQ' M' S'] eqn:?.
          exists (NetMod.put n1 (mq (MQ' ++ [TrRecv (n, t) v]) M' S') (NetMod.put n (mq MQ1 {| handle := h; state := h (TrSend (n1, t) v) s |} S1) MN0)); eattac.
          eapply NTrans_Comm_neq_inv; eattac.
      - eexists (NetMod.put n (mq MQ1 {| handle := h; state := h (TrRecv n0 v) s |} _) MN0); eattac 15.
    Qed.


    Lemma Flushing_act_get_eq : forall ma MN0 MN1 n MQ1 M1 S1,
        Flushing_NAct n ma ->
        (MN0 =(ma)=> MN1) ->
        (NetMod.get n MN0 =(lower_flushing ma)=> mq MQ1 M1 S1) ->
        NetMod.get n MN1 = mq (MQ1 ++ lower_flushing_artifact n ma) M1 S1.

    Proof.
      intros.
      destruct_mna ma; consider (MN0 =(_)=> _); eattac.
      - destruct M2, M3; simpl in *.
        smash_eq n n1; hsimpl in *; attac.
      - smash_eq n n1; hsimpl in *; attac.
    Qed.


    Lemma Flushing_act_get_neq : forall ma MN0 MN1 n n' MQ1 M1 S1,
        n <> n' ->
        Flushing_NAct n ma ->
        (MN0 =(ma)=> MN1) ->
        (NetMod.get n' MN0 = mq MQ1 M1 S1) ->
        NetMod.get n' MN1 = mq (MQ1 ++ lower_flushing_artifact n' ma) M1 S1.

    Proof.
      intros.
      destruct_mna ma; consider (MN0 =(_)=> _); eattac.
      - destruct M2; simpl in *.
        smash_eq n' n1; hsimpl in *; eattac.
      - smash_eq n' n1; hsimpl in *; eattac.
    Qed.


    Lemma Flushing_act_get : forall ma MN0 MN1 n n' MQ1 M1 S1 MQ' M' S',
        Flushing_NAct n ma ->
        (MN0 =(ma)=> MN1) ->
        (NetMod.get n MN0 =(lower_flushing ma)=> mq MQ1 M1 S1) ->
        (NetMod.get n' (NetMod.put n (mq MQ1 M1 S1) MN0) = mq MQ' M' S') ->
        NetMod.get n' MN1 = mq (MQ' ++ lower_flushing_artifact n' ma) M' S'.

    Proof.
      intros.
      smash_eq n n'.
      - eapply Flushing_act_get_eq; eattac.
      - eapply Flushing_act_get_neq; eattac.
    Qed.


    Fixpoint lift_flushing_path (n : Name) mpath (HF : Forall Flushing_act mpath) : list MNAct.
      refine '(match mpath as mpath' return mpath = mpath' -> list MNAct with
               | [] => fun _ => []
               | ma::mpath0 => fun e => lift_flushing n ma _ :: lift_flushing_path n mpath0 _
               end eq_refl
        ); attac.
    Defined.


    Lemma lift_flushing_path_Flushing : forall n mpath (HF : Forall Flushing_act mpath),
        Forall (Flushing_NAct n) (lift_flushing_path n mpath HF).

    Proof.
      induction mpath; eattac.
      eauto 15 using lift_flushing_Flushing.
    Qed.

    Hint Resolve lift_flushing_path_Flushing : LTS.


    Lemma lift_flushing_path_irrelevance : forall n mpath (HF HF' : Forall Flushing_act mpath),
        lift_flushing_path n mpath HF = lift_flushing_path n mpath HF'.

    Proof.
      induction mpath; attac.
      f_equal; eauto with LTS.
    Qed.

    Hint Resolve lift_flushing_path_irrelevance : LTS.


    Lemma lift_lower_flushing_path n (mnpath : list MNAct)
      {HF : Forall Flushing_act (map lower_flushing mnpath)} :
      Forall (Flushing_NAct n) mnpath ->
      lift_flushing_path n (map lower_flushing mnpath) HF = mnpath.
    Proof.
      induction mnpath; attac.
      f_equal; eauto using lift_lower_flushing with LTS.
    Qed.

    Lemma lower_lift_flushing_path n mpath (HF : Forall Flushing_act mpath) :
      map lower_flushing (lift_flushing_path n mpath HF) = mpath.

    Proof.
      induction mpath; attac.
      rewrite lower_lift_flushing.
      f_equal.
      attac.
    Qed.

    Hint Resolve lower_lift_flushing_path lift_lower_flushing_path : LTS.


    (** If a node can perform a path of flushing actions, then the network can too. *)
    Lemma Flushing_path_available : forall [mpath] [MS1] n MN0 (HF : Forall Flushing_act mpath),
        (NetMod.get n MN0 =[mpath]=> MS1) ->
        exists MN1, (MN0 =[lift_flushing_path n mpath HF]=> MN1).

    Proof.
      intros.
      ltac1:(debug auto with LTS).
      generalize dependent MN0 MS1.
      induction mpath; attac.

      destruct MS1 as [MQ2 M2 S2].
      destruct N1 as [MQ1 M1 S1].

      pose (ma := lift_flushing n a (Forall_inv HF)).

      consider (exists MN1, (MN0 =(ma)=> MN1)) by eauto using Flushing_act_available.
      consider (NetMod.get n MN1 = mq (MQ1 ++ (lower_flushing_artifact n ma)) M1 S1).
      {
        subst ma; hsimpl.
        eapply Flushing_act_get_eq; eauto using lift_flushing_Flushing with LTS.
        attac.
      }

      consider (exists MN2 : NetMod.t MQued, MN1 =[ lift_flushing_path n mpath (Forall_inv_tail HF) ]=> MN2)
        by (eapply IHmpath; rewrite `(NetMod.get n MN1 = _); eauto using Flushing_cont, Forall_inv_tail).

      exists MN2.

      eapply path_seq1.
      - erewrite lift_flushing_irrelevance; eauto.
      - erewrite lift_flushing_path_irrelevance; eauto.
    Qed.

    Definition lower_flushing_path_artifact n := List.flat_map (lower_flushing_artifact n).


    Lemma Flushing_path_get_eq : forall mnpath MN0 MN1 n MQ1 M1 S1,
        Forall (Flushing_NAct n) mnpath ->
        (MN0 =[mnpath]=> MN1) ->
        (NetMod.get n MN0 =[List.map lower_flushing mnpath]=> mq MQ1 M1 S1) ->
        NetMod.get n MN1 = mq (MQ1 ++ lower_flushing_path_artifact n mnpath) M1 S1.

    Proof.
      induction mnpath; eattac.

      rename MN1 into MN2.
      rename N2 into MN1.
      rename MQ1 into MQ2.
      rename M1 into M2.
      rename S1 into S2.
      destruct N1 as [MQ1 M1 S1].

      assert (NetMod.get n MN1 = mq (MQ1 ++ lower_flushing_artifact n a) M1 S1) by eauto using Flushing_act_get_eq with LTS.

      enough (NetMod.get n MN1 =[ map lower_flushing mnpath ]=> mq (MQ2 ++ lower_flushing_artifact n a) M2 S2
) by (rewrite app_assoc; eauto).

      rewrite `(NetMod.get n MN1 = _).
      eapply Flushing_cont; eauto with LTS.
    Qed.


    Lemma Flushing_path_get_neq : forall mnpath MN0 MN1 n n' MQ0 M0 S0,
        n <> n' ->
        Forall (Flushing_NAct n) mnpath ->
        (MN0 =[mnpath]=> MN1) ->
        (NetMod.get n' MN0 = mq MQ0 M0 S0) ->
        NetMod.get n' MN1 = mq (MQ0 ++ lower_flushing_path_artifact n' mnpath) M0 S0.

    Proof.
      induction mnpath; attac.

      rename MN1 into MN2.
      rename N1 into MN1.
      assert (NetMod.get n' MN1 = mq (MQ0 ++ lower_flushing_artifact n' a) M0 S0) by eauto using Flushing_act_get_neq with LTS.

      rewrite app_assoc; eauto.
    Qed.


    Lemma Flushing_path_get : forall mnpath MN0 MN1 n n' MQ1 M1 S1 MQ' M' S',
        Forall (Flushing_NAct n) mnpath ->
        (MN0 =[mnpath]=> MN1) ->
        (NetMod.get n MN0 =[List.map lower_flushing mnpath]=> mq MQ1 M1 S1) ->
        (NetMod.get n' (NetMod.put n (mq MQ1 M1 S1) MN0) = mq MQ' M' S') ->
        NetMod.get n' MN1 = mq (MQ' ++ lower_flushing_path_artifact n' mnpath) M' S'.

    Proof.
      intros.
      smash_eq n n'.
      - eapply Flushing_path_get_eq; eattac.
      - eapply Flushing_path_get_neq; eattac.
    Qed.


    Lemma lift_admin_act : forall n a (HF : Flushing_act a),
        [a] >:~ [] ->
        MNAct_to_PNAct (lift_flushing n a HF) = None.

    Proof.
      intros; destruct_ma a; attac.
    Qed.

    Lemma lift_admin_path : forall n mpath (HF : Forall Flushing_act mpath),
        mpath >:~ [] ->
        MNPath_to_PNPath (lift_flushing_path n mpath HF) = [].

    Proof.
      induction mpath; attac.
      destruct_ma a; attac.

      absurd (Flushing_act (MActM (Recv (n0, t) v))); eauto using Forall_cons with LTS.
      eapply Forall_inv; eauto.
    Qed.

    Hint Resolve lift_admin_act lift_admin_path : LTS.


    Lemma lower_flushing_artifact_NoSend : forall n a, NoSends_MQ (lower_flushing_artifact n a).

    Proof.
      intros.
      destruct_mna a; attac; smash_eq n n1; attac.
    Qed.


    Lemma lower_flushing_path_artifact_NoSend : forall n mpath, NoSends_MQ (lower_flushing_path_artifact n mpath).

    Proof.
      intros.
      induction mpath; attac.
      split; eauto using lower_flushing_artifact_NoSend.
    Qed.


    Lemma lower_flushing_artifact_MQ_Clear : forall n a,
        MNAct_to_PNAct a = None -> MQ_Clear (lower_flushing_artifact n a).

    Proof.
      intros.
      destruct_mna a; attac; smash_eq n n1; attac.
    Qed.


    Lemma lower_flushing_path_artifact_MQ_Clear : forall n mpath,
        MNPath_to_PNPath mpath = [] ->
        MQ_Clear (lower_flushing_path_artifact n mpath).

    Proof.
      induction mpath; attac.
      split.
      - destruct_mna a; attac; smash_eq n n1; attac.
      - destruct_mna a; attac.
    Qed.


    Hint Resolve lower_flushing_artifact_NoSend lower_flushing_path_artifact_NoSend lower_flushing_artifact_MQ_Clear lower_flushing_path_artifact_MQ_Clear : LTS.


    Lemma NV_Transp_completeness_tau : forall (I : mon_assg) {n : Name} {N0 N1 : PNet},
        (NVTrans n Tau N0 N1) ->
        (NVTrans n (MActP Tau) (net_instr I N0) (net_instr I N1)).

    Proof.
      intros.
      hsimpl in *.

      destruct (&I n) as (MQ & M) eqn:HI.
      assert (instr MQ M (NetMod.get n N0) =( MActP Tau )=> instr MQ M &S)
        by eauto using Transp_completeness_tau.

      unfold net_instr, net_instr_n; hsimpl.
      attac.
    Qed.


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


    Lemma NV_Transp_completeness_send : forall (Instr0 : mon_assg) {n : Name} {nc : NChan} {v} {N0 N1 : PNet},
        (N0 ~(n @ @send PAct gen_Act_PAct nc v)~> N1) ->
        exists MN1 mnpath MN2,
          (net_instr Instr0 N0 =[NTau n (MActP (Send nc v)) :: mnpath]=> MN1)
          /\ (MN1 ~(n @ @send MAct gen_Act_MAct nc # v)~> MN2)
          /\ net_deinstr MN2 = N1
          /\ Forall (Flushing_NAct n) mnpath
          /\ MNPath_to_PNPath mnpath = [].

    Proof.
      intros.
      hsimpl in *.
      destruct (&Instr0 n) as ([MQ0 ?] & [M0 ?]) eqn:HI.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?.
      destruct S as [I1 P1 O1].

      consider (exists mpath M1,
                   (### mq MQ0 M0 (pq I0 P0 O0) =[MActP (Send nc v) :: mpath]=> (mq [TrSend nc v] M1 (pq (I1 ++ MQ_r MQ0) P1 O1)))
                   /\ Forall Flushing_act mpath
                   /\ ready M1
               ) by eauto using Transp_completeness_send_prep.

      replace (MQ_r MQ0) with ([] : Que Val) by attac.

      assert (mpath >:~ []) by (re_have hsimpl in *; eauto using Flushing_clear_until).

      pose (MN0' := NetMod.put n (mq (MQ0 ++ [TrSend nc v]) M0 (pq I1 P1 O1) ) (net_instr Instr0 N0)).

      assert (net_instr Instr0 N0 =(NTau n (MActP (Send nc v)))=> MN0')
        by (subst MN0'; constructor; eattac; unfold net_instr, net_instr_n; eattac).

      pose (mnpath := lift_flushing_path n mpath ltac:(auto)).
      assert (Forall (Flushing_NAct n) mnpath) by eauto using lift_flushing_path_Flushing.

      consider (exists MN1, MN0' =[ mnpath ]=> MN1).
      {
        subst MN0'.
        eapply Flushing_path_available.
        unfold net_instr, net_instr_n.
        re_have compat_hsimpl in *.
        eauto.
      }

      assert (NetMod.get n MN1 = mq ([TrSend nc v] ++ lower_flushing_path_artifact n mnpath) {| handle := h; state := MRecv s |}  (pq I1 P1 O1)).
      {
        eapply Flushing_path_get_eq; eattac.
        subst mnpath MN0'.
        rewrite lower_lift_flushing_path.
        re_have compat_hsimpl in *.
        attac.
      }

      assert (MQ_Clear (lower_flushing_path_artifact n mnpath)) by (subst mnpath; eauto with LTS).

      pose (MN2 := NetMod.put n (mq (lower_flushing_path_artifact n mnpath) {| handle := h; state := h (TrSend nc v) s |}  (pq I1 P1 O1)) MN1).

      exists MN1, mnpath, MN2.

      enough ('' MN2 = NetMod.put n (pq I1 P1 O1) N0) by eattac.

      subst MN2.
      apply NetMod.extensionality; intros n'.

      unfold net_deinstr, deinstr in *.
      smash_eq n n'.
      1: { hsimpl; attac. }.

      destruct (NetMod.get n' MN1) as [MQ1' M1' [I1' P1' O1']] eqn:?.
      hsimpl.
      remember (pq (I1' ++ MQ_r MQ1') P1' (MQ_s MQ1' ++ O1')) as S'.

      enough (S' = NetMod.get n' '' (net_instr Instr0 N0)) by attac.
      enough (S' = NetMod.get n' (net_instr Instr0 N0)) by (unfold net_deinstr; attac).

      assert (NetMod.get n' (net_instr Instr0 N0) = NetMod.get n' MN0') by (eapply act_particip_stay; attac).
      destruct (NetMod.get n' MN0') as [MQ0' M0' [I0' P0' O0']] eqn:?.
      assert (MQ_Clear MQ0') by attac.
      assert (MQ_Clear (lower_flushing_path_artifact n' mnpath)) by attac.

      enough (S' = NetMod.get n' MN0') by attac.
      enough (S' = mq (MQ0' ++ lower_flushing_path_artifact n' mnpath) M0' (pq I0' P0' O0')) by (rewrite `(NetMod.get n' MN0' = _); attac).

      replace (mq (MQ0' ++ lower_flushing_path_artifact n' mnpath) M0' (pq I0' P0' O0'))
        with (NetMod.get n' MN1)
        by (eauto using Flushing_path_get_neq).

      unfold deinstr in *.
      attac.
    Qed.


    Lemma NV_Transp_completeness_recv : forall {n : Name} {nc : NChan} {v} {N0 N1 : PNet} {MN0},
        '' MN0 = N0 ->
        (NVTrans n (@recv PAct gen_Act_PAct nc v) N0 N1) ->
        exists MN1 mnpath MN2,
        (NVTrans n (@recv MAct gen_Act_MAct nc # v) MN0 MN1)
        /\ (MN1 =[mnpath]=> MN2)
        /\ '' MN2 = N1
        /\ Forall (Flushing_NAct n) mnpath
        /\ MNPath_to_PNPath mnpath = [].

    Proof.
      intros.

      destruct (NetMod.get n MN0) as [MQ0 M0 [I0 P0 O0]] eqn:?.

      assert (NetMod.get n N0 = pq (I0 ++ MQ_r MQ0) P0 (MQ_s MQ0 ++ O0)) by (unfold net_deinstr, deinstr in *; eattac).

      compat_hsimpl in *.

      pose (MN1 := NetMod.put n (mq (MQ0 ++ [TrRecv nc v]) M0 (pq I0 P0 O0)) MN0).

      consider (exists mpath M1,
                   (### mq (MQ0 ++ [TrRecv nc v]) M0 (pq I0 P0 O0) =[ mpath ]=> mq [TrRecv nc v] M1 (pq (I0 ++ MQ_r MQ0) P0 O0))
                   /\ Forall Flushing_act mpath
                   /\ ready M1
               ) by eauto using flush_exists_until.

      pose (mnpath :=  lift_flushing_path n mpath ltac:(auto with LTS)).

      consider (exists MN2, MN1 =[ mnpath ]=> MN2) by (eapply Flushing_path_available; subst MN1; eattac).
      assert (Forall (Flushing_NAct n) mnpath ) by attac.
      assert (MNPath_to_PNPath mnpath = []).
      enough (mpath >:~ []) by attac.
      enough (MQ_Clear MQ0).
      assert (mq MQ0 M0 (pq I0 P0 O0) =[ mpath ]=>
                mq [] {| handle := h; state := MRecv s |} (pq (I0 ++ MQ_r MQ0) P0 O0)
             ) by re_have eauto using Flushing_retract.
      eattac.

      exists MN1, mnpath, MN2.
      eattac.

      repeat split; attac.
      eattac 15.
      constructor.

      assert (Forall (Flushing_NAct n) mnpath ) by attac.

    Lemma Net_Transp_completeness_tau : forall n I0 {N0 N1 : PNet},
        (N0 =(NTau n Tau)=> N1) ->
        (net_instr I0 N0 =(NTau n (MActP Tau))=> net_instr I0 N1).

    Proof.
      intros.
      consider (_ =(_)=> _).
      constructor; attac.
      eauto using NV_Transp_completeness_tau with LTS.
    Qed.


    Lemma Net_Transp_completeness_comm : forall n0 n1 t (v : Val) I0 {N0 N1 : PNet},
        (N0 =(NComm n0 n1 t (v : @Payload PAct gen_Act_PAct))=> N1) ->
        exists mnpath0 mnpath1 MN1,
          (net_instr I0 N0 =[NTau n0 (MActP (Send (n1, t) v)) :: mnpath0 ++ NComm n0 n1 t # v :: mnpath1]=> MN1)
          /\ '' MN1 = N1
          /\ Forall (Flushing_NAct n0) mnpath0
          /\ MNPath_to_PNPath mnpath0 = []
          /\ Forall (Flushing_NAct n1) mnpath1
          /\ MNPath_to_PNPath mnpath1 = [].

    Proof.
      intros.
      consider (_ =(_)=> _).

      consider (exists MN1 mnpath0 MN2,
                 (### net_instr I0 N0 =[ NTau n0 (MActP (Send (n1, t) v)) :: mnpath0 ]=> MN1)
                 /\ (### MN1 ~( n0 @ send (n1, t) # v )~> MN2)
                 /\ '' MN2 = N0'
                 /\ Forall (Flushing_NAct n0) mnpath0
                 /\ MNPath_to_PNPath mnpath0 = []
             )
      by eauto using NV_Transp_completeness_send with LTS.

      consider (exists MN3 mnpath1 MN4,
                   (### NVTrans n1 (@recv MAct gen_Act_MAct (n0, t) # v) MN2 MN3)
                   /\ (### MN3 =[mnpath1]=> MN4)
                   /\ '' MN4 = N1
                   /\ Forall (Flushing_NAct n1) mnpath1
                   /\ MNPath_to_PNPath mnpath1 = []
               ) by eauto using NV_Transp_completeness_recv.

      exists mnpath0, mnpath1, MN4.
      eattac.

      enough (net_instr I0 N0 =[ (NTau n0 (MActP (Send (n1, t) v)) :: mnpath0) ++ NComm n0 n1 t # v :: mnpath1 ]=> MN4) by attac.
      enough (MN1 =(NComm n0 n1 t # v)=> MN3) by re_have eauto with LTS.

      eattac.
    Qed.


    Lemma Net_Transp_completeness_comm_instr : forall n0 n1 t (v : Val) I0 {N0 N1 : PNet},
        (N0 =(NComm n0 n1 t (v : @Payload PAct gen_Act_PAct))=> N1) ->
        exists mnpath0 mnpath1 I1,
          (net_instr I0 N0 =[NTau n0 (MActP (Send (n1, t) v)) :: mnpath0 ++ NComm n0 n1 t # v :: mnpath1]=> net_instr I1 N1)
          /\ Forall (Flushing_NAct n0) mnpath0
          /\ MNPath_to_PNPath mnpath0 = []
          /\ Forall (Flushing_NAct n1) mnpath1
          /\ MNPath_to_PNPath mnpath1 = [].

    Proof.
      intros.

      consider ( exists mnpath0 mnpath1 MN1,
                   (net_instr I0 N0 =[NTau n0 (MActP (Send (n1, t) v)) :: mnpath0 ++ NComm n0 n1 t # v :: mnpath1]=> MN1)
                   /\ '' MN1 = N1
                   /\ Forall (Flushing_NAct n0) mnpath0
                   /\ MNPath_to_PNPath mnpath0 = []
                   /\ Forall (Flushing_NAct n1) mnpath1
                   /\ MNPath_to_PNPath mnpath1 = []
               )
        by eauto using Net_Transp_completeness_comm.

      enough (exists mnpath2 I1, (MN1 =[mnpath2]=> net_instr I1 N1) /\ Forall ())



    (** Network transparency completeness over a single action *)
    Lemma Net_Transp_completeness1 : forall I0 {a} {N0 N1 : PNet},
        (N0 =(a)=> N1) ->
        exists mnpath0 mnpath1 MN1,
          (net_instr I0 N0 =[mnpath0 ++ PNAct_to_MNAct a :: mnpath1]=> MN1)
          /\ '' MN1 = N1
          /\ MNPath_to_PNPath mnpath0 = []
          /\ MNPath_to_PNPath mnpath1 = [].

    Proof.
      intros.
      destruct a.
      - exists [], [], (net_instr I0 N1).
        consider (p = Tau) by attac.
        attac; eauto using Net_Transp_completeness_tau.
      - rename n0 into n1.
        rename n into n0.
        rename p into v.

        consider ( exists mnpath0 mnpath1 MN1,
                     (net_instr I0 N0 =[NTau n0 (MActP (Send (n1, t) v)) :: mnpath0 ++ NComm n0 n1 t # v :: mnpath1]=> MN1)
                     /\ '' MN1 = N1
                     /\ Forall (Flushing_NAct n0) mnpath0
                     /\ MNPath_to_PNPath mnpath0 = []
                     /\ Forall (Flushing_NAct n1) mnpath1
                     /\ MNPath_to_PNPath mnpath1 = []
                 )
          by eauto using Net_Transp_completeness_comm.

        exists (NTau n0 (MActP (Send (n1, t) v)) :: mnpath0), mnpath1.
        eattac.
    Qed.


    (** Network transparency completeness over a single action *)
    Lemma Net_Transp_completeness_instr_1 : forall I0 {a} {N0 N1 : PNet},
        (N0 =(a)=> N1) ->
        exists mnpath0 mnpath1 I1,
          (net_instr I0 N0 =[mnpath0 ++ PNAct_to_MNAct a :: mnpath1]=> net_instr I1 N1)
          /\ MNPath_to_PNPath mnpath0 = []
          /\ MNPath_to_PNPath mnpath1 = [].

    Proof.
      intros.
      destruct a.
      - exists [], [], (net_instr I0 N1).
        consider (p = Tau) by attac.
        attac; eauto using Net_Transp_completeness_tau.
      - rename n0 into n1.
        rename n into n0.
        rename p into v.

        consider ( exists mnpath0 mnpath1 MN1,
                     (net_instr I0 N0 =[NTau n0 (MActP (Send (n1, t) v)) :: mnpath0 ++ NComm n0 n1 t # v :: mnpath1]=> MN1)
                     /\ '' MN1 = N1
                     /\ Forall (Flushing_NAct n0) mnpath0
                     /\ MNPath_to_PNPath mnpath0 = []
                     /\ Forall (Flushing_NAct n1) mnpath1
                     /\ MNPath_to_PNPath mnpath1 = []
                 )
          by eauto using Net_Transp_completeness_comm.

        exists (NTau n0 (MActP (Send (n1, t) v)) :: mnpath0), mnpath1.
        eattac.
    Qed.


    (** Network transparency completeness *)
    Theorem Net_Transp_completeness : forall {ppath} I0 {N0 N1 : PNet},
        (N0 =[ ppath ]=> N1) ->
        exists mpath I1,
          MNPath_to_PNPath mpath = ppath
          /\ (net_instr I0 N0 =[ mpath ]=> net_instr I1 N1).

    Proof with attac.
      induction ppath; intros.
      1: exists [], I0...

      rename N1 into N2.
      hsimpl in *.

      edestruct (Net_Transp_completeness1) with (I0:=I0)
        as (mpath0 & ma & mpath1 & I1 & ?); eauto.
      hsimpl in *.

      consider (exists (mpath2 : list MNAct) (I2 : mon_assg),
                 MNPath_to_PNPath mpath2 = ppath /\ (net_instr I1 N1 =[ mpath2 ]=> net_instr I2 N2)
             ).

      exists (mpath0 ++ [ma] ++ mpath1 ++ mpath2), I2...

      hsimpl.
      rewrite `(MNPath_to_PNPath mpath0 = _).
      rewrite `(MNPath_to_PNPath mpath1 = _).
      attac.
    Qed.
  End Completeness.


  Section Soundness.

  End Soundness.


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
        absurd (MQ_Clear (TrRecv n0 v :: MQ)); attac.

    - destruct p; attac.
      + destruct n0 as [n0 t0].
        smash_eq n n0.
        1: specialize (HNoself t0 (MValP v)); bullshit.

        remember (mq MQ {| handle := h; state := h (TrSend (n0, t0) v) s |} P) as S.

        assert (exists N0', NetMod.get n N0' = &S /\ NVTrans n (send (n0, t0) (MValP v)) N0 N0')
          as (N0' & HeqN0 & NT0)
            by (exists (NetMod.put n &S N0); eattac).

        destruct (recv_available n0 n t0 (MValP v) N0') as (N0'' & NT0').
        exists (NComm n n0 t0 v), N0''; attac.

        all: unfold no_sends_in, NoTrSend, flushed_in, flushed, Flushed, net_deinstr, ready_in in *.
        * hsimpl in *.
          smash_eq n n0 m; attac.

        * hsimpl in *. attac.
        * hsimpl in *. hsimpl in *.
          assert (flushed_in n N0) by auto.
          unfold flushed_in, Flushed in *.
          hsimpl in *. bullshit.
    - destruct a; attac.
      + destruct n0 as [n0 t0].

        smash_eq n n0.
        1: now (specialize (HNoself t0 (MValM v)); bullshit).

        consider (exists N1 : MNet, N0 =( NComm n n0 t0 v)=> N1)
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
      bullshit.
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
    - left; intros t0 v0; destruct v0; bullshit.
    - right. eexists t, (MValM v). eattac.
    - left; intros t0 v0; destruct v0; bullshit.
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
    intros until MN0. intros HNS0.

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
        bullshit.
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
    destruct a; try (destruct p); simpl; try (left; intros; simpl; destruct v0; discriminate);
      try (left; intros; simpl; destruct v; discriminate).
    destruct n0 as [n0 t].
    destruct (NAME.eq_dec n0 n); subst.
    (right; exists t, (MValP v); simpl; auto).
    (left; intros; simpl; destruct v0). discriminate. injection. intros. subst. congruence.
    destruct a. destruct n0 as [n0 t]. destruct (NAME.eq_dec n0 n); subst.
    (right; exists t, (MValM v); simpl; auto).
    (left; intros; simpl; destruct v0). injection. intros. subst. congruence. discriminate.
    (left; intros; simpl; destruct v0; discriminate).
    (left; intros; simpl; destruct v; discriminate).

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
    apply (path_seq T0).
    apply (path_seq T1).
    rewrite &Eq in T2.
    apply T2.
  Qed.


  Lemma Net_corr_extraction : forall [MN0 MN1 : MNet] [mnpath],
      (MN0 =[ mnpath ]=> MN1) ->
      forall n,
      exists mpath ppath,
        Path_of n mnpath mpath
        /\ (NetMod.get n (net_deinstr MN0) =[ ppath ]=> NetMod.get n (net_deinstr MN1))
        /\ path_corr mpath ppath.

  Proof.
    intros until mnpath.
    intros TN n.

    destruct (path_of_exists n mnpath) as (mpath & HPo).
    specialize (path_of_ptrans HPo TN) as TM.

    unfold net_deinstr.
    do 2 (rewrite NetMod.get_map).
    apply corr_extraction in TM as (ppath & T & HCorr).

    exists mpath, ppath.
    repeat split.
    - apply HPo.
    - apply T.
    - apply HCorr.
  Qed.


  Lemma Net_Vis_corr_psend : forall [n n' : Name] [t0 v] [MN0 MN1 : MNet],
      (NVTrans n (MActP (Send (n', t0) v)) MN0 MN1) ->
      net_deinstr MN0 = net_deinstr MN1.

  Proof.
    intros until MN1. intros T.

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
    intros until MN1. intros T.

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
    intros until MN1. intros T.

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
    intros until MN1. intro T.
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
    intros until MN1. intro T.
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
    apply (path_seq TN0 TN1).
  Qed.


  (** Soundness of network transparency *)
  Theorem Net_Transp_soundness : forall {mnpath0} {I0} {N0 : PNet} {MN1 : MNet},
      (net_instr I0 N0 =[ mnpath0 ]=> MN1) ->
      exists mnpath1 pnpath I2 N2,
        (MN1 =[ mnpath1 ]=> net_instr I2 N2)
        /\ (N0 =[ pnpath ]=> N2).

  Proof.
    intros until MN1.
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

    specialize (path_seq NTM0 NTM1) as NTM.

    destruct (Net_path_corr NTM) as (pnpath & TN).
    do 2 (rewrite net_deinstr_instr in TN).

    exists mnpath1, pnpath, I1, N2.

    split.
    - apply NTM1.
    - apply TN.
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
    intros until MN1. intros TN.
    kill TN.
    now apply Net_Vis_corr_mon in H0.
  Qed.


  Lemma mcomm_invariant_deinstr : forall [n n' t0] [m : Msg] [MN0 MN1 : MNet],
      (MN0 =(NComm n n' t0 (MValM m))=> MN1) ->
      net_deinstr MN0 = net_deinstr MN1.

  Proof.
    intros until MN1. intros TN.
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


  Lemma net_instr_ready : forall I N, ready_net (net_instr I N).

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
    intros until N0. intros HC HF TM.

    kill TM; kill HC; kill HF; try (destruct n0 as [n0 t0]).
    - unshelve eexists [NComm n n0 t0 _]. apply (MValM msg).

      assert (NetMod.get n (NetMod.put n (mq MQ1 M0 S1) (net_instr I0 N0))
              =(MActM (Send (n0, t0) msg))=>
                (mq MQ1 M1 S1)
             ).
      repeat (rewrite NetMod.get_put_eq).
      constructor. assumption.
      apply NT_Vis in H1.
      rewrite NetMod.put_put_eq in H1.
      rename H1 into NT_send.

      destruct (NetMod.get n0 (NetMod.put n (mq MQ1 M1 S1) (net_instr I0 N0)))
        as [MQr Mr Sr] eqn:HeqR.

      assert (NetMod.get n0 (NetMod.put n (mq MQ1 M1 S1) (net_instr I0 N0))
              =(MActM (Recv (n, t0) msg))=>
                (mq (MQr ++ [EvRecv (n, t0) msg]) Mr Sr)
             ).
      rewrite HeqR.
      constructor.

      apply NT_Vis in H1.
      rename H1 into NT_recv.

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
          unfold flushed_in in H1.
          rewrite HeqR in H1.
          apply Forall_app; split; attac.
        }

        assert (ready Mr) as HMr.
        {
          specialize (net_instr_ready I0 N0 n0) as HR.
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

        rewrite H2.
        apply H1.
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

      apply (NT_Vis) in H1.
      rewrite NetMod.put_put_eq in H1.
      apply H1.

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

      apply (NT_Vis) in H1.
      rewrite NetMod.put_put_eq in H1.
      apply H1.

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

      apply (NT_Vis) in H1.
      rewrite NetMod.put_put_eq in H1.
      apply H1.
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
    induction mpath; intros until N0; intros HC HF TM.
    kill TM. kill HC. kill HF.

    exists [], I0, []...
    repeat split. rewrite app_nil_r. constructor. constructor.

    apply path_split1 in TM as ([MQ0' M0' S0'] & TM0 & TM1).
    apply path_corr_split_nil1 in HC as (HC0 & HC1).
    inversion HF. subst. rename H1 into HF0. rename H2 into HF1.

    destruct (admin_path_available1' n I0 N0 HC0 HF0 TM0)
      as (nmpath0 & I0' & MQ'0' & TNM0 & HCMQ').

    apply (Flushing_cont MQ'0') in TM1.

    specialize (IHmpath _ _ _ _ _ _ n I0' N0 HC1 HF1 TM1)
      as (nmpath1 & I1 & MQ1' & TNM1 & HMQ1).

    exists (nmpath0 ++ nmpath1), I1, (MQ'0' ++ MQ1').
    split.
    - rewrite app_assoc.
      apply (path_seq TNM0 TNM1).
    - apply Forall_app; auto.
    - auto.
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
    intros until MN0. intros HC HF TM HFN0.

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


  Lemma prepare_send : forall I0 [N0 : PNet] [n n' v S1],
      (NetMod.get n N0 =(send n' v)=> S1) ->
      exists mnpath I1 MQ1 M1 MN1,
        (net_instr I0 N0 =[mnpath]=> MN1)
        /\ NVTrans n (send n' (MValP v)) MN1 (NetMod.put n (mq MQ1 M1 S1) (net_instr I1 N0))
        /\ N0 = net_deinstr MN1
        /\ MQ_Clear MQ1.

  Proof.
    intros until S1. intros T.

    destruct (I0 n) as (MQ0_ & M0_) eqn:HI0.

    destruct (Transp_completeness_send MQ0_ M0_ T)
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
    intros until S1. intros T0 HFN0.

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

    destruct (Transp_completeness_recv MQ0 M0 HMQ0 T0)
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
    - apply (path_seq TNM1).
      apply path_seq0.

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
      specialize (net_instr_ready I0 N0 n0) as HR.
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

      subst.
      apply (path_seq TN0).
      apply (path_seq TN1).
      apply (path_seq TN2).

      rewrite <- HND4 in *.
      rewrite &Eq in TN3.
      unfold net_deinstr in TN3.
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


End Transp.
