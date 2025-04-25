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

Open Scope nat.

Module Type COMPL_STRONG_F(Import Conf : DETECT_CONF)(Import Params : DETECT_PARAMS(Conf)).
  Include COMPL_F(Conf)(Params).
  Module Import NT := NetTactics(Conf)(Params.NetLocks.Net).

  Inductive DetectMeasure := DM {dm_flush : nat; dm_pass : nat}.

  Definition dm_lep (dm0 dm1 : DetectMeasure) : bool :=
    let c0 := dm_flush in
    let c1 := dm_pass in
    let next c f :=
      match (c dm0 =? c dm1) with
      | true => f
      | _ => (c dm0 <=? c dm1)
      end
    in next c1 (next c0 true).

  Definition dm_ltp (dm0 dm1 : DetectMeasure) : bool :=
    let c0 := dm_flush in
    let c1 := dm_pass in
    let next c f :=
      match (c dm0 =? c dm1) with
      | true => f
      | _ => (c dm0 <? c dm1)
      end
    in next c1 (next c0 false).

  Definition dm_eqb (dm0 dm1 : DetectMeasure) : bool :=
    (dm_flush dm0 =? dm_pass dm1)%nat && (dm_pass dm0 =? dm_pass dm1)%nat.

  Definition probe_eqb (p0 p1 : MProbe) :=
    NAME.eqb (origin p0) (origin p1) && (lock_id p0 =? lock_id p1)%nat.

  Lemma probe_eqb_eq : forall p0 p1, probe_eqb p0 p1 = true <-> p0 = p1.
  Proof.
    split; intros; destruct p0, p1; unfold probe_eqb, andb in *;
      simpl in *; blast_cases.
    all: try (rewrite PeanoNat.Nat.eqb_eq in * ).
    all: try (rewrite PeanoNat.Nat.eqb_neq in * ).
    all: attac.
  Qed.

  Lemma probe_eqb_neq : forall p0 p1, probe_eqb p0 p1 = false <-> p0 <> p1.
  Proof.
    split; intros.
    - intros HEq.
      rewrite <- probe_eqb_eq in *. bs.
    - destruct (probe_eqb p0 p1) eqn:?; auto.
      rewrite -> probe_eqb_eq in *. bs.
  Qed.

  Lemma probe_eqb_refl : forall p, probe_eqb p p = true.
  Proof.
    intros.
    rewrite probe_eqb_eq. reflexivity.
  Qed.

  Definition hot_MS (MS : MServ) := {|origin:=self MS; lock_id:=lock_count MS|}.

  Hint Rewrite -> probe_eqb_eq probe_eqb_neq probe_eqb_refl
                   PeanoNat.Nat.eqb_eq PeanoNat.Nat.eqb_neq PeanoNat.Nat.eqb_refl
                   using assumption : LTS LTS_concl.


  Fixpoint measure_mon_fin M : (nat * MState) :=
    match M with
    | MRecv s => (0, s)
    | MSend _ _ M =>
        let (mm, s) := measure_mon_fin M in
        (S mm, s)
    end.

  Fixpoint measure_mq_fin (M : MProc) MQ : option nat :=
    if alarm M
    then Some 0 (* We don't care for the sends *)
    else match MQ with
         | [] => None
         | e :: MQ =>
             let (mm, s) := measure_mon_fin M in
             let M := mon_handle e s in
             option_map (plus (S mm)) (measure_mq_fin M MQ)
    end.

  Definition measure_ms_fin (MS : MServ) : option nat :=
    measure_mq_fin (mserv_m MS) (mserv_q MS).


  Fixpoint measure_mon (n_to : Name) p M : (nat * bool) :=
    match M with
    | MRecv _ => (0, false)
    | MSend (n, R) p' M =>
        if NAME.eqb n n_to && probe_eqb p p'
        then (1, true)
        else
          let (mm, found) := measure_mon n_to p M in
          (S mm, found)
    | MSend (_, Q) _ M =>
        let (mm, found) := measure_mon n_to p M in
        (S mm, found)
    end.


  Fixpoint measure_mq (n_to : Name) p (M : MProc) MQ : option nat :=
    let (mm, found_m) := measure_mon n_to p M in
    if found_m
    then Some mm
    else match MQ with
         | [] => None
         | e :: MQ =>
             match measure_mq n_to p (mon_handle e M) MQ with
             | None => None
             | Some mq => Some (mm + S mq)
             end
         end.


  Lemma unfold_measure_mq : forall (n_to : Name) p (M : MProc) MQ mm found_m,
      measure_mon n_to p M = (mm, found_m) ->
      measure_mq n_to p M MQ =
        if found_m
        then Some mm
        else match MQ with
             | [] => None
             | e :: MQ =>
                 match measure_mq n_to p (mon_handle e M) MQ with
                 | None => None
                 | Some mq => Some (mm + S mq)
                 end
             end.
  Proof. destruct MQ; attac. Qed.

  Hint Rewrite -> unfold_measure_mq using spank : LTS LTS_concl.

  Definition measure_ms (n_to : Name) p (MS : MServ) : option nat :=
    measure_mq n_to p (mserv_m MS) (mserv_q MS).


  Lemma measure_mq_push : forall n_to p M MQ e dm,
      measure_mq n_to p M MQ = Some dm ->
      measure_mq n_to p M (MQ ++ [e]) = Some dm.
  Proof.
    intros.
    generalize dependent M dm.
    induction MQ; attac.
    - destruct b; attac.
    - destruct b; attac.
      unfold option_map in *.
      destruct (measure_mq n_to p (mon_handle a M) MQ) eqn:?; doubt.
      rewrite <- H in *.
      apply IHMQ in Heqo.
      now rewrite Heqo.
  Qed.

  Lemma measure_mq_fin_push : forall M MQ e dm,
      measure_mq_fin M MQ = Some dm ->
      measure_mq_fin M (MQ ++ [e]) = Some dm.

  Proof.
    intros.
    generalize dependent M dm.
    induction MQ; attac.
    - blast_cases; attac.
    - blast_cases; attac.
      unfold option_map in *.
      destruct (measure_mq_fin (mon_handle a m) MQ) eqn:?; doubt.
      rewrite <- H in *.
      apply IHMQ in Heqo.
      now rewrite Heqo.
  Qed.

  Hint Resolve measure_mq_push measure_mq_fin_push : LTS.


  Lemma measure_ms_decr : forall n (MS0 MS1 : MServ) a dm p,
      Flushing_act a ->
      (MS0 =(a)=> MS1) ->
      measure_ms n p MS0 = Some (S (S dm)) ->
      measure_ms n p MS1 = Some (S dm).

  Proof.
    intros.
    destruct MS0 as [MQ0 M0 S0].
    destruct MS1 as [MQ1 M1 S1].
    have (a = a).
    destruct_ma a; attac.
    all: unfold measure_ms in *.
    all: simpl in *; compat_hsimpl in *.
    - blast_cases; attac; blast_cases; attac.
    - blast_cases; attac; blast_cases; attac.
    - destruct (measure_mon n p (MSend (n0, &t) v M3)) eqn:?.
      attac.
      blast_cases; eattac.
    - blast_cases; attac.
  Qed.

  Lemma measure_ms_send : forall n (MS0 MS1 : MServ) a p,
      Flushing_act a ->
      (MS0 =(a)=> MS1) ->
      measure_ms n p MS0 = Some 1 ->
      a = send (n, R) ^ p.

  Proof.
    intros.
    destruct MS0 as [MQ0 M0 S0].
    destruct MS1 as [MQ1 M1 S1].
    have (a = a).
    destruct_ma a; attac.
    all: unfold measure_ms in *.
    all: simpl in *; compat_hsimpl in *.
    - destruct (measure_mon n p (MRecv s)) eqn:?.
      attac. blast_cases; attac.
      all:
        Control.enter (fun _ =>
                         match! goal with [h : measure_mq _ _ ?m _ = _ |- _] =>
                                            destruct (measure_mon n p $m) eqn:?;
                                              hsimpl in $h; attac; blast_cases; attac
                         end
          ).
    - blast_cases; attac; blast_cases; attac.
      all:
        Control.enter (fun _ =>
                         match! goal with [h : measure_mq _ _ ?m _ = _ |- _] =>
                                            destruct (measure_mon n p $m) eqn:?;
                                              hsimpl in $h; attac; blast_cases; attac
                         end
          ).
    - destruct (measure_mon n p (MSend (n0, &t) v M3)) eqn:?.
      attac.
      blast_cases; eattac.
      + destruct M3; attac; blast_cases; attac.
      + destruct M3; attac; blast_cases; attac.
      + unfold andb in *. blast_cases; attac.
      + destruct M3; attac; blast_cases; attac.
      + destruct M3; attac; blast_cases; attac.
    - blast_cases; attac; blast_cases; attac.
      all:
        Control.enter (fun _ =>
                         match! goal with [h : measure_mq _ _ ?m _ = _ |- _] =>
                                            destruct (measure_mon n p $m) eqn:?;
                                              hsimpl in $h; attac; blast_cases; attac
                         end
          ).
      destruct wait; attac; blast_cases; attac.
      destruct wait; attac; blast_cases; attac.
  Qed.

  Lemma measure_ms_fin_decr : forall (MS0 MS1 : MServ) a dm,
      Flushing_act a ->
      (MS0 =(a)=> MS1) ->
      measure_ms_fin MS0 = Some (S dm) ->
      measure_ms_fin MS1 = Some dm.

  Proof.
    intros.
    destruct MS0 as [MQ0 M0 S0].
    destruct MS1 as [MQ1 M1 S1].
    have (a = a).
    destruct_ma a; attac.
    all: unfold measure_ms_fin in *.
    all: simpl in *; compat_hsimpl in *.
    - blast_cases; attac; unfold option_map in *; blast_cases; attac.
    - blast_cases; attac; unfold option_map in *; blast_cases; attac.
    - destruct (measure_mon_fin (MSend (n, &t) v M3)) eqn:?.
      destruct MQ; attac; unfold option_map in *; blast_cases; attac.
    - blast_cases; attac; unfold option_map in *; blast_cases; attac.
  Qed.


  Lemma measure_ms_noincr : forall n (MS0 MS1 : MServ) a dm0 p,
      (MS0 =(a)=> MS1) ->
      measure_ms n p MS0 = Some dm0 ->
      (exists dm1, measure_ms n p MS1 = Some dm1 /\ dm1 <= dm0) \/ a = send (n, R) ^ p.

  Proof.
    intros.
    destruct MS0 as [MQ0 M0 S0].
    destruct MS1 as [MQ1 M1 S1].
    have (a = a).
    destruct_ma a; attac.
    all: unfold measure_ms in *.
    all: simpl in *; compat_hsimpl in *.
    all: blast_cases; attac; blast_cases; attac.
    destruct (measure_mon n p (MSend (n0, &t) v M3)) eqn:?.
    attac; blast_cases; eattac; unfold andb in *; blast_cases; attac.
  Qed.

  Lemma measure_ms_fin_noincr : forall (MS0 MS1 : MServ) a dm0,
      (MS0 =(a)=> MS1) ->
      measure_ms_fin MS0 = Some dm0 ->
      exists dm1, measure_ms_fin MS1 = Some dm1 /\ dm1 <= dm0.

  Proof.
    intros.
    destruct MS0 as [MQ0 M0 S0].
    destruct MS1 as [MQ1 M1 S1].
    have (a = a).
    destruct_ma a; attac.
    all: unfold measure_ms_fin in *.
    all: simpl in *; compat_hsimpl in *.
    all: eattac.
    all: blast_cases; attac; unfold option_map in *; blast_cases; eattac.
    all: destruct MQ; attac; unfold option_map in *; blast_cases; attac.
    all: attac.
    all: rewrite next_state_Send_all in *; attac.
  Qed.

  Lemma measure_mq_split : forall n_to p M MQ MQ' e dm,
      measure_mq n_to p M (MQ ++ [e]) = Some dm ->
      measure_mq n_to p M (MQ ++ e :: MQ') = Some dm.
  Proof.
    intros.
    generalize dependent M dm.
    induction MQ; attac.
    - destruct b; attac.
      blast_cases; attac.
    - destruct b; attac.
      unfold option_map in *.
      destruct (measure_mq n_to p (mon_handle a M) (MQ ++ [e])) eqn:?; doubt.
      rewrite <- H in *.
      apply IHMQ in Heqo.
      now rewrite Heqo.
  Qed.

  Fixpoint measure_lock_chain (MN : MNet) n0 L n1 p : option ((Name * Name) * DetectMeasure) :=
    match L with
    | [] =>
        match measure_ms n0 p (MN n1) with
        | Some mm => Some ((n0, n1), {|dm_pass := 1; dm_flush := mm|})
        | None => None
        end
    | n05 :: L =>
        match measure_ms n0 p (MN n05) with
        | Some mm => Some ((n0, n05), {|dm_pass := 1; dm_flush := mm|})
        | None =>
            match measure_lock_chain MN n05 L n1 p with
            | None => None
            | Some ((m0, m1), {|dm_pass:=dmp; dm_flush:=dmf|}) =>
                Some ((m0, m1), {|dm_pass:=S dmp; dm_flush:=dmf|})
            end
        end
    end.

  Definition measure_loop (MN : MNet) n L : option ((Name * Name) * DetectMeasure) :=
    match measure_ms_fin (MN n) with
    | Some dmf => Some ((n, n), {|dm_pass := 0; dm_flush := dmf|})
    | None =>
        measure_lock_chain MN n L n (active_probe_of MN n)
    end.


  Lemma measure_loop_end : forall MN n L m0 m1,
      measure_loop MN n L = Some ((m0, m1), {|dm_pass := 0; dm_flush := 0|}) ->
      alarm (MN n) = true.

  Proof.
    intros.
    destruct (alarm (MN n)) eqn:?; auto.
    exfalso.

    unfold measure_loop, NetGet, measure_ms, active_probe_of in *.
    blast_cases; attac.
    - destruct (NetMod.get m1 MN); attac.
      induction mserv_q0; attac.
      + induction mserv_m0; attac.
        unfold measure_ms_fin in *. simpl in *. attac.
      + unfold measure_ms_fin in *. simpl in *. attac.
        induction mserv_m0; attac.
        unfold option_map in *.
        blast_cases; attac.
        unfold option_map in *.
        blast_cases; attac.
    - induction L; attac; blast_cases; attac.
  Qed.

  Lemma measure_lock_chain_find : forall (MN0 : MNet) (n0 n1 m0 m1 : Name) (L : list Name) p dm,
      measure_lock_chain MN0 n0 L n1 p = Some (m0, m1, dm) ->
      measure_ms m0 p (MN0 m1) = Some (dm_flush dm).

  Proof.
    intros.
    destruct dm.
    generalize dependent n0 dm_pass0 dm_flush0.
    induction L; intros; simpl in *; hsimpl in *.
    - blast_cases; attac.
    - blast_cases; attac.
  Qed.


  Lemma measure_sp_true : forall (n : Name) p MS,
      sends_probe (n, R) p MS ->
      exists dmf, (measure_ms n p MS) = Some dmf.

  Proof.
    intros.
    unfold measure_ms.
    destruct (measure_mon n p MS) as [dmm found] eqn:?.

    remember (n, R) as nc.
    generalize dependent dmm.
    induction `(sends_probe _ _ _); intros.
    - hsimpl in *.
      enough (exists dmf,
                 measure_mq n p (MRecv c) (MQ ++ [MqRecv (n, Q) v]) = Some dmf) as [dmf ?]
          by eauto using measure_mq_split.

      destruct (measure_mon n p (MRecv c)) as [dmm found] eqn:?.
      hsimpl.
      consider (exists M, next_state M = c) by (exists (MRecv c); attac).
      destruct found; attac.
      generalize dependent M.
      induction MQ.
      1: { attac; destruct p; blast_cases; attac. blast_cases; attac. }
      intros.

      simpl.
      unfold option_map; attac.
      destruct (measure_mon n p (mon_handle a M)) as [dmm' found'] eqn:?.
      hsimpl.
      destruct found'; attac.

      specialize IHMQ with (M:=mon_handle a M) as [dmf ?]; eattac.
      {
        unfold NoRecvR_from in *; attac.
        intros ?.
        specialize H with v0.
        attac.
      }
      + destruct a; attac; blast_cases; attac.
        rewrite next_state_Send_all; attac.
      + destruct a; attac; blast_cases; attac.
        rewrite next_state_Send_all; attac.
      + destruct a; attac; blast_cases; attac.
        * unfold NoRecvR_from in *.
          specialize H with v0. bs.
        * rewrite next_state_Send_all; attac.
      + exists (S (add dmm' dmf)).
        destruct (MQ ++ [MqRecv (n, Q) v]); doubt.
        unfold option_map in *; attac.
        clear - H5; blast_cases; attac.
    - hsimpl in *.
      enough (exists dmf,
                 measure_mq n p (MRecv c) (MQ ++ [MqProbe (n', R) p]) = Some dmf) as [dmf ?]
          by eauto using measure_mq_split.

      destruct (measure_mon n p (MRecv c)) as [dmm found] eqn:?.
      hsimpl.
      consider (exists M, next_state M = c) by (exists (MRecv c); attac).
      destruct found; attac.
      generalize dependent M.
      induction MQ.
      1: { attac; destruct p; blast_cases; attac.
           rewrite <- Heqm in Heqp0.
           clear - Heqp0 H3. (* measure_mon, In  *)
           generalize dependent n0.
           induction wait; doubt.
           simpl in *.
           unfold andb in *.
           blast_cases; attac.
      }

      intros.
      simpl.

      unfold option_map; attac.
      destruct (measure_mon n p (mon_handle a M)) as [dmm' found'] eqn:?.
      hsimpl.
      destruct found'; attac.

      specialize IHMQ with (M:=mon_handle a M) as [dmf ?]; eattac.
      {
        unfold NoRecvR_from in *; attac.
        intros ?.
        specialize H with v.
        attac.
      }
      + destruct a; attac; blast_cases; attac.
        unfold andb in *;  blast_cases; attac.
        rewrite next_state_Send_all; attac.
      + destruct a; attac; blast_cases; attac.
        unfold andb in *;  blast_cases; attac.
        rewrite next_state_Send_all; attac.
      + destruct a; attac; blast_cases; attac.
        * unfold NoRecvR_from in *.
          specialize H with v. bs.
        * rewrite next_state_Send_all; attac.
      + exists (S (add dmm' dmf)).
        destruct (MQ ++ [MqProbe (n', R) p]); doubt.
        unfold option_map in *; attac.
        clear - H5; blast_cases; attac.
    - eattac.
      destruct (measure_mon n p (MSend (n, R) p M)) eqn:?.
      hsimpl.
      blast_cases; attac.
    - hsimpl in *.
      hsimpl in *.
      destruct found; attac.
      destruct nc'; attac.
      blast_cases; attac.
  Qed.


  Lemma unfold_measure_mq_fin_alarm : forall (M : MProc) MQ,
      alarm M = true -> measure_mq_fin M MQ = Some 0.
  Proof. destruct MQ; attac. Qed.

  Lemma unfold_measure_mq_fin_noalarm : forall (M : MProc) MQ,
      alarm M = false ->
      measure_mq_fin M MQ =
        match MQ with
        | [] => None
        | e :: MQ0 =>
            let (mm, s) := measure_mon_fin M in
            let M0 := mon_handle e s in option_map (add (S mm)) (measure_mq_fin M0 MQ0)
        end.
  Proof. destruct MQ; attac. Qed.

  Hint Rewrite -> unfold_measure_mq_fin_alarm unfold_measure_mq_fin_noalarm using spank : LTS LTS_concl.


  Lemma next_state_measure_fin : forall M mm c,
      measure_mon_fin M = (mm, c) ->
      next_state M = c.

  Proof. induction M; attac. blast_cases; attac. Qed.

  Hint Rewrite -> next_state_measure_fin using spank : LTS LTS_concl.


  Lemma measure_mq_fin_split : forall M MQ MQ' e dm,
      measure_mq_fin M (MQ ++ [e]) = Some dm ->
      measure_mq_fin M (MQ ++ e :: MQ') = Some dm.
  Proof.
    intros.
    generalize dependent M dm.
    induction MQ; attac.
    - destruct (alarm M); attac.
      blast_cases; attac.
    - destruct (alarm M) eqn:?; attac.
      unfold option_map in *.
      destruct (measure_mq_fin (mon_handle a m) (MQ ++ [e])) eqn:?; doubt.
      rewrite <- H in *.
      apply IHMQ in Heqo.
      now rewrite Heqo.
  Qed.

  Lemma measure_mq_fin_skip1 : forall M MQ e,
      measure_mq_fin M (MQ ++ [e]) = None ->
      measure_mq_fin M MQ = None.
  Proof.
    intros.
    generalize dependent M.
    induction MQ; attac.
    - destruct (alarm M); attac.
    - destruct (alarm M) eqn:?; attac.
      unfold option_map in *.
      destruct (measure_mq_fin (mon_handle a m) (MQ ++ [e])) eqn:?; doubt.
      blast_cases; attac.
  Qed.

  Lemma measure_mq_fin_skip : forall M MQ MQ' e,
      measure_mq_fin M (MQ ++ e :: MQ') = None ->
      measure_mq_fin M (MQ ++ [e]) = None.
  Proof.
    intros.
    generalize dependent M.
    induction MQ' using rev_ind; attac.
    rewrite app_comm_cons in H.
    rewrite app_assoc in H.
    apply measure_mq_fin_skip1 in H.
    attac.
  Qed.

  Lemma lock_NoRecvR_from : forall (MN : MNet) n0 n1,
      lock MN n0 n1 ->
      NoRecvR_from n1 (mserv_q (MN n0)).

  Proof.
    unfold NoRecvR_from.
    intros.
    unfold lock, lock_set, NetGet in *.
    attac.
    unfold deinstr in *; rewrite NetMod.get_map in *.
    destruct (NetMod.get n0 MN).
    consider (serv_lock _ _).
    unfold proc_lock in *.
    destruct P; attac.
    intros ?.
    specialize H3 with (n:=n1)(v:=v).
    blast_cases; attac.
    eapply H3; attac.
  Qed.

  Lemma measure_lock_chain_tip : forall (MN : MNet) n0 L n1 n2 p,
      measure_ms n1 p (MN n2) <> None ->
      measure_lock_chain MN n0 (L ++ [n1]) n2 p <> None.

  Proof.
    intros.
    generalize dependent n0.
    induction L; attac.
    - unfold measure_ms in *.
      blast_cases; attac.
    - blast_cases; attac.
  Qed.

  Lemma measure_lock_chain_mid : forall (MN : MNet) n0 L0 n1 n2 L1 n3 p,
      measure_ms n1 p (MN n2) <> None ->
      measure_lock_chain MN n0 (L0 ++ n1::n2::L1) n3 p <> None.

  Proof.
    intros.
    generalize dependent L1 n0 n1 n2.
    induction L0; attac.
    -  unfold measure_ms in *.
       blast_cases; attac.
    - blast_cases; attac.
  Qed.

  Lemma measure_lock_chain_mids : forall MN n0 L0 L1 n1 n2 p,
      measure_lock_chain MN n1 L1 n2 p <> None ->
      measure_lock_chain MN n0 (L0 ++ (n1::L1)) n2 p <> None.

  Proof.
    intros.

    generalize dependent n1 n2 L1.
    induction L0 using rev_ind; attac.
    - unfold measure_ms in *.
      blast_cases; attac.
    - rewrite <- app_assoc in *.
      simpl.
      specialize IHL0 with (L1:=n1::L1)(n1:=x).
      eapply IHL0; eattac.
      blast_cases; attac.
  Qed.

  Lemma measure_lock_chain_split : forall (MN0 : MNet) (n0 n1 m0 m1 : Name) (L : list Name) p dm,
      measure_lock_chain MN0 n0 L n1 p = Some (m0, m1, dm) ->
      exists L0 L1, n0 :: L ++ [n1] = L0 ++ m0 :: m1 :: L1
               /\ measure_ms m0 p (MN0 m1) = Some (dm_flush dm)
               /\ dm_pass dm = S (length L0).

  Proof.
    intros.
    generalize dependent n0 m0 m1 n1 dm.
    induction L; intros; simpl in *; hsimpl in *.
    - exists [], [].
      blast_cases. 2: attac.
      attac.
    - blast_cases; attac.
      + exists [], (L ++ [n1]); attac.
      + apply IHL in Heqo0.
        hsimpl in *.
        exists (n0::L0), L1.
        attac.
  Qed.


  Lemma measure_lock_chain_connect : forall (MN0 : MNet) (n0 n1 m0 m1 : Name) (L0 L1 : list Name) p dmm,
      ~ In n0 L0 ->
      NoDup L0 ->
      measure_ms m0 p (MN0 m1) = Some dmm ->
      exists m0' m1' dm',
      measure_lock_chain MN0 n0 (L0 ++ m0 :: m1 :: L1) n1 p = Some (m0', m1', dm')
      /\ dm_lep dm' {|dm_pass := S (S (length L0)); dm_flush := dmm |} = true.

  Proof.
    intros.

    generalize dependent n0 n1 m0 m1 L1.
    induction L0; intros.
    - attac.
      destruct (measure_ms n0 p (MN0 m0)) eqn:?.
      + exists n0, m0, {|dm_flush := n; dm_pass := 1|}. attac.
      + exists m0, m1, {|dm_flush := dmm; dm_pass := 2|}. attac.
        unfold dm_lep; attac.
    - hsimpl in *.
      destruct (measure_ms n0 p (MN0 a)) eqn:?.
      + eexists _, _, _. attac.
      + specialize IHL0 with
          (L1 := L1)
          (m1 := m1)
          (m0 := m0)
          (n0 := a)
          (n1 := n1).

        kill H0.
        specialize (IHL0 ltac:(auto)).
        specialize (IHL0 ltac:(auto)).
        specialize (IHL0 ltac:(auto)).
        hsimpl in *.
        eexists _, _, _. split. attac.
        attac.
  Qed.

  Lemma measure_lock_chain_connect_tip : forall (MN0 : MNet) (n0 n1 m0 : Name) (L0 : list Name) p dmm,
      ~ In n0 L0 ->
      NoDup L0 ->
      measure_ms m0 p (MN0 n1) = Some dmm ->
      exists m0' m1' dm',
      measure_lock_chain MN0 n0 (L0 ++ [m0]) n1 p = Some (m0', m1', dm')
      /\ dm_lep dm' {|dm_pass := S (S (length L0)); dm_flush := dmm |} = true.

  Proof.
    intros.

    generalize dependent n0 n1 m0.
    induction L0; intros.
    - attac.
      destruct (measure_ms n0 p (MN0 m0)) eqn:?.
      + exists n0, m0, {|dm_flush := n; dm_pass := 1|}. attac.
      + exists m0, n1, {|dm_flush := dmm; dm_pass := 2|}. attac.
        unfold dm_lep; attac.
    - hsimpl in *.
      destruct (measure_ms n0 p (MN0 a)) eqn:?.
      + eexists _, _, _. attac.
      + specialize IHL0 with
          (m0 := m0)
          (n0 := a)
          (n1 := n1).

        kill H0.
        specialize (IHL0 ltac:(auto)).
        specialize (IHL0 ltac:(auto)).
        specialize (IHL0 ltac:(auto)).
        hsimpl in *.
        eexists _, _, _. split. attac.
        attac.
  Qed.


  Lemma NoRecvQ_from_cons : forall n e MQ,
      NoRecvQ_from n (e :: MQ) <->
        NoRecvQ_from n MQ
        /\ match e with
          | MqRecv (n', Q) _ => n' <> n
          | _ => True
          end.

  Proof.
    unfold NoRecvQ_from; repeat split; repeat (intros ?).
    - eapply H; eattac.
    - blast_cases; eattac.
      specialize (H v); eattac.
    - destruct e; eattac.
      destruct `(_ \/ _); eattac.
  Qed.

  Hint Rewrite -> NoRecvQ_from_cons using assumption : LTS LTS_concl.

  Lemma NoRecvQ_from_app : forall n MQ0 MQ1,
      NoRecvQ_from n (MQ0 ++ MQ1) <->
        NoRecvQ_from n MQ0 /\ NoRecvQ_from n MQ1.

  Proof.
    induction MQ0; attac.
    - rewrite IHMQ0 in H; attac.
    - rewrite IHMQ0 in H; attac.
    - rewrite IHMQ0; attac.
  Qed.

  Hint Rewrite -> NoRecvQ_from_app using assumption : LTS LTS_concl.


  Lemma NoRecvR_from_cons : forall n e MQ,
      NoRecvR_from n (e :: MQ) <->
        NoRecvR_from n MQ
        /\ match e with
          | MqRecv (n', R) _ => n' <> n
          | _ => True
          end.

  Proof.
    unfold NoRecvR_from; repeat split; repeat (intros ?).
    - eapply H; eattac.
    - blast_cases; eattac.
      specialize (H v); eattac.
    - destruct e; eattac.
      destruct `(_ \/ _); eattac.
  Qed.

  Hint Rewrite -> NoRecvR_from_cons using assumption : LTS LTS_concl.

  Lemma NoRecvR_from_app : forall n MQ0 MQ1,
      NoRecvR_from n (MQ0 ++ MQ1) <->
        NoRecvR_from n MQ0 /\ NoRecvR_from n MQ1.

  Proof.
    induction MQ0; attac.
    - rewrite IHMQ0 in H; attac.
    - rewrite IHMQ0 in H; attac.
    - rewrite IHMQ0; attac.
  Qed.

  Hint Rewrite -> NoRecvR_from_app using assumption : LTS LTS_concl.

  Lemma NoRecvR_from_nil : forall n,
      NoRecvR_from n [] <-> True.

  Proof. unfold NoRecvR_from; attac. Qed.

  Lemma NoRecvQ_from_nil : forall n,
      NoRecvQ_from n [] <-> True.

  Proof. unfold NoRecvQ_from; attac. Qed.

  Hint Rewrite -> NoRecvR_from_nil NoRecvQ_from_nil using assumption : LTS LTS_concl.


  Ltac2 Notation "destruct_mna" a(constr) :=
    destruct $a as [? [[[? [|]]|[? [|]]|]|[[? ?]|[? ?]|]|[[? ?]|[? ?]|]] | ? ? [|] [?|?]]; doubt.

  Lemma measure_lock_chain_in_l : forall MN n0 L n1 p m0 m1 dm,
      measure_lock_chain MN n0 L n1 p = Some (m0, m1, dm) ->
      In m0 (n0::L).

  Proof.
    intros.
    generalize dependent n0 m0 m1 dm.
    induction L; attac.
    - blast_cases; attac.
    - blast_cases; attac.
  Qed.

  Lemma measure_lock_chain_in_r : forall MN n0 L n1 p m0 m1 dm,
      measure_lock_chain MN n0 L n1 p = Some (m0, m1, dm) ->
      In m1 (n1::L).

  Proof.
    intros.
    smash_eq n1 m1; attac.
    generalize dependent n0 n1 m0 m1 dm.
    induction L; attac.
    - blast_cases; attac.
    - blast_cases; attac.
  Qed.

  Lemma measure_ms_lock : forall MN n0 n1 n2 MQ p,
      KIC MN ->
      lock MN n0 n1 ->
      lock MN n1 n2 ->
      origin p <> n1 ->
      n0 <> n1 ->
      mserv_q (MN n1) = MQ ++ [MqProbe (n2, R) p] ->
      exists dmm, measure_ms n0 p (MN n1) = Some dmm.

  Proof.
    intros.
    unfold measure_ms.
    assert (NoRecvQ_from n0 MQ -> In n0 (wait (MN n1))).
    {
      intros.
      assert (NoRecvQ_from n0 (MQ ++ [MqProbe (n2, R) p])).
      {
        unfold NoRecvQ_from in *. intros ? ?.
        apply `(~ In (MqRecv (n0, Q) v) MQ).
        attac.
      }
      consider (KIC _).
      eapply H_wait_C; eauto.
      now rewrite `(mserv_q _ = _).
    }
    assert (locked (MN n1) = Some n2) by attac.
    assert (NoRecvR_from n2 MQ).
    {
      enough (NoRecvR_from n2  (MQ ++ [MqProbe (n2, R) p])) by attac.
      rewrite <- `(mserv_q _ = _).
      eauto using lock_NoRecvR_from.
    }
    assert (NoSends_MQ MQ).
    {
      enough (NoSends_MQ (MQ ++ [MqProbe (n2, R) p])) by attac.
      enough (NoSends_MQ (mserv_q (Transp.Net.NetMod.get n1 MN))) by (rewrite <- `(mserv_q _ = _); attac).
      enough (no_sends_in n1 MN) by  (unfold no_sends_in, NoMqSend, NetGet in *; destruct (NetMod.get n1 MN); attac).
      eauto using lock_M_no_sends_in.
    }
    assert (self (MN n1) = n1) by attac.

    unfold NetGet in *.
    destruct (NetMod.get n1 MN) as [MQ' M S].
    hsimpl in *.

    generalize dependent M.
    induction MQ; attac.
    - generalize dependent n.
      remember (wait M) as wl.
      clear Heqwl.
      destruct (next_state M); simpl in *; attac.
      generalize dependent n1.
      induction wl; attac. blast_cases; attac.
      unfold andb in *; blast_cases; attac.
    - specialize (IHMQ ltac:(auto) ltac:(auto)) with (M:=mon_handle a M).
      repeat (specialize (IHMQ ltac:(auto))).
      destruct b; attac.
      destruct (measure_mon n0 p (mon_handle a M)) eqn:?.
      attac. destruct b; attac.
      destruct IHMQ; attac.
      all: destruct a; simpl in *; blast_cases; eattac.
      all: try (rewrite next_state_Send_all in * ).
      all: attac.
      all: unfold andb in *; blast_cases; attac.
  Qed.


  Lemma measure_lock_chain_decr : forall (MN0 MN1 : MNet) (n0 n1 n2 m0 m1 : Name) (L : list Name) dm0 a p,
      KIC MN0 ->
      origin p = n0 ->
      lock_chain MN0 n0 L n1 ->
      lock MN0 n1 n2 ->
      NoDup L ->
      ~ In n0 L ->
      Flushing_NAct m1 a ->
      (MN0 =(a)=> MN1) ->
      measure_lock_chain MN0 n0 L n1 p = Some (m0, m1, dm0) ->
      dm_pass dm0 > 1 ->
      exists m0' m1' dm1, measure_lock_chain MN1 n0 L n1 p = Some (m0', m1', dm1) /\ dm_ltp dm1 dm0 = true.

  Proof.
    intros * HKIC0 ASDASD HL HL'.
    intros.

    assert (HKIC1 : KIC MN1) by eauto using KIC_invariant.

    apply measure_lock_chain_split in H3. hsimpl in *.

    assert (lock MN0 m0 m1) as HL0_m01.
    {
      destruct L0.
      1: bs.
      rewrite <- app_comm_cons in *.
      kill H3.
      destruct L1 using rev_ind.
      - consider (L = L0 ++ [m0] /\ n1 = m1).
        {
          clear - H8.
          replace (L0 ++ [m0;m1]) with ((L0 ++ [m0]) ++ [m1]) by attac.
          remember (L0 ++ [m0]) as chuj. clear Heqchuj.
          generalize dependent L.
          induction chuj; intros.
          + induction L; attac.
          + destruct L.
            * attac.
            * specialize (IHchuj L) as [? ?]; attac.
        }
        apply lock_chain_split in HL; attac.
      - repeat (rewrite app_comm_cons in * ).
        repeat (rewrite app_assoc in * ).
        consider ( (L0 ++ m0 :: m1 :: L1) = L /\ n1 = x).
        {
          clear - H8.
          remember (L0 ++ m0 :: m1 :: L1) as chuj. clear Heqchuj.
          generalize dependent L.
          induction chuj; intros.
          + induction L; attac.
          + destruct L.
            * attac.
            * specialize (IHchuj L) as [? ?]; attac.
        }
        apply lock_chain_split in HL; attac.
    }

    consider (exists m2, lock MN0 m1 m2).
    {
        destruct L0.
      1: bs.
      rewrite <- app_comm_cons in *.
      kill H3.
      destruct L1 using rev_ind.
      - consider (L = L0 ++ [m0] /\ n1 = m1).
        {
          clear - H8.
          replace (L0 ++ [m0;m1]) with ((L0 ++ [m0]) ++ [m1]) by attac.
          remember (L0 ++ [m0]) as chuj. clear Heqchuj.
          generalize dependent L.
          induction chuj; intros.
          + induction L; attac.
          + destruct L.
            * attac.
            * specialize (IHchuj L) as [? ?]; attac.
        }
        apply lock_chain_split in HL; attac.
      - repeat (rewrite app_comm_cons in * ).
        repeat (rewrite app_assoc in * ).
        consider ( (L0 ++ m0 :: m1 :: L1) = L /\ n1 = x).
        {
          clear - H8.
          remember (L0 ++ m0 :: m1 :: L1) as chuj. clear Heqchuj.
          generalize dependent L.
          induction chuj; intros.
          + induction L; attac.
          + destruct L.
            * attac.
            * specialize (IHchuj L) as [? ?]; attac.
        }
        apply lock_chain_split in HL; attac.
        kill HL1; attac.
    }


    have (MN0 =(a)=> MN1) as KURWA.

    destruct dm0; simpl in *; hsimpl in *.
    destruct dm_flush0 > [ | destruct dm_flush0 ].
    - exfalso.
      destruct (MN0 m1) as [MQ0 M0 S0].
      unfold measure_ms in *; simpl in *.
      destruct (measure_mon m0 p M0) eqn:?; attac; blast_cases; attac.
      destruct M0; attac; blast_cases; attac.
      induction n; attac.
    - assert (forall aa MS1, Flushing_act aa -> (MN0 m1 =(aa)=> MS1) -> aa = send (m0, R) ^ p)
        as H_send
        by eauto using measure_ms_send.

      kill H2.
      + unfold NetGet in *.
        hsimpl in *.
        specialize H_send with (aa:=a0)(MS1:=&S).
        repeat (specialize (H_send ltac:(assumption))).
        bs.
      + unfold active_probe_of, NetGet in *.
        specialize H_send with (aa:=send (n', &t) v)(MS1:=NetMod.get m1 N0').
        hsimpl in *.
        unfold send in *. simpl in *.
        specialize (H_send ltac:(destruct v; attac)).
        hsimpl in *.
        repeat (specialize (H_send ltac:(assumption))).
        destruct v; attac.

        destruct L0.
        1: { bs. }
        clear IHL0.

        rewrite <- app_comm_cons in *. simpl in *.
        kill H3.

        consider (exists L1' n1', m1 :: L1 = L1' ++ [n1']).
        {
          clear.
          induction L1 using rev_ind; attac.
          exists []; attac.
        }
        rewrite <- `(_ = m1 :: L1) in *.
        consider (L = L0 ++ m0 :: L1' /\ n1' = n1).
        {
          clear - H2.
          repeat (rewrite app_comm_cons in * ).
          repeat (rewrite app_assoc in * ).
          remember (L0 ++ m0 :: L1') as L'.
          clear HeqL'.
          generalize dependent L'.
          induction L; intros; hsimpl in * |-.
          - induction L'; attac.
          - induction L'.
            attac.
            rewrite <- app_comm_cons in *.
            rewrite <- app_comm_cons in *.
            kill H2.
            apply IHL in H0.
            attac.
        }
        clear H2.

        remember

          (NetMod.put m0
                      {| mserv_q := MQ0 ++ [MqProbe (m1, R) p]; mserv_m := M; mserv_s := P0 |}
                      (NetMod.put m1 {| mserv_q := MQ; mserv_m := M1; mserv_s := P |} MN0))

          as MN1.
        setoid_rewrite <- HeqMN1.
        setoid_rewrite <- HeqMN1 in HKIC1.

        remember (origin p) as n0.

        assert (exists dmm, measure_ms (last L0 n0) p {| mserv_q := MQ0 ++ [MqProbe (m1, R) p]; mserv_m := M; mserv_s := P0 |} = Some dmm).
        assert (exists dmm, measure_ms (last L0 n0) p (MN1 m0) = Some dmm).
        {
          assert (lock MN1 (last L0 n0) m0).
          {
            enough (lock MN0 (last L0 n0) m0).
            {
              erewrite <- deinstr_act_skip.
              eauto.
              2: subst; re_have eauto.
              attac.
            }
            destruct L0 using rev_ind.
            simpl in *.
            kill HL; attac.
            apply lock_chain_split in HL.
            rewrite last_last.
            kill HL.
            clear - H2.
            generalize dependent p.
            induction L0; attac.
          }
          assert (lock MN1 m0 m1).
          {
            erewrite <- deinstr_act_skip.
            eauto.
            2: subst; re_have eauto.
            attac.
          }
          eapply measure_ms_lock with (MQ:=MQ0); simpl; eauto.
          attac.
          clear - H H0. induction L0 using rev_ind; attac. rewrite last_last. attac.
          rewrite <- app_assoc in *.
          apply NoDup_app_remove_l in H. attac. kill H. attac.
          subst. clear. attac. unfold NetGet. attac.
        }
        subst.
        clear - H2.
        hsimpl in *.
        exists dmm.
        unfold NetGet in *; attac.
        clear KURWA.

        unfold active_probe_of, NetGet in *.
        attac.

        destruct L0 using rev_ind.
        1: { simpl in *. attac.
             unfold active_probe_of, NetGet in *.
             attac.
        }
        clear IHL0.

        rewrite <- app_assoc in *; simpl.
        rewrite last_last in *.

        remember (origin p) as n0.
        assert (~ In n0 L0) by attac.
        assert (NoDup L0) by (eauto using NoDup_app_remove_r).

        replace ( {| mserv_q := MQ0 ++ [MqProbe (m1, R) p]; mserv_m := M; mserv_s := P0 |}) with ( (NetMod.put m0 {| mserv_q := MQ0 ++ [MqProbe (m1, R) p]; mserv_m := M; mserv_s := P0 |}
                                                                                                      (NetMod.put m1 {| mserv_q := MQ; mserv_m := M1; mserv_s := P |} MN0)) m0) by (unfold NetGet; attac).

        eapply measure_lock_chain_connect with (L0:=L0)(L1:=L1')(n0:=n0)(n1:=n1) in H2; auto.
        hsimpl in *.
        exists m0', m1', dm'.
        split; auto.
        hsimpl in *.
        unfold NetGet; attac.
        clear - H12. rewrite PeanoNat.Nat.add_1_r. unfold dm_lep, dm_ltp in *.
        destruct dm'; simpl in *.
        destruct
          (dm_pass0 =? S (S (S (length L0)))) eqn:?,
          (dm_pass0 =? S (S (length L0))) eqn:?,
          (dm_flush0 =? dmm) eqn:?,
          (dm_flush0 <=? dmm) eqn:?,
          (dm_pass0 <=? S (S (S (length L0)))) eqn:?.
        all: try (rewrite PeanoNat.Nat.eqb_eq in * ).
        all: try (rewrite PeanoNat.Nat.eqb_neq in * ).
        all: try (rewrite PeanoNat.Nat.leb_le in * ).
        all: try (rewrite PeanoNat.Nat.ltb_lt in * ).
        all: try (lia).
    - destruct L0.
      1: { bs. }

      rewrite <- app_comm_cons in *.
      kill H3.

      assert (measure_ms m0 p (MN1 m1) = Some (S dm_flush0)).
      {
        remember (origin p) as n0.
        assert (n0 <> m0).
        {
          clear - H0 H8.
          generalize dependent m1 L1 L.
          induction L0; attac; induction L; attac.
        }

        assert (NoRecvQ_from m0 (mserv_q (MN0 m1)) -> In m0 (wait (MN0 m1))).
        {
          clear - HKIC0 HL0_m01.
          kill HKIC0.
          attac.
        }
        assert (NoRecvR_from m2 (mserv_q (MN0 m1))) by eauto using lock_NoRecvR_from.
        assert (NoSends_MQ (mserv_q (MN0 m1))).
        assert (no_sends_in m1 MN0) by eauto using lock_M_no_sends_in.
        unfold no_sends_in, NoMqSend in *. unfold NetGet in *; attac.
        destruct (NetMod.get m1 MN0); attac.

        subst.
        clear - H3 H6 H9 H10 Heqn0 H2 H5 H1.
        destruct (measure_mon m0 p (MN0 m1)) as [dm0 b0] eqn:?.
        destruct (measure_mon m0 p (MN1 m1)) as [dm1 b1] eqn:?.
        unfold measure_ms in *; simpl in *.

        unfold NetGet in *.
        subst.
        destruct (NetMod.get m1 MN0) as [MQ0 M0 S0] eqn:?.
        destruct (NetMod.get m1 MN1) as [MQ1 M1 S1] eqn:?.
        simpl in *.

        destruct a.
        - smash_eq m1 n.
          2: {
            replace (NetMod.get m1 MN1) with (NetMod.get m1 MN0) by eauto using NTau_neq_stay.
            attac.
          }

          consider (MN0 =(_)=> _).
          compat_hsimpl in *.
          rewrite `(NetMod.get m1 MN0 = _) in *.
          consider (_ =(_)=> _); compat_hsimpl in *.
          all: hsimpl in *.
          all: blast_cases; attac.
        - smash_eq m1 n.
          rename n0 into n.
          destruct p as [n0 nx]; simpl in *.
          destruct p0; consider (_ =(_)=> _); hsimpl in *.
          + smash_eq m1 n; hsimpl in *; blast_cases; attac.
            f_equal; attac.
            ltac1:(rewrite_strat innermost progress fold (l ++ [MqProbe (m1, Q) m]) in Heqo0).
            eapply measure_mq_push in Heqo; eauto.
            rewrite Heqo in Heqo0. attac.

            f_equal; attac.
            ltac1:(rewrite_strat innermost progress fold (l ++ [MqProbe (m1, R) m]) in Heqo0).
            eapply measure_mq_push in Heqo; eauto.
            rewrite Heqo in Heqo0. attac.
          + compat_hsimpl in *; bs.
      }

      simpl in *.

      remember (origin p) as n0.
      clear Heqn0.

      clear HL HL' HL0_m01 H7.

      generalize dependent m0 m1 n0 n1 L0 L1 dm_flush0.
      induction L; intros; hsimpl in *.
      {
        clear - H8.
        induction L0; attac.
      }

      destruct (measure_ms n0 p (MN1 a0)) eqn:?.
      1: { eexists _, _, _. split; attac. }

      rewrite <- app_comm_cons in *.
      destruct L0.
      + simpl in *.
        kill H8.
        destruct L; simpl in *.
        * kill H9.
          attac.
          eexists _, _, _. split. attac.
          clear.
          unfold dm_ltp, dm_lep; simpl.
          destruct
            (dm_flush0 =? S dm_flush0) eqn:?,
              (S dm_flush0 <=? S (S (S (dm_flush0)))) eqn:?.
          all: try (rewrite PeanoNat.Nat.eqb_eq in * ).
          all: try (rewrite PeanoNat.Nat.eqb_neq in * ).
          all: try (rewrite PeanoNat.Nat.leb_le in * ).
          all: try (rewrite PeanoNat.Nat.ltb_lt in * ).
          all: try (lia).
        * kill H9.
          hsimpl.
          eexists _, _, _. split. attac.
          clear.
          unfold dm_ltp, dm_lep; simpl.
          destruct
            (dm_flush0 =? S dm_flush0) eqn:?,
              (S dm_flush0 <=? S (S (S (dm_flush0)))) eqn:?.
          all: try (rewrite PeanoNat.Nat.eqb_eq in * ).
          all: try (rewrite PeanoNat.Nat.eqb_neq in * ).
          all: try (rewrite PeanoNat.Nat.leb_le in * ).
          all: try (rewrite PeanoNat.Nat.ltb_lt in * ).
          all: try (lia).
      + rewrite <- app_comm_cons in *.
        kill H8.

        consider (exists L1' n1', m1 :: L1 = L1' ++ [n1']).
        {
          clear.
          induction L1 using rev_ind; attac.
          exists []; attac.
        }
        rewrite <- `(_ = m1 :: L1) in *.
        consider (L = L0 ++ m0 :: L1' /\ n1 = n1').
        {
          clear - H9.
          kill H9.
          repeat (rewrite app_comm_cons in * ).
          repeat (rewrite app_assoc in * ).
          remember (L0 ++ m0 :: L1') as L'.
          clear HeqL'.
          generalize dependent L' n1 n1'.
          induction L; intros.
          induction L'; attac.
          destruct L'; hsimpl in * |- .
          attac.
          apply IHL in H0.
          attac.
        }
        clear H9.
        setoid_rewrite <- app_assoc in IHL.
        simpl in *.

        specialize IHL with
            (dm_flush0:=dm_flush0)
            (L0:=L0)
            (L1:=L1)
            (n0:=a0)
            (n1:=n1')
            (m0:=m0)
            (m1:=m1)
          .
          rewrite H7 in *.
          assert (NoDup (L0 ++ m0 :: L1')) by consider (NoDup _).
          assert (~ In a0 (L0 ++ m0 :: L1')) by consider (NoDup _).
          repeat (specialize (IHL ltac:(first [auto; lia]))).
          hsimpl in *.
          eexists _, _, _.
          attac.
  Qed.


  Lemma measure_loop_decr : forall (MN0 MN1 : MNet) (n m0 m1 : Name) (L : list Name) dm0 a,
      KIC MN0 ->
      lock_chain MN0 n L n ->
      NoDup L ->
      ~ In n L ->
      Flushing_NAct m1 a ->
      (MN0 =(a)=> MN1) ->
      measure_loop MN0 n L = Some (m0, m1, dm0) ->
      exists m0' m1' dm1, measure_loop MN1 n L = Some (m0', m1', dm1) /\ alarm (MN0 n) || dm_ltp dm1 dm0 = true.

  Proof.
    intros.
    unfold measure_loop in *.

    replace (active_probe_of MN1 n) with (active_probe_of MN0 n).
    2: {
      eapply deadlocked_preserve_active_probe_of1; eauto with LTS.
      eapply dep_self_deadlocked; eauto with LTS.
    }

    blast_cases; attac.
    - eexists _, _, _. split. attac.

      destruct (alarm (MN0 m1)) eqn:?; attac.

      unfold NetGet in *.
      destruct_mna a; consider (Flushing_NAct m1 _); consider (MN0 =(_)=> MN1).
      all: compat_hsimpl in *; attac.
      all: unfold measure_ms_fin in *; simpl in *.
      all: rewrite `(NetMod.get m1 MN0 = _) in *.
      all: simpl in *; hsimpl in *.
      all: unfold option_map in *; blast_cases; attac.
      all: unfold option_map in *; blast_cases; attac.
      all: unfold dm_ltp, dm_lep; simpl.

      all: try (Control.enter (fun () => match! goal with [|- (if ?x then _ else _) = _] => destruct $x eqn:? end)).
      all: try (rewrite PeanoNat.Nat.eqb_eq in * ).
      all: try (rewrite PeanoNat.Nat.eqb_neq in * ).
      all: try (rewrite PeanoNat.Nat.leb_le in * ).
      all: try (rewrite PeanoNat.Nat.ltb_lt in * ).
      all: try (lia).

      smash_eq n2 m1; attac; unfold option_map in *; blast_cases; attac.
      ltac1:(rewrite_strat innermost progress fold (n3 + n) in Heqo0).
      ltac1:(rewrite_strat innermost progress fold (n3 + n4) in Heqo0).
      simpl in *.
      assert (n = S n4). clear - Heqo0. induction n3; attac.
      erewrite measure_mq_fin_push in Heqo; eauto.
      attac.

      smash_eq n2 m1; attac; unfold option_map in *; blast_cases; attac.
      ltac1:(rewrite_strat innermost progress fold (_ + _) in Heqb0).
      ltac1:(rewrite_strat innermost progress fold (n3 + n4) in Heqb0).
      ltac1:(rewrite_strat innermost progress fold (_ + _)).
      ltac1:(rewrite_strat innermost progress fold (n3 + n4)).
      erewrite measure_mq_fin_push in Heqo; eauto.
      attac.

      smash_eq n2 m1; attac; unfold option_map in *; blast_cases; attac.
      erewrite measure_mq_fin_push in Heqo; eauto.
      attac. attac.

      attac.
      destruct s; attac.
      setoid_rewrite Heqo2 in Heqo. attac.

      smash_eq n2 m1; attac; unfold option_map in *; blast_cases; attac.
      erewrite measure_mq_fin_push in Heqo; eauto.
      attac. attac.

      destruct s; attac.
      erewrite measure_mq_fin_push in Heqo; eauto.
      attac.

      erewrite measure_mq_fin_push in Heqo; eauto.
      attac.


      attac.
      attac.
      ltac1:(rewrite_strat innermost progress fold (_ + _) in Heqb0).
      ltac1:(rewrite_strat innermost progress fold (n3 + n4) in Heqb0).
      ltac1:(rewrite_strat innermost progress fold (_ + _)).
      ltac1:(rewrite_strat innermost progress fold (n3 + n4)).
      erewrite measure_mq_fin_push in Heqo; eauto.
      attac.
      unfold lt.


      ltac1:(rewrite_strat innermost progress fold (n3 + n4) in Heqo0).
      simpl in *.
      assert (n = S n4). clear - Heqo0. induction n3; attac.
      erewrite measure_mq_fin_push in Heqo; eauto.
      attac.


    - consider (exists n', lock MN0 n n') by (consider (lock_chain '' MN0 n L n); attac).
      eapply measure_lock_chain_decr; eauto.
      simpl; lia.



  Lemma measure_lock_chain_split : forall MN n0 L n1 m0 m1 p,
      measure_lock_chain MN n1 L1 n2 p = Some (m0, m1,. ) ->
      measure_lock_chain MN n0 (L0 ++ (n1::L1)) n2 p <> None.


  Lemma measure_ac : forall (MN0 : MNet) (n : Name) (L : list Name),
      (KIC MN0) ->
      (lock_chain '' MN0 n L n) ->
      alarm_condition n MN0 ->
      measure_loop MN0 n L <> None.

  Proof.
    intros.
    kill H1.
    - unfold measure_loop, NetGet, measure_ms_fin in *.
      destruct (NetMod.get n MN0); simpl in *.
      destruct (measure_mon_fin mserv_m0) eqn:?.
      compat_hsimpl.
      congruence.
    - unfold measure_loop.
      blast_cases; eattac.

      smash_eq m n.
      + destruct L; hsimpl in *.
        * consider (m' = m) by (eapply SRPC_lock_set_uniq; eauto with LTS).
          eattac.
          blast_cases; eattac.
          unfold measure_ms, NetGet in *; simpl in *.
          destruct (NetMod.get m MN0) as [MQ0 M0 S0] eqn:?.
          simpl in *.
          apply measure_sp_true in H4; unfold measure_ms in *; simpl in *.
          eattac.
        * consider (m' = n) by (eapply SRPC_lock_set_uniq; eauto with LTS).
          eattac.
          blast_cases; eattac.
          unfold measure_ms, NetGet in *; simpl in *.
          destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.
          simpl in *.
          apply measure_sp_true in H4; unfold measure_ms in *; simpl in *.
          eattac.
      + destruct `(_ \/ _); doubt.

        assert (In m L \/ m = n) as [|].
        {
          consider (exists L', lock_chain '' MN0 n L' m /\ ~ In m L')
            by eauto using dep_lock_chain with LTS.
          eapply lock_chain_loop_in; eauto with LTS; consider (KIC _); eapply SRPC_lock_set_uniq; eauto with LTS.
        }
        2: bs.

        apply lock_chain_split_in with (n1:=m) in H0; eauto.
        hsimpl in *.
        apply measure_sp_true in H4.
        destruct L1; hsimpl in *.
        * consider (m' = n) by (eapply SRPC_lock_set_uniq; eauto with LTS).
          eapply measure_lock_chain_tip. attac.
        * consider (n0 = m') by (eapply SRPC_lock_set_uniq; eauto with LTS).
          eapply measure_lock_chain_mid. attac.

    - unfold measure_loop, measure_ms_fin, active_ev_of, active_probe_of in *.
      apply in_split in H3 as (MQ & MQ' & ?).
      rewrite H1.

      assert (locked (MN0 n) = Some n') by attac.
      assert (NoRecvR_from n' (mserv_q (MN0 n))) by eauto using lock_NoRecvR_from.
      assert (no_sends_in n MN0) by eauto using lock_M_no_sends_in.
      clear H0 H2.

      assert (self (MN0 n) = n) by attac.
      destruct (alarm (MN0 n)) eqn:?.
      1: { compat_hsimpl; congruence. }

      destruct (measure_mq_fin (MN0 n)
                  (MQ ++ MqProbe (n', R) {| origin := n; lock_id := lock_count (MN0 n) |} :: MQ')) eqn:?.
      1: eattac.
      exfalso.
      unfold no_sends_in in *.
      apply measure_mq_fin_skip in Heqo.
      unfold NetGet in *.
      destruct (NetMod.get n MN0); simpl in *.
      hsimpl in *.
      clear - Heqo Heqb H3 H0 H4 H5.

      clear Heqb.
      generalize dependent mserv_m0.
      induction MQ; attac.
      + unfold option_map in *.
        induction mserv_m0; attac.
        * destruct state; attac. attac.
        * compat_hsimpl in *.
          destruct (measure_mon_fin mserv_m0) eqn:?.
          destruct m; attac.
          attac.
      + unfold option_map in *.
        destruct (measure_mon_fin mserv_m0) eqn:?.
        destruct (alarm (mon_handle a m)) eqn:?; compat_hsimpl in *; doubt.
        unfold option_map in *.
        specialize (IHMQ (mon_handle a mserv_m0)).
        replace (self (mon_handle a mserv_m0)) with (self mserv_m0)
          by (clear; destruct a; simpl; blast_cases; attac; rewrite next_state_Send_all; attac).
        replace (lock_count (mon_handle a mserv_m0)) with (lock_count mserv_m0)
          by (clear - H5; destruct a; simpl; blast_cases; attac; rewrite next_state_Send_all; attac).
        replace (locked (mon_handle a mserv_m0)) with (locked mserv_m0)
          by (clear - H4 H3 H5; unfold NoRecvR_from in *; destruct a; simpl; blast_cases; attac; try (specialize H4 with v); try (rewrite next_state_Send_all); attac).

        specialize (IHMQ ltac:(auto)).
        specialize (IHMQ ltac:(auto) ltac:(auto)).

        assert (NoRecvR_from n'
                  (MQ ++
                     MqProbe (n', R) {| origin := self mserv_m0; lock_id := lock_count mserv_m0 |} :: MQ')).
        {
          unfold NoRecvR_from in *.
          intros ? ?.
          eapply H4 with (v:=v).
          eattac.
        }
        specialize (IHMQ ltac:(auto)).
        destruct (MQ ++ [MqProbe (n', R) {| origin := self mserv_m0; lock_id := lock_count mserv_m0 |}]) eqn:?; doubt.
        setoid_rewrite Heql in Heqo.
        setoid_rewrite Heql in IHMQ.
        clear H4.
        blast_cases; attac.
        blast_cases; attac.
        blast_cases; attac.
  Qed.


  Lemma measure_lock_chain_find : forall (MN0 : MNet) p (n0 n1 m : Name) (L : list Name),
      snd (measure_lock_chain p MN0 L n0) = Some m ->
      measure_ms n0 p (NetMod.get m MN0) =
        ( ( dm_mon (fst (measure_lock_chain p MN0 L n0)),
            dm_mque (fst (measure_lock_chain p MN0 L n0))
          ),
          true
        ).

  Proof.
    intros.
    induction L; intros; simpl in *.
    - destruct (measure_ms n0 p (NetMod.get n0 MN0)) as [? [|]] eqn:?.
      2: { destruct p0; bs. }

      destruct p0.
      attac.
    - destruct (measure_ms n0 p (NetMod.get a MN0)) as [? [|]] eqn:?.
      2: { destruct p0; attac. }

      destruct p0.
      attac.
  Qed.

  Lemma measure_mq_push : forall n p MQ0 e mq0,
      (mq0, true) = measure_mq n p MQ0 ->
      (mq0, true) = measure_mq n p (MQ0 ++ [e]).

  Proof.
    induction MQ0.
    1: { attac. }

    intros.
    specialize (IHMQ0 e).
    hsimpl in *.
    blast_cases; attac.
    all: specialize (IHMQ0 _ eq_refl); attac.
  Qed.



  (** ********************** *)
  Inductive DetectMeasure := DM {dm_mon : nat; dm_mque : nat; dm_vis : nat}.

  Definition dm_lep (dm0 dm1 : DetectMeasure) : bool :=
    let c0 := dm_mon in
    let c1 := dm_mque in
    let c2 := dm_vis in
    let next c f :=
      match (c dm0 =? c dm1) with
      | true => f
      | _ => (c dm0 <=? c dm1)
      end
    in next c2 (next c1 (next c0 true)).

  Definition dm_ltp (dm0 dm1 : DetectMeasure) : bool :=
    let c0 := dm_mon in
    let c1 := dm_mque in
    let c2 := dm_vis in
    let next c f :=
      match (c dm0 =? c dm1) with
      | true => f
      | _ => (c dm0 <? c dm1)
      end
    in next c2 (next c1 (next c0 false)).

  Definition dm_eqb (dm0 dm1 : DetectMeasure) : bool :=
    match
      (dm_mon dm0 =? dm_mon dm1)%nat,
      (dm_mque dm0 =? dm_mque dm1)%nat,
      (dm_vis dm0 =? dm_vis dm1)%nat with
    | true, true, true => true
    | _, _, _ => false
    end.

  Fixpoint measure_mq nl p MQ0 : nat * bool :=
    match MQ0 with
    | [] => (0, false)
    | MqProbe (n, R) p' :: MQ0 =>
        if NAME.eqb (origin p) (origin p')
           && (lock_id p =? lock_id p')%nat
           && (NAME.eqb n nl)
        then (1, true)
        else
          let (m, found) := measure_mq nl p MQ0 in
          (S m, found)
    | _ :: MQ0 =>
        let (m, found) := measure_mq nl p MQ0
        in (S m, found)
    end.

  Fixpoint measure_init n_to MQ0 : nat * bool :=
    match MQ0 with
    | [] => (0, false)
    | MqRecv (n_from, Q) _ :: MQ0 =>
        if NAME.eqb n_from n_to
        then (1, true)
        else
          let (m, found) := measure_init n_to MQ0
          in (S m, found)
    | _::MQ0 =>
        let (m, found) := measure_init n_to MQ0
        in (S m, found)
    end.

  Fixpoint measure_mon p M0 : (nat * bool) :=
    match M0 with
    | MRecv _ => (0, false)
    | MSend _ p' M0 =>
        if NAME.eqb (origin p) (origin p')
           && (lock_id p =? lock_id p')%nat
        then (1, true)
        else
          let (m, found) := measure_mon p M0 in
          (S m, found)
    end.

  Definition measure_ms p MS : ((nat * nat) * bool) := (* M MQ *)
    let (mm, found_m) := measure_mon p (mserv_m MS) in
    if found_m then ((mm, 0), true)
    else
      match locked MS with
      | None => (0, 0, false)
      | Some nl =>
          let (mq, found_q) := measure_mq nl p (mserv_q MS) in
          ((mm, mq), found_q)
      end.

  Definition measure_ms_init n_to (MS : MServ) : ((nat * nat) * bool) := (* M MQ *)
    let (mm, found_m) := measure_mon {|origin:=self MS; lock_id:=lock_count MS|} (mserv_m MS) in
    if found_m then ((mm, 0), true)
    else
      let (mq, found_q) := measure_init n_to (mserv_q MS) in
      ((mm, mq), found_q).


  Fixpoint measure_lock_chain (p : MProbe) (MN : MNet) (n_prev : Name) (L : list Name) (n : Name) : (DetectMeasure * option Name) :=
    match L with
    | [] =>
        match measure_ms_init n_prev (NetMod.get n MN) with
          ((mm, mq), found) =>
            ({|dm_mon := mm; dm_mque := mq; dm_vis := 1|},
              if found then Some n else None
            )
        end
    | m::L =>
        match measure_ms p (NetMod.get m MN) with
        | ((mm, mq), true) =>
            ({|dm_mon := mm; dm_mque := mq; dm_vis := 1|}, Some m)
        | _ =>
            let (dm, found_name) := measure_lock_chain p MN m L n in
            ({|dm_mon := dm_mon dm; dm_mque := dm_mque dm; dm_vis := S (dm_vis dm)|},
              found_name
            )
        end
    end.



  Definition measure_loop (MN : MNet) (L : list Name) (n : Name) : (DetectMeasure * option Name) :=
    if alarm (MN n)
    then ({|dm_mon := 0; dm_mque := 0; dm_vis := 0|}, Some n)
    else
      match measure_mq n (active_probe_of MN n) (mserv_q (MN n)) with
      | (mq, true) =>
          ({|dm_mon := ; dm_mque := mq; dm_vis := 0|}, Some n)
      | _ =>
          measure_lock_chain (active_probe_of MN n) MN n L n
      end.

  Lemma measure_loop_end : forall MN L n m,
    measure_loop MN L n = ({|dm_mon := 0; dm_mque := 0; dm_vis := 0|}, Some m) ->
    alarm (MN n) = true.

  Proof.
    intros.
    destruct (alarm (MN n)) eqn:?; auto.
    exfalso.

    unfold measure_loop, NetGet, measure_ms, active_probe_of in *.
    rewrite Heqb in *.
    blast_cases; attac.
    destruct (NetMod.get m MN); attac.
    attac.
  Qed.


  Lemma measure_sp_true : forall (n : Name) p MS,
      sends_probe (n, R) p MS ->
      snd (measure_ms p MS) = true.

  Proof.
    intros.
    unfold measure_ms.
    induction H.
    - blast_cases; attac.

      (* destruct c; simpl in *; destruct alarm; doubt. *)
      (* hsimpl in *. *)

      generalize dependent n0 n2 n' p b0.
      induction MQ; intros; attac.
      + blast_cases; attac.
        destruct b0; auto.
        exfalso.
        setoid_rewrite <- H2 in Heqb1.
        setoid_rewrite <- H3 in Heqb1.
        setoid_rewrite NAME_H.same_eqb_inv in Heqb1.
        rewrite PeanoNat.Nat.eqb_refl in Heqb1.
        bs.
      + blast_cases; attac.
        * eapply IHMQ; eauto.
          unfold NoRecvR_from in *.
          intros.
          specialize (H v1).
          attac.
        * eapply IHMQ; eauto.
          unfold NoRecvR_from in *.
          intros.
          specialize (H v1).
          attac.
        * eapply IHMQ; eauto.
          unfold NoRecvR_from in *.
          intros.
          specialize (H v0).
          attac.
        * eapply IHMQ; eauto.
          unfold NoRecvR_from in *.
          intros.
          specialize (H v0).
          attac.
    - blast_cases; attac.

      destruct c; simpl in *; doubt.
      hsimpl in *.

      destruct b0; auto.
      exfalso.

      generalize dependent n0 n2 n' p.
      induction MQ; intros; attac.
      + blast_cases; attac.
        rewrite PeanoNat.Nat.eqb_refl in Heqb0.
        simpl in *.
        bs.
      + unfold NoRecvR_from in *; hsimpl in *.
        blast_cases; attac.
        * eapply IHMQ; eauto.
          intros.
          specialize (H v0).
          attac.

          destruct `(_ \/ _). attac.
          specialize (H v0).
          eattac.
        * eapply IHMQ; eauto.
          unfold NoRecvR_from in *.
          intros.
          specialize (H v).
          attac.
    - blast_cases; attac.
      rewrite PeanoNat.Nat.eqb_refl in *.
      bs.
    - blast_cases; attac.
      destruct p, p'.
      simpl in *.
      blast_cases; attac.
  Qed.


  Lemma measure_ac : forall (MN0 : MNet) (n : Name) (L : list Name),
      (KIC MN0) ->
      (lock_chain '' MN0 n L n) ->
      alarm_condition n MN0 ->
      exists m, snd (measure_loop MN0 L n) = Some m.

  Proof.
    intros.
    kill H1.
    - exists n.
      unfold measure_loop.
      rewrite `(alarm _ = true); eauto.
    - unfold measure_loop.
      blast_cases; eattac.
      blast_cases; eattac.
      unfold measure_ms in *.
      destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.
      simpl in *.
      blast_cases; eattac.

      destruct `(_ \/ _); subst.
      + destruct L.
        * hsimpl in *.
          consider (m' = m) by (eapply SRPC_lock_set_uniq; eauto with LTS).
          eattac.
          blast_cases; eattac.
          apply measure_sp_true in H4.
          unfold measure_ms in *; simpl in *.
          blast_cases; eattac.
        * hsimpl in *.
          consider (m' = n) by (eapply SRPC_lock_set_uniq; eauto with LTS).
          eattac.
          blast_cases; eattac.
          apply measure_sp_true in H4.
          unfold measure_ms in *; simpl in *.
          blast_cases; eattac.
      + apply measure_sp_true in H4; unfold measure_ms in *; simpl in *.
        consider (exists L', lock_chain '' MN0 n L' m' /\ ~ In m' L')
          by eauto using dep_lock_chain with LTS.

        assert (In m' L \/ m' = n) as [|] by
          (eapply lock_chain_loop_in; eauto with LTS; consider (KIC _); eapply SRPC_lock_set_uniq; eauto with LTS).
        2: { eattac. }

        apply (lock_chain_split_in `(In m' L)) in H0.
        hsimpl in *.

        clear H7 H3 H2 H1 H5 H6 L'.

        generalize dependent n L1 m' d o n0 n1.
        induction L0; intros; simpl in *.
        * hsimpl in *.
          unfold measure_ms in *.
          blast_cases; eattac.
        * blast_cases; eattac.
          -- eapply IHL0 in Heqp4; eauto.
             blast_cases; eattac.
          -- eapply IHL0 in Heqp4; eauto.
             blast_cases; eattac.
    - unfold active_ev_of, NetGet in *.
      destruct (NetMod.get n MN0) eqn:?.
      simpl in *.
      exists n.
      unfold measure_loop, measure_ms in *.
      destruct (alarm (MN0 n)); eauto.
      hsimpl in *. subst.
      destruct b; auto.

      unfold active_probe_of, NetGet, measure_ms in *.
      rewrite `(NetMod.get _ _ = _) in *; simpl in *.
      clear - Heqp H3.
      exfalso.
      generalize dependent n0 n1.
      induction mserv_m0; intros; eattac.
      + generalize dependent n0 n1.
        induction mserv_q0; eattac.
        destruct a; attac.
        * eapply IHmserv_q0. eauto.
          rewrite <- Heqp.
          blast_cases; attac.
        * eapply IHmserv_q0. eauto.
          rewrite <- Heqp.
          blast_cases; attac.
        * kill H3; attac.
          -- blast_cases; attac.
             bs (&lock_count <> &lock_count) by (eapply PeanoNat.Nat.eqb_neq; eauto).
          -- eapply IHmserv_q0. eauto.
             rewrite <- Heqp.
             blast_cases; attac.
      + blast_cases; attac.
  Qed.


  Lemma measure_lock_chain_find : forall (MN0 : MNet) p (n0 n1 m : Name) (L : list Name),
      snd (measure_lock_chain p MN0 L n0) = Some m ->
      measure_ms n0 p (NetMod.get m MN0) =
        ( ( dm_mon (fst (measure_lock_chain p MN0 L n0)),
            dm_mque (fst (measure_lock_chain p MN0 L n0))
          ),
          true
        ).

  Proof.
    intros.
    induction L; intros; simpl in *.
    - destruct (measure_ms n0 p (NetMod.get n0 MN0)) as [? [|]] eqn:?.
      2: { destruct p0; bs. }

      destruct p0.
      attac.
    - destruct (measure_ms n0 p (NetMod.get a MN0)) as [? [|]] eqn:?.
      2: { destruct p0; attac. }

      destruct p0.
      attac.
  Qed.

  Lemma measure_mq_push : forall n p MQ0 e mq0,
      (mq0, true) = measure_mq n p MQ0 ->
      (mq0, true) = measure_mq n p (MQ0 ++ [e]).

  Proof.
    induction MQ0.
    1: { attac. }

    intros.
    specialize (IHMQ0 e).
    hsimpl in *.
    blast_cases; attac.
    all: specialize (IHMQ0 _ eq_refl); attac.
  Qed.



  Lemma measure_non_incr : forall (MN0 MN1 : MNet) (n : Name) (L : list Name) (a : MNAct),
      (KIC MN0) ->
      (lock_chain '' MN0 n L n) ->
      alarm_condition n MN0 ->
      (MN0 =(a)=> MN1) ->
      dm_lep (fst (measure_loop MN1 L n)) (fst (measure_loop MN0 L n)) = true.
  Proof.
    intros.

    destruct (alarm (MN0 n)) eqn:?.
    {
      unfold measure_loop.
      assert (alarm (MN1 n) = true) by eauto using net_preserve_alarm.
      attac.
    }

    destruct (alarm (MN1 n)) eqn:?.
    {
      unfold measure_loop.
      attac.
      unfold dm_lep; blast_cases; attac.
    }

    consider (exists m, snd (measure_loop MN0 L n) = Some m) by eauto using measure_ac.
    unfold measure_loop in *.
    rewrite Heqb in *.
    eassert (measure_ms _ _ _ = _) by (eapply measure_lock_chain_find; eauto).
    unfold measure_loop in *; attac.

    kill H1; auto.
    - admit.
    - unfold NetGet, active_ev_of in *.
      destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?; simpl in *.
      destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?; simpl in *.
      replace (active_probe_of MN1 n) with (active_probe_of MN0 n)
        by eauto using deadlocked_preserve_active_probe_of1, dep_self_deadlocked with LTS.
      unfold measure_ms, active_probe_of, NetGet in *.
      hsimpl in *.

      consider (_ =(_)=> _); compat_hsimpl in *.
      + smash_eq n n4; hsimpl in *.
        * rewrite Heqm0 in *.
          consider (_ =(_)=> _).
          -- compat_hsimpl in *; hsimpl in *.
             destruct s; simpl in *.
             destruct n4.
             clear Heqp1.

      destruct_mna a; consider (_ =(_)=> _); compat_hsimpl in *.
      + smash_eq n n4; hsimpl in *.
        * rewrite Heqm0 in *.
          destruct (measure_mon {| origin := n; lock_id := lock_count M1 |} M1).
          destruct b1; hsimpl in *.
          clear; unfold dm_lep; blast_cases; attac. admit. (* ez *)

          destruct

        blast_cases; attac.

      clear - H6 Heqp Heqp2.


      assert (trans_lock MN0 n n) by eauto with LTS.
      eapply dep_self_deadlocked.

    eapply measure_ac in H1 as (m' & ?); eauto.
    unfold measure_loop in *. rewrite `(alarm (MN0 _) = _) in H1.
    eassert (measure_ms _ _ _ = _) by (eapply measure_lock_chain_find; eauto).


    kill H1; auto.
    - admit.
    - clear H0
      unfold measure_loop, NetGet, active_ev_of, active_probe_of in *; attac.
      destruct_mna a; consider (_ =(_)=> _); compat_hsimpl in *.

      destruct (NetMod.get n MN0).
      destruct (NetMod.get n MN0).
      unfold measure_ms in *.
      simpl in *.
      induction
      destruct b; simpl in *.

    consider (exists m, snd (measure_loop MN0 L n) = Some m) by eauto using measure_ac.
    unfold measure_loop in *.


    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.
    destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.

    (* assert (forall n0 n1 t v, a = NComm n0 n1 t # v -> ~ In n0 L) as HNosendL. *)
    (* { *)
    (*   intros. *)
    (*   subst. *)
    (*   intros ?. *)
    (*   assert (trans_lock MN0 n0 n) by (apply lock_chain_split_in with (n1:=n0) in H; attac). *)
    (*   absurd (n0 <> n0); consider (trans_lock _ n0 n); eauto using locked_M_no_send with LTS. *)
    (* } *)

    induction L.
    - admit.
    -

    destruct_mna a; consider (_ =(_)=> _); compat_hsimpl in *.

    - unfold dm_lep, active_probe_of in *.










  Inductive boolp : Prop := truep | falsep.
  Inductive natp : Prop := zerop | succp (n : natp).

  Fixpoint eqp (n0 n1 : natp) : boolp :=
    match n0, n1 with
    | zerop, zerop => truep
    | succp n0, succp n1 => eqp n0 n1
    | _, _ => falsep
    end.

  Fixpoint lep (n m : natp) {struct n} : boolp :=
    match n with
    | zerop => truep
    | succp n' => match m with
             | zerop => falsep
             | succp m' => lep n' m'
             end
    end.

  Definition ltp (n0 n1 : natp) : boolp :=
    lep (succp n0) n1.

  Inductive DetectMeasure : Prop := DM {dm_mon : natp; dm_mque : natp; dm_vis : natp}.

  Definition dm_lep (dm0 dm1 : DetectMeasure) : boolp :=
    let c0 := dm_mon in
    let c1 := dm_mque in
    let c2 := dm_vis in
    let next c f :=
      match eqp (c dm0) (c dm1) with
      | truep => f
      | _ => lep (c dm0) (c dm1)
      end
    in next c0 (next c1 (next c2 truep)).

  Definition dm_ltp (dm0 dm1 : DetectMeasure) : boolp :=
    let c0 := dm_mon in
    let c1 := dm_mque in
    let c2 := dm_vis in
    let next c f :=
      match eqp (c dm0) (c dm1) with
      | truep => f
      | _ => ltp (c dm0) (c dm1)
      end
    in next c0 (next c1 (next c2 falsep)).

  Goal dm_lep (DM zerop zerop zerop) (DM zerop zerop zerop) = truep. reflexivity. Qed.
  Goal dm_lep (DM zerop zerop zerop) (DM (succp zerop) zerop zerop) = truep. reflexivity. Qed.
  Goal dm_lep (DM zerop zerop zerop) (DM zerop zerop (succp zerop)) = truep. reflexivity. Qed.
  Goal dm_lep (DM (succp zerop) zerop zerop) (DM zerop zerop zerop) = falsep. reflexivity. Qed.
  Goal dm_lep (DM (succp zerop) zerop zerop) (DM (succp zerop) zerop zerop) = truep. reflexivity. Qed.
  Goal dm_lep (DM zerop zerop (succp zerop)) (DM zerop zerop zerop) = falsep. reflexivity. Qed.
  Goal dm_lep (DM zerop zerop (succp zerop)) (DM zerop (succp zerop) zerop) = truep. reflexivity. Qed.
  Goal dm_lep (DM zerop zerop (succp zerop)) (DM (succp zerop) zerop zerop) = truep. reflexivity. Qed.

  Goal dm_ltp (DM zerop zerop zerop) (DM zerop zerop zerop) = falsep. reflexivity. Qed.
  Goal dm_ltp (DM zerop zerop zerop) (DM (succp zerop) zerop zerop) = truep. reflexivity. Qed.
  Goal dm_ltp (DM zerop zerop zerop) (DM zerop zerop (succp zerop)) = truep. reflexivity. Qed.
  Goal dm_ltp (DM (succp zerop) zerop zerop) (DM zerop zerop zerop) = falsep. reflexivity. Qed.
  Goal dm_ltp (DM (succp zerop) zerop zerop) (DM (succp zerop) zerop zerop) = falsep. reflexivity. Qed.
  Goal dm_ltp (DM zerop zerop (succp zerop)) (DM zerop zerop zerop) = falsep. reflexivity. Qed.
  Goal dm_ltp (DM zerop zerop (succp zerop)) (DM zerop (succp zerop) zerop) = truep. reflexivity. Qed.
  Goal dm_ltp (DM zerop zerop (succp zerop)) (DM (succp zerop) zerop zerop) = truep. reflexivity. Qed.

  Definition dm_eqp (dm0 dm1 : DetectMeasure) : boolp :=
    match (eqp (dm_mon dm0) (dm_mon dm1)),
      (eqp (dm_mque dm0) (dm_mque dm1)),
      (eqp (dm_vis dm0) (dm_vis dm1)) with
    | truep, truep, truep => truep
    | _, _, _ => falsep
    end.

  Fixpoint lengthp [A : Type] (l : list A) : natp :=
    match l with
    | [] => zerop
    | _ :: l => succp (lengthp l)
    end.

  Fixpoint measure_mq p MQ0 : natp * bool :=
    match MQ0 with
    | [] => (zerop, false)
    | (MqProbe _ p')::MQ0 =>
        if NAME.eqb (origin p) (origin p')
           && (lock_id p =? lock_id p')%nat
        then (succp zerop, true)
        else
          let (m, found) := measure_mq p MQ0
          in (succp m, found)
    | _::MQ0 =>
        let (m, found) := measure_mq p MQ0
        in (succp m, found)
    end.

  Fixpoint measure_mon p M0 : (natp * bool) :=
    match M0 with
    | MRecv _ => (zerop, false)
    | MSend _ p' M0 =>
        if NAME.eqb (origin p) (origin p')
           && (lock_id p =? lock_id p')%nat
        then (succp zerop, true)
        else
          let (m, found) := measure_mon p M0 in
          (succp m, found)
    end.

  Definition measure_ms p MS : ((natp * natp) * bool) := (* M MQ *)
    let (mm, found_m) := measure_mon p (mserv_m MS) in
    if found_m then ((mm, zerop), true)
    else
      let (mq, found_q) := measure_mq p (mserv_q MS) in
      ((mm, mq), found_q).

  Fixpoint measure_tlock (p : MProbe) n m (MN : MNet)
    (Hl : trans_lock MN n m) : (DetectMeasure * boolp).
    ltac1:(refine(
               match Hl as Hl' in trans_lock _ _ n0  return m = n0 -> (DetectMeasure * boolp) with
               | trans_lock_Direct _ _ _ => fun _ =>
                                             match measure_ms p (NetMod.get m MN) with
                                               ((mm, mq), found) =>
                                                 ({|dm_mon := mm; dm_mque := mq; dm_vis := succp zerop|},
                                                   if found then truep else falsep)
                                             end
               | @trans_lock_Indirect _ _ n' _ Hl1 Hl0 =>
                   fun e =>
                     let (dm, found) := measure_tlock p n' m MN _ in
                     ({|dm_mon := dm_mon dm; dm_mque := dm_mque dm; dm_vis := succp (dm_vis dm)|}, found)
               end eq_refl)).
    subst. assumption.
  Defined.

  Fixpoint measure_tlock_g (p : MProbe) n m (MN : MNet)
    (Hl : trans_lock MN n m) : (DetectMeasure * boolp).
    ltac1:(refine(
               match Hl as Hl' in trans_lock _ _ n0  return m = n0 -> (DetectMeasure * boolp) with
    | trans_lock_Direct _ _ _ => fun _ =>
        match measure_ms p (NetMod.get m MN) with
          ((mm, mq), found) =>
            ({|dm_mon := mm; dm_mque := mq; dm_vis := succp zerop|},
              if found then truep else falsep)
        end
    | @trans_lock_Indirect _ _ n' _ Hl1 Hl0 =>
        fun e =>
          match measure_ms p (NetMod.get m MN) with
          | ((mm, mq), true) =>
              ({|dm_mon := mm; dm_mque := mq; dm_vis := succp zerop|}, truep)
          | _ =>
              let (dm, found) := measure_tlock_g p n' m MN _ in
              ({|dm_mon := dm_mon dm; dm_mque := dm_mque dm; dm_vis := succp (dm_vis dm)|}, found)
          end end eq_refl)).
    subst. assumption.
  Defined.

  Fixpoint measure_lock_chain (p : MProbe) (MN : MNet) (L : list Name) (n : Name) : (DetectMeasure * bool) :=
    match L with
    | [] =>
        match measure_ms p (NetMod.get n MN) with
          ((mm, mq), found) =>
            ({|dm_mon := mm; dm_mque := mq; dm_vis := succp zerop|}, found)
        end
    | m::L =>
        match measure_ms p (NetMod.get m MN) with
        | ((mm, mq), true) =>
            ({|dm_mon := mm; dm_mque := mq; dm_vis := succp zerop|}, true)
        | _ =>
            let (dm, found) := measure_lock_chain p MN L n in
            ({|dm_mon := dm_mon dm; dm_mque := dm_mque dm; dm_vis := succp (dm_vis dm)|}, found)
        end
    end.

  (* Lemma tlock_dep_preserve [MN0 MN1 n0 n1 a] : *)
  (*   well_formed '' MN0 -> *)
  (*   (MN0 =(a)=> MN1) -> *)
  (*   trans_lock '' MN0 n0 n0 -> *)
  (*   trans_lock '' MN0 n0 n1 -> *)
  (*   trans_lock '' MN1 n0 n1. *)

  (* Proof. *)
  (*   intros. *)
  (*   apply dep_self_deadlocked in H1; auto. *)
  (*   destruct (MNAct_to_PNAct a) eqn:?. *)
  (*   2: { *)
  (*     eapply deinstr_act_skip in Heqo; eauto. *)
  (*     rewrite <- Heqo. *)
  (*     auto. *)
  (*   } *)
  (*   eapply deinstr_act_do in Heqo; eauto. *)
  (*   clear H0. *)
  (*   induction H2. *)
  (*   - constructor 1. *)
  (*     eauto using deadlocked_lock_on_invariant1. *)
  (*   - constructor 2 with (n1:=n1). *)
  (*     eauto using deadlocked_lock_on_invariant1. *)
  (*     eapply IHtrans_lock. *)
  (*     eauto using deadlocked_invariant, deadlocked_lock_on. *)
  (* Defined. *)

  (* Lemma tlock_loop_preserve [MN0 MN1 n a] : *)
  (*   KIC MN0 -> *)
  (*   (MN0 =(a)=> MN1) -> *)
  (*   trans_lock '' MN0 n n -> *)
  (*   trans_lock '' MN1 n n. *)

  (* Proof. *)
  (*   intros. *)
  (*   eauto using tlock_dep_preserve with LTS. *)
  (* Defined. *)

  Definition measure_loop (MN : MNet) (L : list Name) (n : Name) : (DetectMeasure * bool) :=
    match (alarm (MN n)) with
    | true => ({|dm_mon := zerop; dm_mque := zerop; dm_vis := zerop|}, true)
    | false => measure_lock_chain (active_probe_of MN n) MN (n::L) n
    end.


  Lemma measure_loop_end : forall MN L n,
    measure_loop MN L n = ({|dm_mon := zerop; dm_mque := zerop; dm_vis := zerop|}, true) ->
    alarm (MN n) = true.

  Proof.
    intros.
    destruct (alarm (MN n)) eqn:?; auto.
    exfalso.

    unfold measure_loop in *.
    rewrite Heqb in *.
    unfold measure_lock_chain in *.
    induction L.
    - unfold active_probe_of in *.
      destruct (NetMod.get n MN).
      unfold measure_ms in *.
      induction mserv_m0; auto.
      + unfold measure_mon in *.
        simpl in *.
        induction mserv_q0.
        * unfold measure_mq in *.
          simpl in *.
          bs.
        * induction mserv_q0; intros; simpl in *.
          -- destruct a; simpl in *; doubt.
             blast_cases; doubt.
             kill H.
          -- destruct b.


          assert (snd (({| dm_mon := zerop; dm_mque := zerop; dm_vis := succp (succp zerop) |}, falsep)) = snd ( ({| dm_mon := zerop; dm_mque := zerop; dm_vis := zerop |}, truep)
)) by (now rewrite H).
          simpl in *.
          ltac1:(dependent destruction H0).


  Lemma measure_non_incr : forall (MN0 MN1 : MNet) (n : Name) (L : list Name) (a : MNAct),
      (lock_chain '' MN0 n L n) -> (MN0 =(a)=> MN1) -> (KIC MN0) ->
      dm_lep
        (fst (measure_tlock_g (active_probe_of MN0 n) n n MN0 (measure)))
        (fst (measure_tlock_g (active_probe_of MN1 n) n n MN1 (tlock_loop_preserve HKIC HT Hl0))) = truep.
  Proof.
    intros.
    unfold trans in HT.
    ltac1:(dependent destruction HT).
    - ltac1:(dependent destruction n1).
      unfold trans in t.
      ltac1:(dependent destruction t); doubt.
      unfold active_probe_of, dm_lep in *.
      blast_cases; auto.


  (* Fixpoint measure_tlock p n m (MN : MNet) *)
  (*   (Hl : trans_lock MN n m) : (DetectMeasure * boolp) := *)
  (*   match Hl with *)
  (*   | trans_lock_Direct _ _ _ => *)
  (*        match measure_ms p (NetMod.get m MN) with *)
  (*          ((mm, mq), found) => *)
  (*            ({|dm_mon := mm; dm_mque := mq; dm_vis := succp zerop|}, *)
  (*              if found then truep else falsep) *)
  (*        end *)
  (*   | @trans_lock_Indirect _ _ n' _ Hl1 Hl0 => *)
  (*       _ *)
  (*       let (dm, found) := measure_tlock p n' m MN Hl0 in *)
  (*       ({|dm_mon := dm_mon dm; dm_mque := dm_mque dm; dm_vis := succp (dm_vis dm)|}, found) *)
  (*       (* match measure_ms p (NetMod.get n' MN) with *) *)
  (*       (*   ((mm, mq), found) => *) *)
  (*       (*     if found *) *)
  (*       (*     then ({|dm_mon := mm; dm_mque := mq; dm_vis := succp zerop|}, found) *) *)
  (*       (*     else measure_tlock p n' m Hl *) *)
  (*       (* end *) *)
  (*   end. *)

  (* Fixpoint measure_sends_probe [nc] [p MS] *)
  (*   (Hs : sends_probe nc p MS) : natp * natp. *)
  (*   ltac1:(refine(match Hs with *)
  (*   | sp_init MQ _ _ _ _ _ _ _  _ _ _ _ _ => _ *)
  (*   | sp_prop MQ _ _ _ _ _ _  _ _ _ _ _ => _ *)
  (*   | sp_send _ _ _ _ _ => _ *)
  (*   | sp_late _ _ _ _ _ _ _  _ Hs => _ *)
  (*   end)). *)
  (*   - apply (lengthp MQ, zerop). *)
  (*   - apply (lengthp MQ, zerop). *)
  (*   - apply (zerop, zerop). *)
  (*   - apply measure_sends_probe in Hs as [mq mm]. *)
  (*     apply (mq, succp mm). *)
  (* Defined. *)

  (* Fixpoint measure_tlock [n m : Name] [MN : MNet] *)
  (*   (Hl : trans_lock MN n m) : natp := *)
  (*   match Hl with *)
  (*   | trans_lock_Direct _ _ _ => succp zerop *)
  (*   | trans_lock_Indirect _ _ _ Hl => succp (measure_tlock Hl) *)
  (*   end. *)

  (* Definition measure_ac [n MN] (ac : alarm_condition n MN) : DetectMeasure := *)
  (*   match ac with *)
  (*   | ac_alarm _ _ _ => {|dm_mon:=zerop; dm_mque:=zerop; dm_vis:=zerop|} *)
  (*   | @ac_seek _ _ m m' HL_n_m H_n_m' Hsend => *)
  (*       let (mq, mm) := measure_send Hsend in *)
  (*       let mv := match HL_n_m with *)
  (*                 | or_introl _ => zerop *)
  (*                 | or_intror Hl => measure_tlock Hl *)
  (*                 end in *)
  (*       let mv := succp mv in *)
  (*       {|dm_mon:=mm; dm_mque:=mq; dm_vis:=mv|} *)
  (*   | @ac_fin _ _ n' HL_n_n' HIn => {|dm_mon:=zerop; dm_mque:=zerop; dm_vis:=zerop|} *)
  (*   end. *)


  (* Lemma measure_send_non_incr : forall (MN0 MN1 : MNet) nc p (n0 : Name) (a : MNAct) *)
  (*                                 (Hs : sends_probe nc p (NetMod.get MN0 n0)), *)
  (*     KIC MN0 -> *)
  (*     trans_lock '' MN0 n0 n0 -> *)
  (*     (MN0 =(a)=> MN1) -> *)
  (*     exists (ac1 : alarm_condition n0 MN1), *)
  (*       dm_lep (measure_sends ac1) (measure_sends ac0) = truep. *)

  Lemma measure_non_incr : forall (MN0 MN1 : MNet) (n : Name) (a : MNAct)
      (ac0 : alarm_condition n MN0),
      KIC MN0 ->
      trans_lock '' MN0 n n ->
      (MN0 =(a)=> MN1) ->
      exists (ac1 : alarm_condition n MN1),
        dm_lep (measure_ac ac1) (measure_ac ac0) = truep.

  Proof.
    intros.
    assert (deadlocked n '' MN0) by eauto using dep_self_deadlocked with LTS.

    ltac1:(dependent destruction ac0).
    - consider (KIC MN0).
      assert (alarm (MN1 n) = true) as HA by eauto using net_preserve_alarm.
      eexists (ac_alarm n MN1 HA).
      unfold dm_lep; blast_cases; attac.
    - destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.
      ltac1:(dependent destruction s).
      + admit.
      + admit.
      +
      +

    + assert (sends_probe (m0, R) (active_probe_of MN0 m) (NetMod.get m' MN1) \/ ~ sends_probe (m0, R) (active_probe_of MN0 m) (NetMod.get m' MN1))
        as [|] by eauto using sends_probe_dec.
      * assert (active_probe_of MN0 m = active_probe_of MN1 m) by eauto 3 using deadlocked_preserve_active_probe_of1 with LTS.
        rewrite `(active_probe_of _ _ = _) in *.

        assert (deadlocked m '' MN0) by eauto 3 with LTS.
        assert (deadlocked m0 '' MN0) by (consider (m = m0 \/ _); eauto 3 with LTS).
        consider (m = m0 \/ trans_lock MN0 m m0) by attac > [left|right]; auto.
        -- eexists (ac_seek m0 MN1 _ _ _).
           eauto 3 using deadlocked_M_dep_invariant1 with LTS.
        -- consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound1; eauto 2 with LTS.
      * exists m.
        split; auto.

        consider (a = NComm m' m0 R ^ (active_probe_of MN0 m)) by eauto using sends_probe_sent with LTS.
        smash_eq m0 m.
        -- constructor 3 with (n':=m'); eauto.
           1: consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS; eauto 4 with LTS.

           clear - H0.
           kill H0. hsimpl in *.
           unfold active_ev_of, active_probe_of in *.
           ltac1:(autounfold with LTS_get in * ).
           hsimpl in |- *.
           smash_eq m0 m'; compat_hsimpl in *.
           rewrite H; attac.
           attac.
        -- destruct `(m = m0 \/ trans_lock MN0 m m0).
           1: bs.

           assert (deadlocked m0 '' MN0) by eauto 3 with LTS.
           assert (deadlocked m '' MN0) by eauto 3 with LTS.
           assert (exists m'', trans_lock MN0 m m'' /\ lock MN0 m'' m0).
           {
             apply dep_lock_chain in H9. hsimpl in H9.
             ltac1:(rev_induction L); intros; hsimpl in *.
             - exists m.
               split; auto.
               eapply dep_reloop; re_have (eauto with LTS).
             - exists a; split; eauto.
               eauto using lock_chain_dep.
           } (* TODO TO LEMMA *)

           assert (~ active MN0 (active_probe_of MN0 m) m0) by (intros Hx; kill Hx).

           hsimpl in *.
           assert (sends_probe (m'', R) (active_probe_of MN0 m) (NetMod.get m0 MN1)) by eauto using probe_pass_on.

           assert (trans_lock MN1 m m'') by eauto 4 using deadlocked_M_dep_invariant1 with LTS.

           assert (lock MN1 m'' m0) by
             (consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound1;
              eauto 4 using deadlocked_lock_on_invariant with LTS
             ).
           assert (trans_lock MN1 m m0) by eauto 4 using deadlocked_M_dep_invariant1 with LTS.

           econstructor 2.
           3: replace (active_probe_of MN1 m) with (active_probe_of MN0 m) by eauto 3 using deadlocked_preserve_active_probe_of1 with LTS.
           3: eauto 4 with LTS.
           all: auto.
    + exists m.
      split; auto.

      assert (locked (MN0 m) = Some n') by eauto with LTS.
      assert (deadlocked m '' MN0) by eauto 3 with LTS.
      assert (lock MN1 m n')
        by (consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS; eauto 4 with LTS).
      assert (well_formed '' MN1)
        by (consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS; eauto 4 with LTS).

      assert (active_ev_of MN1 n' m = active_ev_of MN0 n' m).
      {
        unfold active_ev_of.
        consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using transp_sound with LTS.
        replace (active_probe_of MN1 m) with (active_probe_of MN0 m) by eauto using deadlocked_preserve_active_probe_of1, eq_sym with LTS.
        auto.
      }

      kill H0.
      * smash_eq m n.
        2: econstructor 3; eauto; unfold NetGet in *; replace (NetMod.get m MN1) with (NetMod.get m MN0) by eauto using NV_stay, eq_sym; rewrite `(active_ev_of _ _ _ = _); eauto.

        apply in_split in H10. hsimpl in H10.

        unfold active_ev_of, active_probe_of in *.
        ltac1:(autounfold with LTS_get in * ).

        destruct_ma &a0; doubt; compat_hsimpl in *.
        -- exfalso.
           absurd (no_sends_in m (NetMod.put m
                                    (mserv
                                       ((l1 ++
                                           MqProbe (n', R) {| origin := m; lock_id := lock_count (next_state M) |}
                                           :: l2) ++ [MqSend (n, &t) v]) M (serv I0 P2 O1)) MN0)).
           2: { eapply lock_M_no_sends_in; eattac. }

           intros Hx. clear - Hx.
           unfold no_sends_in, NoMqSend in *.
           blast_cases.
           hsimpl in *.
           apply Forall_app in Hx.
           apply Forall_app in Hx.
           attac.

        -- simpl in *.
           assert (self s = m).
           {
             clear - H Heqm0 H16.
             consider (KIC MN0).
             specialize (H_self_C m).
             ltac1:(autounfold with LTS_get in * ).
             rewrite `(NetMod.get m MN0 = _) in *.
             eattac.
           }
           destruct l1.
           1: { attac. }

           destruct s; attac.
           econstructor 3; eauto.
           unfold active_ev_of, active_probe_of.
           ltac1:(autounfold with LTS_get in * ).
           ltac1:(autorewrite with LTS in * ).
           simpl.
           blast_cases; attac.

        -- exfalso.
           attac.
           destruct P0 as [I0 P0 O0].
           apply lock_singleton in H9; eauto with LTS.
           apply lock_singleton in H12; eauto with LTS.
           unfold lock_set, deinstr in *.
           attac.
           destruct P1 as [I1 P1 O1].
           kill H12.
           kill H9.
           hsimpl in *.
           unfold serv_deinstr in *.
           attac.
           kill H18; attac.
           kill H9.
           apply `(~ In ((n', R), v) (I0 ++ retract_recv l1 ++ retract_recv l2)).
           destruct n as [? [|]]; attac.
           consider (_ /\ handle (n, Q) = None) by eauto. bs.
           consider (_ /\ handle (n, Q) = None) by eauto.
           consider (n' = n) by attac.
           attac.
        -- bs.
        -- simpl in *.
           assert (self s = m).
           {
             clear - H Heqm0 H16.
             consider (KIC MN0).
             specialize (H_self_C m).
             ltac1:(autounfold with LTS_get in * ).
             unfold NetGet in *. simpl in *.
             rewrite `(NetMod.get m MN0 = _) in *.
             eattac.
           }
           destruct l1.
           ++ econstructor 1.
              ltac1:(autorewrite with LTS in * ).
              hsimpl in *.
              unfold NetGet in *.
              hsimpl in |- *. rewrite PeanoNat.Nat.eqb_refl in *. attac.
           ++ kill H10.
              simpl in *.
              econstructor 3; eauto.
              unfold active_ev_of, active_probe_of.
              ltac1:(autounfold with LTS_get in * ).
              ltac1:(autorewrite with LTS in * ).
              rewrite `(NetMod.get self0 MN0 = _) in *.
              blast_cases; compat_hsimpl in *; attac.
      * constructor 3 with (n':=n').
        1: auto.
        rewrite `(active_ev_of _ _ _ = active_ev_of _ _ _).
        clear - H10 H15 H16.
        hsimpl in *. hsimpl in *.
        unfold active_ev_of, active_probe_of in *.
        ltac1:(autounfold with LTS_get in * ).
        all: smash_eq m n n'0; destruct v; hsimpl in *; hsimpl in |- *;
          try (rewrite `(NetMod.get m _ = _) in * );
          try (rewrite `(NetMod.get n _ = _) in * );
          try (rewrite `(NetMod.get n'0 _ = _) in * ); hsimpl in *; doubt.
        all: compat_hsimpl in *; eattac.

    - assert (deadlocked n0 '' MN1) by re_have (eauto using dep_self_deadlocked).
      consider (exists m0 m1 v, (n0 = m0 \/ trans_lock MN1 n0 m0) /\ a = NComm m0 m1 Q (MValP v)).
      {
        consider (exists (m0 m1 : Name) (v : Val),
                     a = NComm m0 m1 Q # v /\
                       (m0 = n0 \/ m0 <> n0 /\ trans_lock MN0 n0 m0 /\ trans_lock MN1 n0 m0) /\
                       (m1 = n0 \/ m1 <> n0 /\ trans_lock MN0 m1 n0 /\ trans_lock MN1 m1 n0))
          by re_have (eauto 2 using net_M_dep_close).
        do 2 (destruct `(_ \/ _)); eattac.
      }

      assert (lock MN1 m0 m1)
        by (consider (~ lock MN0 m0 m1 /\ lock MN1 m0 m1);
            eauto using SRPC_M_net_query_new_lock with LTS).

      exists m1.
      split.
      1: { consider (_ \/ _); eauto with LTS. }

      assert (trans_lock MN1 n0 m0) by
        (destruct `(n0 = m0 \/ trans_lock MN1 n0 m0); subst; eauto 4 using dep_reloop, dep_loop, trans_lock_seq1 with LTS).
      assert (forall n : Name, AnySRPC_serv (NetMod.get n '' MN1)) by re_have (eauto with LTS).
      assert (sends_probe (m0, R) (active_probe_of MN1 m1) (NetMod.get m1 MN1)).
      {
        assert (deadlocked m1 '' MN1) by eauto 4 using dep_self_deadlocked with LTS.
        destruct (NetMod.get m1 MN1) as [MQ1 s1 S1] eqn:?.
        consider (exists m2, lock MN1 m1 m2) by re_have (eauto 3 using deadlocked_M_get_lock with LTS).

        assert (NoRecvR_MQ (mserv_q (MN1 m1))) by re_have (eauto using deadlocked_M_NoRecvR with LTS).
        assert (NoSends_MQ (mserv_q (MN1 m1))).
        {
          assert (no_sends_in m1 MN1) by eauto using lock_M_no_sends_in.
          ltac1:(autounfold with LTS_get).
          unfold no_sends_in, NoMqSend in *.
          destruct (NetMod.get m1 MN1).
          auto.
        }
        assert (locked (next_state s1) = Some m2).
        {
          assert (locked (MN1 m1) = Some m2) by eauto using KIC_invariant_H_locked with LTS.
          ltac1:(autounfold with LTS_get in * ).
          rewrite `(NetMod.get m1 MN1 = _) in *.
          auto.
        }
        assert (m1 = self (next_state s1)); subst.
        {
          consider (m1 = self (MN0 m1)) by consider (KIC MN0).
          replace (self (MN0 m1)) with (self (MN1 m1)) by (consider (KIC MN0); eauto using net_preserve_self, eq_sym with LTS); auto.
          ltac1:(autounfold with LTS_get in * ).
          rewrite `(NetMod.get m1 MN1 = _).
          auto.
        }

        consider (exists MQ1', MQ1 = MQ1' ++ [MqRecv (m0, Q) v]) by (consider (_ =(_)=> _); compat_hsimpl in *; eattac).
        clear - H11 H12 H13 H14 Heqm. (* lock, 2x No____MQ, locked _ = Some _ *)

        unfold active_probe_of in *.
        ltac1:(autounfold with LTS_get in * ).
        rewrite `(NetMod.get (self (next_state s1)) MN1 = _) in *.
        clear Heqm.

        induction s1; simpl in *.
        1: eattac.

        destruct
          (NameTag_eq_dec to (m0, R)),
          (MProbe_eq_dec msg {| origin := self (next_state s1); lock_id := lock_count (next_state s1) |}); subst;
          eauto with LTS.
      }

      econstructor 2. 3: eauto. all: eauto.
      right.
      destruct `(n0 = m0 \/ trans_lock MN1 n0 m0); subst; eauto 4 using dep_reloop, dep_loop, trans_lock_seq1 with LTS.
  Qed.
