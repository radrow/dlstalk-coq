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

  Definition dm_leb (dm0 dm1 : DetectMeasure) : bool :=
    let c0 := dm_flush in
    let c1 := dm_pass in
    let next c f :=
      match (c dm0 =? c dm1) with
      | true => f
      | _ => (c dm0 <=? c dm1)
      end
    in next c1 (next c0 true).

  Definition dm_ltb (dm0 dm1 : DetectMeasure) : bool :=
    let c0 := dm_flush in
    let c1 := dm_pass in
    let next c f :=
      match (c dm0 =? c dm1) with
      | true => f
      | _ => (c dm0 <? c dm1)
      end
    in next c1 (next c0 false).

  Definition dm_eqb (dm0 dm1 : DetectMeasure) : bool :=
    (dm_flush dm0 =? dm_flush dm1)%nat && (dm_pass dm0 =? dm_pass dm1)%nat.

  Lemma dm_eqb_eq : forall dm0 dm1, dm_eqb dm0 dm1 = true <-> dm0 = dm1.
  Proof.
    destruct dm0, dm1.
    unfold dm_eqb, andb.
    split; intros; simpl in *.
    - blast_cases; attac.
      rewrite PeanoNat.Nat.eqb_eq in *; attac.
    - attac.
      repeat (rewrite PeanoNat.Nat.eqb_refl in * ); attac.
  Qed.

  Lemma dm_eqb_neq : forall dm0 dm1, dm_eqb dm0 dm1 = false <-> dm0 <> dm1.
  Proof.
    destruct dm0, dm1.
    unfold dm_eqb, andb.
    split; intros; simpl in *.
    - blast_cases; attac.
      all: rewrite PeanoNat.Nat.eqb_neq in *; attac.
    - blast_cases; attac.
      rewrite PeanoNat.Nat.eqb_neq in *; attac.
      intros ?.
      apply `(~ _).
      attac.
      rewrite PeanoNat.Nat.eqb_eq in *; attac.
  Qed.

  Hint Rewrite -> dm_eqb_eq dm_eqb_neq using assumption : LTS LTS_concl.


  Definition dm_zero : DetectMeasure :=
    {|dm_pass:=0; dm_flush:=0|}.

  Definition dm_decr (next : nat) (dm : DetectMeasure) : DetectMeasure :=
    match dm with
    | {|dm_pass:=dmp; dm_flush:=S dmf|} =>
        {|dm_pass:=dmp; dm_flush:=dmf|}
    | {|dm_pass:=S dmp; dm_flush:=0|} =>
        {|dm_pass:=dmp; dm_flush:=next|}
    | _ => {|dm_pass:=0; dm_flush:=0|}
    end.


  Lemma nat_neqb_n_Sn : forall n, n =? S n = false.
    intros. rewrite PeanoNat.Nat.eqb_neq. attac.
  Qed.

  Lemma nat_ltb_n_Sn : forall n, n <? S n = true.
    intros. rewrite PeanoNat.Nat.ltb_lt. attac.
  Qed.

  Lemma nat_leb_n_Sn : forall n, n <=? S n = true.
    intros. rewrite PeanoNat.Nat.leb_le. attac.
  Qed.

  Hint Rewrite -> nat_neqb_n_Sn nat_ltb_n_Sn nat_leb_n_Sn
                   PeanoNat.Nat.eqb_refl
                   using assumption
    : LTS LTS_concl.


  Lemma dm_decr_lt : forall n dm, dm <> dm_zero -> dm_ltb (dm_decr n dm) dm = true.
  Proof.
    unfold dm_ltb, dm_zero.
    destruct dm; attac.
    destruct dm_flush0, dm_pass0; attac.
  Qed.

  Lemma dm_decr_le : forall n dm, dm_leb (dm_decr n dm) dm = true.
  Proof.
    unfold dm_leb, dm_zero.
    destruct dm; attac.
    destruct dm_flush0, dm_pass0; attac.
  Qed.

  Hint Rewrite -> dm_decr_lt dm_decr_le using (unfold dm_zero in *; spank) : LTS LTS_concl.

  Lemma dm_decr_zero : forall n, dm_decr n dm_zero = dm_zero.
  Proof.
    eauto with LTS.
  Qed.

  Hint Rewrite -> dm_decr_zero using assumption : LTS LTS_concl.

  Lemma dm_nonzero_pass : forall n dm, dm_pass dm = S n -> dm <> dm_zero.
  Proof.
    unfold dm_zero; destruct dm; attac.
  Qed.

  Lemma dm_nonzero_flush : forall n dm, dm_flush dm = S n -> dm <> dm_zero.
  Proof.
    unfold dm_zero; destruct dm; attac.
  Qed.

  Hint Resolve dm_nonzero_flush dm_nonzero_pass : LTS.


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

  Lemma next_state_measure_fin : forall M mm c,
      measure_mon_fin M = (mm, c) ->
      next_state M = c.

  Proof. induction M; attac. blast_cases; attac. Qed.

  Hint Rewrite -> next_state_measure_fin using spank : LTS LTS_concl.

  Lemma measure_mon_fin_Send_all : forall (M : MProc) tag p ws n s,
      measure_mon_fin (MSend_all ws tag p M) = (n, s) <->
        exists n', measure_mon_fin M = (n', s)
              /\ n = length ws + n'
              /\ s = next_state M.

  Proof.
    split; intros; attac.
    - generalize dependent n.
      induction ws; attac.
      destruct ( measure_mon_fin (MSend_all ws tag p M) ) eqn:?.
      hsimpl in *.
      specialize (IHws _ eq_refl).
      attac.
    - generalize dependent n'.
      induction ws; attac.
      specialize (IHws _ ltac:(eauto)).
      attac.
  Qed.

  Hint Rewrite -> measure_mon_fin_Send_all using spank : LTS LTS_concl.

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
      eapply IHMQ in Heqo.
      bs.
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

  Hint Resolve measure_mq_fin_push : LTS.


  Lemma measure_mq_fin_Send : forall (M : MProc) MQ nc p dm,
      alarm M = false ->
      measure_mq_fin (MSend nc p M) MQ = Some dm <->
        exists dm', measure_mq_fin M MQ = Some dm' /\ dm = S dm'.
  Proof.
    split; intros; attac.
    - blast_cases; attac.
      unfold option_map in *; attac.
      blast_cases; attac.
    - blast_cases; attac.
      unfold option_map in *; attac.
      blast_cases; attac.
  Qed.

  Lemma measure_mq_fin_Send_finito : forall (M : MProc) MQ nc p,
      alarm M = true ->
      measure_mq_fin (MSend nc p M) MQ = Some 0.
  Proof.
    attac.
  Qed.

  Hint Rewrite -> measure_mq_fin_Send measure_mq_fin_Send_finito using assumption : LTS LTS_concl.


  Lemma measure_mq_fin_Send_all : forall (M : MProc) MQ t p ws dm,
      alarm M = false ->
      measure_mq_fin (MSend_all ws t p M) MQ = Some dm <->
      exists dm', measure_mq_fin M MQ = Some dm' /\ dm = add (length ws) dm'.
  Proof.
    assert (forall (M : MProc) MQ t p ws dm,
               alarm M = false ->
               measure_mq_fin (MSend_all ws &t p M) MQ = Some dm ->
               exists dm', measure_mq_fin M MQ = Some dm' /\ dm = add (length ws) dm').
    - intros.
      generalize dependent dm.
      induction ws; attac.
      destruct (alarm (MSend (a, &t) p (MSend_all ws &t p M))) eqn:?; hsimpl in H; attac.
      unfold option_map in *.
      destruct MQ; attac.
      unfold option_map in *.
      destruct (measure_mon_fin (MSend_all ws &t p M)) eqn:?.
      consider (m0 = m).
      {
        transitivity '(next_state (MSend_all ws &t p M)).
        - attac.
        - rewrite next_state_Send_all.
          attac.
      }

      blast_cases; attac.
      specialize (IHws _ eq_refl).
      attac.
    - split; eauto.
      generalize dependent dm.
      induction M; attac; blast_cases; attac.
      + unfold option_map in *.
        blast_cases; attac.
        f_equal.
        lia.
      + attac.
        unfold option_map in *.
        destruct (measure_mq_fin (mon_handle e m0) l) eqn:?; attac.
        destruct ( measure_mon_fin (MSend_all ws &t p M) ) eqn:?; attac.
        rewrite `(measure_mq_fin _ _ = _) in *.
        repeat (rewrite PeanoNat.Nat.add_succ_r in * ).
        do 2 f_equal.
        eassert (Some (S (length ws + n' + n0)) = Some _)
          by (eapply IHM; eattac).
        attac.
  Qed.

  Lemma measure_mq_fin_Send_all_finito : forall (M : MProc) MQ t p ws,
      alarm M = true ->
      measure_mq_fin (MSend_all ws t p M) MQ = Some 0.

  Proof.
    induction ws; attac.
    rewrite measure_mq_fin_Send_finito; eauto. (* wtf this not work *)
    attac.
  Qed.

  Hint Rewrite -> measure_mq_fin_Send_all measure_mq_fin_Send_all_finito using spank : LTS LTS_concl.

  Hint Rewrite -> next_state_Send_all using assumption : LTS LTS_concl.


  Definition measure_ms_fin (MS : MServ) : option nat :=
    measure_mq_fin (mserv_m MS) (mserv_q MS).


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
    all: try (rewrite next_state_Send_all in *; attac).
    all: try (rewrite measure_mon_fin_Send_all in *; attac).
  Qed.


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

  Hint Rewrite -> next_state_measure_fin using spank : LTS LTS_concl.

  Lemma measure_mon_Send_all_Q : forall (M : MProc) p ws n dmm b,
      measure_mon n p (MSend_all ws Q p M) = (dmm, b) <->
        exists dmm', measure_mon n p M = (dmm', b) /\ dmm = length ws + dmm'.
  Proof.
    split; intros; attac.
    - generalize dependent dmm.
      induction ws; attac.
      blast_cases; attac.
      specialize (IHws _ eq_refl).
      attac.
    - generalize dependent dmm'.
      induction ws; attac.
      apply IHws in H.
      attac.
  Qed.

  Lemma measure_mon_Send_all_in_found : forall (M : MProc) p ws n dmm b,
      In n ws ->
      measure_mon n p (MSend_all ws R p M) = (dmm, b) -> b = true.
  Proof.
    intros.
    generalize dependent dmm.
    induction ws; attac.
    unfold andb in *.
    blast_cases; attac.
  Qed.

  Lemma measure_mon_Send_all_not_in_found : forall (s : MState) p ws n dmm b,
      ~ In n ws ->
      measure_mon n p (MSend_all ws R p (MRecv s)) = (dmm, b) -> b = false.
  Proof.
    intros.
    generalize dependent dmm.
    induction ws; attac.
    unfold andb in *.
    blast_cases; attac.
  Qed.

  Lemma measure_mon_Send_all_not_in_len : forall (s : MState) p ws n dmm b,
      ~ In n ws ->
      measure_mon n p (MSend_all ws R p (MRecv s)) = (dmm, b) -> dmm = length ws.
  Proof.
    intros.
    generalize dependent dmm.
    induction ws; attac.
    unfold andb in *.
    blast_cases; attac.
  Qed.

  Hint Rewrite -> measure_mon_Send_all_Q measure_mon_Send_all_in_found
                   measure_mon_Send_all_not_in_found measure_mon_Send_all_not_in_len using assumption : LTS LTS_concl.


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


  Lemma measure_mq_Send_bad_p : forall (M : MProc) MQ n0 n1 p0 p1 tag dm,
      p0 <> p1 ->
      measure_mq n0 p0 (MSend (n1, tag) p1 M) MQ = Some dm <->
        exists dm', measure_mq n0 p0 M MQ = Some dm' /\ dm = S dm'.
  Proof.
    split; intros; attac.
    - blast_cases; attac.
      destruct (measure_mon n0 p0 (MSend (n1, tag) p1 M)) eqn:?.
      hsimpl in H0.
      blast_cases; attac.
      unfold andb in *.
      blast_cases; attac.
      unfold andb in *.
      blast_cases; attac.
    - destruct (measure_mon n0 p0 M) eqn:?.
      hsimpl in *.
      destruct (measure_mon n0 p0 (MSend (n1, tag) p1 M)) eqn:?.
      hsimpl.
      hsimpl in *.
      unfold andb in *.
      blast_cases; attac.
  Qed.

  Lemma measure_mq_Send_bad_t : forall (M : MProc) MQ n0 n1 p0 p1 dm,
      measure_mq n0 p0 (MSend (n1, Q) p1 M) MQ = Some dm <->
        exists dm', measure_mq n0 p0 M MQ = Some dm' /\ dm = S dm'.
  Proof.
    split; intros; attac.
    - blast_cases; attac.
      destruct (measure_mon n0 p0 (MSend (n1, Q) p1 M)) eqn:?.
      hsimpl in H.
      blast_cases; attac.
      unfold andb in *.
      blast_cases; attac.
      unfold andb in *.
      blast_cases; attac.
    - destruct (measure_mon n0 p0 M) eqn:?.
      hsimpl in *.
      destruct (measure_mon n0 p0 (MSend (n1, Q) p1 M)) eqn:?.
      hsimpl.
      hsimpl in *.
      unfold andb in *.
      blast_cases; attac.
  Qed.

  Lemma measure_mq_Send_bad_n : forall (M : MProc) MQ n0 n1 tag p0 p1 dm,
      n0 <> n1 ->
      measure_mq n0 p0 (MSend (n1, tag) p1 M) MQ = Some dm <->
        exists dm', measure_mq n0 p0 M MQ = Some dm' /\ dm = S dm'.
  Proof.
    split; intros; attac.
    - blast_cases; attac.
      destruct (measure_mon n0 p0 (MSend (n1, tag) p1 M)) eqn:?.
      hsimpl in H0.
      blast_cases; attac.
      unfold andb in *.
      blast_cases; attac.
      unfold andb in *.
      blast_cases; attac.
    - destruct (measure_mon n0 p0 M) eqn:?.
      hsimpl in *.
      destruct (measure_mon n0 p0 (MSend (n1, tag) p1 M)) eqn:?.
      hsimpl.
      hsimpl in *.
      unfold andb in *.
      blast_cases; attac.
  Qed.

  Lemma measure_mq_Send_finito : forall (M : MProc) MQ n p,
      measure_mq n p (MSend (n, R) p M) MQ = Some 1.
  Proof.
    attac.
    destruct (measure_mon n p (MSend (n, R) p M)) eqn:?.
    hsimpl. attac.
  Qed.

  Hint Rewrite -> measure_mq_Send_finito measure_mq_Send_bad_n measure_mq_Send_bad_t measure_mq_Send_bad_p using assumption : LTS LTS_concl.


  Lemma measure_mq_Send_all_bad_p : forall (M : MProc) MQ n0 ws p0 p1 tag dm,
      p0 <> p1 ->
      measure_mq n0 p0 (MSend_all ws tag p1 M) MQ = Some dm <->
        exists dm', measure_mq n0 p0 M MQ = Some dm' /\ dm = length ws + dm'.
  Proof.
    split; intros; attac.
    - generalize dependent dm.
      induction ws; attac.
      apply IHws in H0.
      attac.
    - induction ws; attac.
  Qed.

  Lemma measure_mq_Send_all_bad_t : forall (M : MProc) MQ n0 ws p0 p1 dm,
      measure_mq n0 p0 (MSend_all ws Q p1 M) MQ = Some dm <->
        exists dm', measure_mq n0 p0 M MQ = Some dm' /\ dm = length ws + dm'.
  Proof.
    split; intros; attac.
    - generalize dependent dm.
      induction ws; attac.
      rewrite measure_mq_Send_bad_t in *.
      attac.
      apply IHws in H.
      attac.
    - induction ws; attac.
      rewrite measure_mq_Send_bad_t in *.
      attac.
  Qed.

  Lemma measure_mq_Send_all_bad_n : forall (M : MProc) MQ n0 ws p0 p1 tag dm,
      ~ In n0 ws ->
      measure_mq n0 p0 (MSend_all ws tag p1 M) MQ = Some dm <->
        exists dm', measure_mq n0 p0 M MQ = Some dm' /\ dm = length ws + dm'.
  Proof.
    split; intros; attac.
    - generalize dependent dm.
      induction ws; attac.
      rewrite measure_mq_Send_bad_n in *; eauto.
      attac.
      apply IHws in H0; eauto.
      attac.
    - induction ws; attac.
      rewrite measure_mq_Send_bad_n in *; eauto.
  Qed.

  Lemma measure_mq_Send_all_finito : forall (M : MProc) MQ n ws p,
      In n ws ->
      exists dm, measure_mq n p (MSend_all ws R p M) MQ = Some dm /\ dm <= length ws.
  Proof.
    attac.
    induction ws; attac.
    smash_eq a n; attac.
    - rewrite measure_mq_Send_finito.
      exists 1; attac.
    - specialize (IHws ltac:(auto)).
      attac.
      rewrite IHws.
      eexists _; attac.
  Qed.

  Hint Rewrite -> measure_mq_Send_all_bad_n measure_mq_Send_all_bad_t measure_mq_Send_all_bad_p using assumption : LTS LTS_concl.


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

  Hint Resolve measure_mq_push : LTS.


  Definition measure_ms (n_to : Name) p (MS : MServ) : option nat :=
    measure_mq n_to p (mserv_m MS) (mserv_q MS).


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


  Lemma measure_ms_net_decr : forall n0 n1 (MN0 MN1 : MNet) a dm p,
      Flushing_NAct n1 a ->
      (MN0 =(a)=> MN1) ->
      measure_ms n0 p (MN0 n1) = Some (S (S dm)) ->
      measure_ms n0 p (MN1 n1) = Some (S dm).

  Proof.
    intros.
    destruct (MN0 n1) as [MQ0 M0 S0] eqn:?.
    destruct (MN1 n1) as [MQ1 M1 S1] eqn:?.
    destruct a; attac; consider (_ =(_)=> _); unfold NetGet in *; compat_hsimpl in *.
    - eapply measure_ms_decr; attac.
    - smash_eq n1 n2.
      + hsimpl in *.
        rewrite `(NetMod.get n1 MN0 = _) in *.
        eapply measure_ms_decr with (MS1:=S2) in H; eauto.
        2: destruct p0; attac.
        clear - H2 H.
        destruct p0; compat_hsimpl in *; attac.
      + hsimpl in *.
        rewrite `(NetMod.get n1 MN0 = _) in *.
        eapply measure_ms_decr in H; eauto.
        destruct p0; attac.
  Qed.

  Lemma measure_ms_net_send : forall n0 n1 (MN0 MN1 : MNet) a p,
      Flushing_NAct n0 a ->
      (MN0 =(a)=> MN1) ->
      measure_ms n1 p (MN0 n0) = Some 1 ->
      a = (NComm n0 n1 R ^ p).

  Proof.
    intros.
    destruct (MN0 n0) as [MQ0 M0 S0] eqn:?.
    destruct (MN1 n0) as [MQ1 M1 S1] eqn:?.
    destruct a; attac; consider (_ =(_)=> _); unfold NetGet in *; compat_hsimpl in *.
    - rewrite `(NetMod.get n0 MN0 = _) in *.
      eapply measure_ms_send in H1; eattac.
    - smash_eq n0 n2.
      + hsimpl in *.
        rewrite `(NetMod.get n0 MN0 = _) in *.
        eapply measure_ms_send with (p:=p)(n:=n1) in H ; eauto.
        all: destruct p0; attac.
      + hsimpl in *.
        rewrite `(NetMod.get n0 MN0 = _) in *.
        eapply measure_ms_send with (p:=p)(n:=n1) in H ; eauto.
        all: destruct p0; attac.
  Qed.

  Lemma measure_ms_net_noincr : forall n0 n1 (MN0 MN1 : MNet) a dm0 p,
      (MN0 =(a)=> MN1) ->
      measure_ms n1 p (MN0 n0) = Some dm0 ->
      (exists dm1, measure_ms n1 p (MN1 n0) = Some dm1 /\ dm1 <= dm0) \/
        a = (NComm n0 n1 R ^ p).

  Proof.
    intros.
    destruct (MN0 n0) as [MQ0 M0 S0] eqn:?.
    destruct (MN1 n0) as [MQ1 M1 S1] eqn:?.
    destruct a; consider (_ =(_)=> _).
    - unfold NetGet in *.
      smash_eq n0 n; attac.
      rewrite `(NetMod.get n0 _ = _) in *.
      eapply measure_ms_noincr in H; eauto.
      destruct `(_ \/ _); attac.
    - attac; unfold NetGet in *; compat_hsimpl in *.
      smash_eq n0 n; attac.
      + rewrite `(NetMod.get n0 MN0 = _) in *.
        eapply measure_ms_noincr with (p:=p)(n:=n1) in H1 ; eauto.
        destruct `(_ \/ _); attac.
        all: destruct p0; attac.
        * left.
          exists dm1.
          smash_eq n0 n2; attac.
        * smash_eq n0 n2; attac.
          compat_hsimpl in *.
          attac.
      + exists dm0.
        attac.
        smash_eq n0 n2; attac.
        rewrite `(NetMod.get n0 MN0 = _) in *; attac.
        destruct p0; compat_hsimpl in *; attac.
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

  Lemma measure_ms_fin_recv : forall (MS0 MS1 : MServ) n,
      serv_lock [n] MS0 ->
      locked MS0 = Some n ->
      (MS0 =(recv (n, R) ^ {|origin:=self MS0; lock_id:=lock_count MS1|})=> MS1) ->
      exists dm, measure_ms_fin MS1 = Some dm.
  Proof.
    intros.
    assert (NoRecvR_from n (mserv_q MS0)).
    {
      unfold NoRecvR_from; intros v ?.
      destruct MS0; attac.
      consider (serv_lock _ _).
      assert (~ In (n, R, v) &I) by attac.
      destruct P; attac.
    }
    assert (NoSends_MQ (mserv_q MS0)).
    {
      destruct MS0; attac.
      consider (serv_lock _ _).
      destruct P; attac.
      eapply app_eq_nil in H6.
      attac.
      eapply Forall_forall.
      attac.
      apply in_split in H; attac.
      blast_cases; attac.
    }
    destruct MS0 as [MQ0 M0 S0].
    destruct MS1 as [MQ1 M1 S1].
    simpl in *.
    hsimpl in *.
    unfold measure_ms_fin.
    generalize dependent M.
    clear H.

    induction MQ; attac.
    - generalize dependent n0.
      induction M; attac.
      1: { destruct alarm; attac. }
      destruct (measure_mon_fin M) eqn:?.
      attac.
      destruct &alarm; attac.
    - hsimpl in *.
      specialize IHMQ with (M:=mon_handle a m).

      assert (lock_count m = lock_count (mon_handle a m)).
      {
        destruct m; simpl in *.
        attac.
        destruct a; attac; blast_cases; attac.
        all: try (rewrite next_state_Send_all in * ).
        all: attac.
      }
      assert (locked m = locked (mon_handle a m)).
      {
        destruct m; simpl in *.
        attac.
        destruct a; attac; blast_cases; attac.
        all: try (rewrite next_state_Send_all in * ).
        all: attac.
      }
      assert (self m = self (mon_handle a m)).
      {
        destruct m; simpl in *.
        attac.
        destruct a; attac; blast_cases; attac.
        all: try (rewrite next_state_Send_all in * ).
        all: attac.
      }

      destruct IHMQ as [dm ?]; attac.
      destruct (alarm m) eqn:?; attac.
      unfold option_map.
      attac.
      rewrite `(lock_count _ = _) in *.
      rewrite `(self _ = _) in *.
      attac.
  Qed.

  Lemma net_get_deinstr : forall (MN : MNet) n, NetMod.get n '' MN = NetMod.get n MN.
    intros.
    unfold deinstr. attac.
  Qed.

  Import SrpcNet. (* TODO MOVE UP *)

  Lemma measure_ms_fin_net_recv : forall (MN0 MN1 : MNet) n0 n1,
      KIC MN0 ->
      lock MN0 n0 n1 ->
      (MN0 =(NComm n1 n0 R ^ (active_probe_of MN0 n0))=> MN1) ->
      exists dm, measure_ms_fin (MN1 n0) = Some dm.

  Proof.
    intros.
    smash_eq n0 n1.
    - assert (self (MN0 n0) = n0) by attac.
      assert (locked (MN0 n0) = Some n0) by attac.
      unfold active_probe_of, measure_ms_fin, NetGet in *.
      kill H1.
      eapply measure_ms_fin_recv with (n:=n0)(MS0:=N0' n0).
      + unfold NetGet.
        rewrite <- net_get_deinstr.
        assert (serv_lock [n0] (NetMod.get n0 '' MN0)) by attac.
        clear H5.
        kill H4.
        hsimpl.
        clear H H0 H2 H3.
        kill H5.
        unfold deinstr in *.
        rewrite NetMod.get_map in *.
        attac.
        rewrite H3 in *.
        kill H1.
        constructor; attac.
      + compat_hsimpl in *.
        compat_hsimpl in *.
        unfold NetGet.
        compat_hsimpl in *.
        rewrite H4 in *.
        attac.
      + unfold NetGet.
        compat_hsimpl in *.
        compat_hsimpl in *.
        rewrite H4 in *.
        simpl in *.
        subst.
        constructor.
    - eapply measure_ms_fin_recv with (n:=n1)(MS0:=MN0 n0).
      + unfold NetGet.
        rewrite <- net_get_deinstr.
        eapply lock_singleton; eauto with LTS.
      + eattac.
      + assert (self (MN0 n0) = n0) by attac.
        unfold active_probe_of in *.
        consider (_ =(_)=> _); unfold NetGet in *.
        compat_hsimpl in *; attac.
  Qed.

  Lemma measure_ms_recv_wait : forall (MS0 MS1 : MServ) n0 n1 p,
      serv_lock [n1] MS0 ->
      locked MS0 = Some n1 ->
      self MS0 <> origin p ->
      In n0 (wait MS0) ->
      (MS0 =(recv (n1, R) ^ p)=> MS1) ->
      exists dm, measure_ms n0 p MS1 = Some dm.
  Proof.
    intros.
    assert (NoRecvR_from n1 (mserv_q MS0)).
    {
      unfold NoRecvR_from; intros v ?.
      destruct MS0; attac.
      consider (serv_lock _ _).
      assert (~ In (n1, R, v) &I) by attac.
      destruct P; attac.
    }
    assert (NoSends_MQ (mserv_q MS0)).
    {
      destruct MS0; attac.
      consider (serv_lock _ _).
      destruct P; attac.
      eapply app_eq_nil in H7.
      attac.
      eapply Forall_forall.
      attac.
      apply in_split in H; attac.
      blast_cases; attac.
    }
    destruct MS0 as [MQ0 M0 S0].
    destruct MS1 as [MQ1 M1 S1].
    simpl in *.
    hsimpl in *.
    unfold measure_ms.
    generalize dependent M.
    clear H.

    induction MQ; attac.
    - generalize dependent n0.
      induction M; attac.
      1: {
        destruct b0; attac.
        destruct state; attac.
        blast_cases; attac.
        bs (false = true) by (eapply measure_mon_Send_all_in_found; eauto).
      }
      destruct (measure_mon n0 p M) eqn:?.
      destruct b; attac.
      destruct b0; attac.
      blast_cases; attac.
      bs (false = true) by (eapply measure_mon_Send_all_in_found; eauto).
      bs (false = true) by (eapply measure_mon_Send_all_in_found; eauto).
    - hsimpl in *.
      destruct b; attac.
      specialize IHMQ with (M:=mon_handle a M).

      assert (lock_count M = lock_count (mon_handle a M)).
      {
        destruct a; attac; blast_cases; attac.
        all: try (rewrite next_state_Send_all in * ).
        all: attac.
      }
      assert (locked M = locked (mon_handle a M)).
      {
        destruct a; attac; blast_cases; attac.
        all: try (rewrite next_state_Send_all in * ).
        all: attac.
      }
      assert (self M = self (mon_handle a M)).
      {
        destruct a; attac; blast_cases; attac.
        all: try (rewrite next_state_Send_all in * ).
        all: attac.
      }
      assert (In n0 (wait (mon_handle a M))).
      {
        destruct a; attac; blast_cases; attac.
        all: try (rewrite next_state_Send_all in * ).
        all: attac.
      }

      destruct IHMQ as [dm ?]; attac.
  Qed.

  Lemma measure_mon_restate : forall s0 s1 n p,
      measure_mon n p (MRecv s0) = measure_mon n p (MRecv s1).

  Proof. attac. Qed.

  Lemma measure_mon_handle : forall s n p a dm0,
      measure_mon n p (MRecv s) = (dm0, true) ->
      exists dm1, measure_mon n p (mon_handle a s) = (dm1, true).

  Proof.
    intros.
    generalize dependent dm0.
    induction (mon_handle a s); attac.
  Qed.

  Lemma measure_ms_recv_MQ : forall (MS0 MS1 : MServ) n0 n1 p v,
      serv_lock [n1] MS0 ->
      locked MS0 = Some n1 ->
      self MS0 <> origin p ->
      In (MqRecv (n0, Q) v) (mserv_q MS0) ->
      (MS0 =(recv (n1, R) ^ p)=> MS1) ->
      exists dm, measure_ms n0 p MS1 = Some dm.

  Proof.
    intros.
    assert (NoRecvR_from n1 (mserv_q MS0)).
    {
      unfold NoRecvR_from; intros v0 ?.
      destruct MS0; attac.
      consider (serv_lock _ _).
      assert (~ In (n1, R, v0) &I) by attac.
      destruct P; attac.
    }
    assert (NoSends_MQ (mserv_q MS0)).
    {
      destruct MS0; attac.
      consider (serv_lock _ _).
      destruct P; attac.
      eapply app_eq_nil in H7.
      attac.
      eapply Forall_forall.
      attac.
      apply in_split in H; attac.
      blast_cases; attac.
    }

    eapply in_split in H2 as (MQ0 & MQ0' & ?).

    destruct MS0 as [MQ M0 S0].
    destruct MS1 as [MQ1 M1 S1].

    subst; simpl in *; hsimpl in *.

    generalize dependent M MQ0'.
    induction MQ0.
    - intros.
      induction M; intros.
      + attac.
        consider (exists dm : nat,
                     measure_ms n0 p
                                {|
                                  mserv_q := MQ0' ++ [MqProbe (n1, R) p];
                                  mserv_m := mon_handle (MqRecv (n0, Q) v) state;
                                  mserv_s := P
                                |} = Some dm
                 ).
        {
          eapply measure_ms_recv_wait with
            (n0:=n0)
            (n1:=n1)
            (MS0:= {|
                    mserv_q := MQ0';
                    mserv_m := mon_handle (MqRecv (n0, Q) v) state;
                    mserv_s := P
                  |} ).
          all: destruct state; simpl in *; subst; simpl in *; eauto.
          - destruct P; attac.
            consider (serv_lock _ _).
            constructor; eauto.
            intros.
            intros ?.
            hsimpl in *.
            absurd (In (n, R, v0) (serv_i0 ++ (n0, Q, v) :: retract_recv MQ0')); attac.
            compat_hsimpl.
            attac.
          - attac.
        }

        destruct state; attac.
        unfold measure_ms in *; attac.
        rewrite H2.
        attac.
      + specialize (IHM ltac:(attac) ltac:(attac)).
        attac.
        unfold measure_ms in *.
        attac.
        blast_cases; attac.
    - intros.
      specialize IHMQ0 with (MQ0':=MQ0')(M:=mon_handle a M)
        as [dm ?]; attac.
      + consider (serv_lock _ _); attac.
        hsimpl in *.
        destruct a; attac.
        * rewrite `(_ = []).
          constructor; intros; eauto.
          intros ?.
          apply app_eq_nil in H13; hsimpl in *.
          apply app_eq_nil in H13; hsimpl in *.
          repeat (rewrite `(_ = []) in * ).
          repeat (rewrite app_nil_r in * ).

          eapply (H10 _ v1 eq_refl); eauto.
          eapply in_app_or in H5 as [|]; attac.
        * rewrite `(_ = []).
          constructor; intros; eauto.
          intros ?.
          apply app_eq_nil in H13; hsimpl in *.
          apply app_eq_nil in H13; hsimpl in *.
          repeat (rewrite `(_ = []) in * ).
          repeat (rewrite app_nil_r in * ).

          eapply (H10 _ v0 eq_refl); eauto.
      + destruct a; attac.
        all: blast_cases; attac.
        rewrite next_state_Send_all.
        attac.
      + destruct a; attac.
        all: blast_cases; attac.
        rewrite next_state_Send_all.
        attac.
      + clear H.
        unfold measure_ms in *.
        simpl in *.
        destruct (measure_mon n0 p M) eqn:?.
        hsimpl.
        destruct b; attac.
  Qed.

  Lemma measure_ms_net_recv : forall (MN0 MN1 : MNet) n0 n1 n2 p,
      KIC MN0 ->
      n0 <> n1 ->
      n1 <> n2 ->
      lock MN0 n0 n1 ->
      lock MN0 n1 n2 ->
      origin p <> n1 ->
      (MN0 =(NComm n2 n1 R ^ p)=> MN1) ->
      exists dm, measure_ms n0 p (MN1 n1) = Some dm.

  Proof.
    intros.
    destruct (NoRecvQ_from_dec n0 (mserv_q (MN0 n1))).
    - eapply measure_ms_recv_wait with (n1:=n2)(n0:=n0)(MS0:=MN0 n1); eauto with LTS.
      + unfold NetGet.
        rewrite <- net_get_deinstr.
        eapply lock_singleton; eauto with LTS.
      + assert (self (MN0 n1) = n1); attac.
        (* now rewrite H5. *)
      + consider (KIC _); attac.
      + unfold NetGet, NoRecvQ_from in *.
        consider (_ =(_)=> _); compat_hsimpl in *.
        attac.

    - consider (exists v, In (MqRecv (n0, Q) v) (mserv_q (MN0 n1))).
      {
        clear - H6.
        induction (mserv_q (MN0 n1)); attac.
        unfold NoRecvQ_from in *; attac.
        destruct a as [[n [|]] | [n [|]] | [n [|]]]; smash_eq n0 n; attac.
        all: apply IHl.
        all: intros ?.
        all: attac.
      }
      eapply measure_ms_recv_MQ with (n1:=n2)(n0:=n0)(MS0:=MN0 n1); eauto with LTS.
      + unfold NetGet.
        rewrite <- net_get_deinstr.
        eapply lock_singleton; eauto with LTS.
      + assert (self (MN0 n1) = n1); attac.
      + unfold NetGet, NoRecvQ_from in *.
        consider (_ =(_)=> _); compat_hsimpl in *.
        attac.
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
      blast_cases; attac.
    - blast_cases; attac.
      + exists [], (L ++ [n1]); attac.
      + apply IHL in Heqo0.
        hsimpl in *.
        exists (n0::L0), L1.
        attac.
  Qed.


  Lemma measure_lock_chain_in_l : forall (MN0 : MNet) (n0 n1 m0 m1 : Name) (L : list Name) p dm,
      measure_lock_chain MN0 n0 L n1 p = Some (m0, m1, dm) ->
      m0 = n0 \/ In m0 L.

  Proof.
    intros.
    generalize dependent n0 dm.
    induction L; attac.
    blast_cases; attac.
    blast_cases; attac.
    eapply IHL in Heqo0 as [|]; attac.
  Qed.

  Lemma measure_lock_chain_in_r : forall (MN0 : MNet) (n0 n1 m0 m1 : Name) (L : list Name) p dm,
      measure_lock_chain MN0 n0 L n1 p = Some (m0, m1, dm) ->
      m1 = n1 \/ In m1 L.

  Proof.
    intros.
    generalize dependent n0 dm.
    induction L; attac.
    blast_cases; attac.
    blast_cases; attac.
    eapply IHL in Heqo0 as [|]; attac.
  Qed.


  Lemma measure_lock_chain_cut : forall (MN0 : MNet) (n0 n1 m0 m1 : Name)
                                   (L0 L1 : list Name) p dm,
      measure_lock_chain MN0 n0 (L0 ++ [m0]) m1 p = Some (m0, m1, dm) ->
      measure_lock_chain MN0 n0 (L0 ++ m0 :: m1 :: L1) n1 p = Some (m0, m1, dm).

  Proof.
    intros.
    generalize dependent dm n0.
    induction L0; attac.
    - blast_cases; attac.
    - blast_cases; attac.
      eapply IHL0 in Heqo0.
      rewrite Heqo0 in Heqo1.
      attac.
  Qed.

  Lemma measure_lock_chain_len : forall (MN0 : MNet) (n0 n1 m0 m1 : Name)
                                   (L0 L1 : list Name) p dmf,
      measure_lock_chain MN0 n0 (L0 ++ [m0]) m1 p = None ->
      measure_ms m0 p (MN0 m1) = Some dmf ->
      measure_lock_chain MN0 n0 (L0 ++ m0 :: m1 :: L1) n1 p =
        Some (m0, m1, {|dm_pass := S (length L0); dm_flush := dmf|}).

  Proof.
    intros.
    generalize dependent n0.
    induction L0; attac.
    - blast_cases; attac.
    - blast_cases; attac.
      eapply IHL0 in Heqo0.
      rewrite Heqo0 in Heqo1.
      attac.
  Qed.


  Lemma measure_lock_chain_tip : forall (MN0 : MNet) (n0 n1 m0 m1 : Name)
                                   (L0 L1 : list Name) p dm,
      n1 <> m1 ->
      measure_lock_chain MN0 n0 (L0 ++ [m0]) n1 p = Some (m0, m1, dm) ->
      measure_lock_chain MN0 n0 L0 m0 p = Some (m0, m1, dm).

  Proof.
    intros.
    generalize dependent dm n0.
    induction L0; attac.
    - blast_cases; attac.
    - blast_cases; attac.
      eapply IHL0 in Heqo0.
      rewrite Heqo0 in Heqo1.
      attac.
  Qed.

  Lemma measure_lock_chain_behead : forall (MN0 : MNet) (n0 n1 m0 m1 : Name)
                                      (L0 L1 : list Name) p dm,
      measure_lock_chain MN0 n0 (L0 ++ m0 :: m1 :: L1) n1 p = Some (m0, m1, dm) ->
      measure_lock_chain MN0 n0 (L0 ++ [m0]) m1 p = Some (m0, m1, dm).

  Proof.
    intros.

    generalize dependent dm n0.
    induction L0; attac.
    - destruct (measure_ms n0 p (MN0 m0)) eqn:?; attac.
      destruct (measure_ms m0 p (MN0 m1)) eqn:?; attac.
      destruct (measure_lock_chain MN0 m1 L1 n1 p) as [[[m0' m1'] dm'] | ] eqn:?; attac.
      destruct dm'; attac.
      eapply measure_lock_chain_split in Heqo1.
      attac.
    - blast_cases; attac.
      eapply IHL0 in Heqo0; attac.
  Qed.

  Lemma measure_lock_chain_swap : forall (MN0 : MNet) (n0 n1 m0 m1 : Name)
                                   (L0 L1 L1' : list Name) p dm,
      measure_lock_chain MN0 n0 (L0 ++ m0 :: m1 :: L1) n1 p = Some (m0, m1, dm) ->
      measure_lock_chain MN0 n0 (L0 ++ m0 :: m1 :: L1') n1 p = Some (m0, m1, dm).

  Proof.
    intros.
    generalize dependent dm n0.
    induction L0; attac.
    - destruct (measure_ms n0 p (MN0 m0)) eqn:?. attac.
      destruct (measure_ms m0 p (MN0 m1)) eqn:?. attac.
      destruct (measure_lock_chain MN0 m1 L1 n1 p) as [[[m0' m1'] dm'] | ] eqn:?.
      destruct dm'; attac.
      + eapply measure_lock_chain_split in Heqo1; attac.
      + bs.
    - blast_cases; attac.
      eapply IHL0 in Heqo0; attac.
  Qed.


  Lemma measure_lock_chain_split_nth : forall (MN0 : MNet) (n0 n1 m0 m1 : Name) (L : list Name) p dm,
      NoDup L ->
      n0 <> m0 ->
      n1 <> m1 ->
      measure_lock_chain MN0 n0 L n1 p = Some (m0, m1, dm) ->
      exists L0 L1, L = L0 ++ m0 :: m1 :: L1
               /\ ~ In m0 L0
               /\ measure_ms m0 p (MN0 m1) = Some (dm_flush dm)
               /\ measure_lock_chain MN0 n0 L0 m0 p = None
               /\ dm_pass dm = S (S (length L0)).

  Proof.
    intros.

    generalize dependent n0 m0 m1 n1 dm.
    induction L; intros; simpl in *; hsimpl in *.
    1: { blast_cases; attac. }

    consider (NoDup (_ :: _)).

    destruct (measure_ms n0 p (MN0 a)) eqn:?; attac.
    destruct (measure_lock_chain MN0 a L n1 p) as [[[m0' m1'] dm'] | ] eqn:?; attac.
    destruct dm'; attac.

    smash_eq m0 a.
    - consider (exists L', L = m1 :: L').
      {
        assert (m1 = n1 \/ In m1 L) by eauto using measure_lock_chain_in_r.
        attac.
        clear IHL.

        destruct L.
        1: clear Heqo0; simpl in *; blast_cases; attac.

        consider (NoDup (_ :: _)).
        smash_eq n m1. eattac.
        hsimpl in *.

        exfalso.
        simpl in *.
        destruct (measure_ms m0 p (MN0 n)) eqn:?; attac.
        destruct (measure_lock_chain MN0 n L n1 p) as [[[m0' m1'] dm'] | ] eqn:?; attac.
        destruct dm'; attac.

        assert (m0 = n \/ In m0 L) by eauto using measure_lock_chain_in_l.
        attac.
      }
      exists [], L'.
      simpl.
      repeat split; auto.
      + simpl in *.
        destruct (measure_ms m0 p (MN0 m1)) eqn:?; attac.
        destruct (measure_lock_chain MN0 m1 L' n1 p) as [[[m0' m1'] dm'] | ] eqn:?; attac.
        destruct dm'; attac.

        consider (NoDup (_ :: _)).
        assert (m1 = n1 \/ In m1 L') by eauto using measure_lock_chain_in_r.
        attac.
      + destruct (measure_ms n0 p (MN0 m0)) eqn:?; attac.
      + simpl in *.
        destruct (measure_ms m0 p (MN0 m1)) eqn:?; attac.
        destruct (measure_lock_chain MN0 m1 L' n1 p) as [[[m0' m1'] dm'] | ] eqn:?; attac.
        destruct dm'; attac.

        consider (NoDup (_ :: _)).
        assert (m1 = n1 \/ In m1 L') by eauto using measure_lock_chain_in_r.
        attac.
    - eapply IHL in Heqo0; eauto.
      clear IHL.
      hsimpl in *.
      exists (a :: L0), L1; attac.
  Qed.

  Lemma measure_ms_send_zero : forall MS0 MS1 n p,
      (MS0 =(send (n, R) ^ p)=> MS1) ->
      measure_ms n p MS0 = Some 1.

  Proof.
    intros.
    destruct MS0; attac.
    unfold measure_ms; attac.
  Qed.

  Lemma measure_ms_net_send_zero : forall (MN0 MN1 : MNet) n0 n1 p,
      (MN0 =(NComm n1 n0 R ^ p)=> MN1) ->
      measure_ms n0 p (MN0 n1) = Some 1.

  Proof.
    intros.
    consider (MN0 =(_)=> _).
    kill H0.
    eauto using measure_ms_send_zero.
  Qed.

  Lemma dm_ltb_pass : forall dm0 dm1, dm_pass dm0 < dm_pass dm1 ->
                                 dm_ltb dm0 dm1 = true.
  Proof.
    intros.
    destruct dm0, dm1; simpl in *.
    unfold dm_ltb in *; simpl.
    destruct (dm_pass0 =? dm_pass1) eqn:?.
    attac.
    now rewrite PeanoNat.Nat.ltb_lt.
  Qed.

  Hint Resolve dm_ltb_pass : LTS.


  Lemma measure_lock_chain_extend : forall (MN0 : MNet) L n0 m0 m1 dmm p,
      measure_lock_chain MN0 n0 L m0 p = None ->
      measure_ms m0 p (MN0 m1) = Some dmm ->
      measure_lock_chain MN0 n0 (L ++ [m0]) m1 p =
        Some (m0, m1, {|dm_pass := S (S (length L)); dm_flush := dmm|}).

  Proof.
    intros.
    generalize dependent n0.
    induction L; attac.
    1: blast_cases; attac.

    destruct (measure_ms n0 p (MN0 a)) eqn:?; attac.
    destruct (measure_lock_chain MN0 a L m0 p) as [[[m0' m1'] dm'] | ] eqn:?; attac.
    - destruct dm'; attac.
    - eapply IHL in Heqo0.
      rewrite Heqo0; attac.
  Qed.


  Lemma measure_lock_chain_cut_None : forall MN n0 n1 n2 L0 L1 p,
      measure_lock_chain MN n0 (L0 ++ n1 :: L1) n2 p = None ->
      measure_lock_chain MN n0 L0 n1 p = None.

  Proof.
    intros.
    generalize dependent n0.
    induction L0; attac.
    - blast_cases; attac.
    - blast_cases; attac.
      eapply IHL0 in Heqo0.
      bs.
  Qed.


  Lemma measure_lock_chain_decapitate :
    forall (MN0 MN1 : MNet) (n0 n1 n2 n3 : Name) (L0 L1 : list Name) p,
      KIC MN0 ->
      NoDup (L0 ++ n1::n2::n3::L1) ->
      origin p <> n2 ->
      lock_chain MN0 n0 L0 n1 ->
      lock MN0 n1 n2 ->
      lock MN0 n2 n3 ->
      (MN0 =(NComm n3 n2 R ^ p)=> MN1) ->
      measure_lock_chain MN0 n0 (L0 ++ [n1]) n2 p = None ->
      measure_lock_chain MN1 n0 L0 n1 p = None.

  Proof.
    intros.

    assert (n1 <> n2) by (apply NoDup_app_remove_l in H0; kill H0; attac).
    assert (n1 <> n3) by (apply NoDup_app_remove_l in H0; kill H0; attac).
    assert (n2 <> n3) by (apply NoDup_app_remove_l in H0; kill H0; consider (NoDup (_ :: _)); attac).
    assert (forall n, In n L0 -> MN1 n = MN0 n).
    {
      intros.
      enough (n <> n2 /\ n <> n3) as [? ?].
      {
        unfold NetGet.
        eauto using NComm_neq_stay, eq_sym.
      }
      apply in_split in H10.
      hsimpl in H10.
      rewrite <- app_assoc in *.
      rewrite <- app_comm_cons in *.
      apply NoDup_app_remove_l in H0.
      kill H0.
      attac.
    }
    assert (MN1 n1 = MN0 n1) by eauto using NComm_neq_stay, eq_sym.

    assert (measure_lock_chain MN0 n0 L0 n1 p = None)
      by eauto using measure_lock_chain_cut_None.
    clear0 [(find_i '(measure_lock_chain _ _ (_ ++ _) _ _ = None) None)].

    generalize dependent n0.
    induction L0; intros; simpl in *.
    - blast_cases; attac.
    - rewrite H10; eauto.
      destruct (measure_ms n0 p (MN0 a)) eqn:?; attac.
      destruct (measure_lock_chain MN0 a L0 n1 p) as [[[m0' m1'] dm']|] eqn:?.
      + destruct dm'; attac.
      + eapply IHL0 in Heqo0; eauto.
        attac.
        bs.
  Qed.

  Lemma measure_lock_chain_pass : forall (MN0 MN1 : MNet) (n0 n1 m0 m1 : Name)
                                   (L : list Name) p dm0,
      KIC MN0 ->
      NoDup L ->
      n0 <> m0 ->
      n1 <> m1 ->
      lock_chain MN0 n0 L n1 ->
      measure_lock_chain MN0 n0 L n1 p = Some (m0, m1, dm0) ->
      (MN0 =(NComm m1 m0 R ^ p)=> MN1) ->
      origin p <> m0 ->
      exists m' dm1,
        measure_lock_chain MN1 n0 L n1 p = Some (m', m0, dm1)
        /\ dm_ltb dm1 dm0 = true.

  Proof.
    intros.
    apply measure_lock_chain_split_nth in H4; auto.
    assert (measure_ms m0 p (MN0 m1) = Some 1) by eauto using measure_ms_net_send_zero.
    hsimpl in *.

    destruct L0 using rev_ind; attac.
    - consider (NoDup (_ :: _)).
      consider (NoDup (_ :: _)).
      eapply measure_ms_net_recv in H5; auto.
      4: eauto.
      all: auto.
      2: attac.
      hsimpl in *.
      eexists _, _.
      split; eauto.
      eapply dm_ltb_pass.
      simpl; attac.
    - clear IHL0.
      rewrite <- app_assoc in *.
      simpl in *.

      consider (exists dm : nat, measure_ms x p (MN1 m0) = Some dm).
      {
        eapply measure_ms_net_recv in H5; auto.
        4: eauto.
        all: auto.
        consider (NoDup (_ :: _ :: _)) by eauto using NoDup_app_remove_l.
        consider (NoDup (_ :: _)); consider (NoDup (_ :: _)); attac.
      }

      assert (measure_lock_chain MN1 n0 L0 x p = None)
        by eauto using measure_lock_chain_decapitate with LTS.

      eapply measure_lock_chain_extend in H16.
      2: eauto.

      eapply measure_lock_chain_cut in H16.
      eexists _, _.
      split; eauto.
      destruct dm0; simpl in *.
      subst.
      eapply dm_ltb_pass.
      simpl.
      lia.
  Qed.


  Lemma measure_lock_chain_flush : forall (MN0 MN1 : MNet) (n0 n1 m0 m1 : Name)
                                    (L : list Name) p dm0 a,
      KIC MN0 ->
      NoDup L ->
      n0 <> m0 ->
      n1 <> m1 ->
      lock_chain MN0 n0 L n1 ->
      measure_lock_chain MN0 n0 L n1 p = Some (m0, m1, dm0) ->
      Flushing_NAct m1 a ->
      (MN0 =(a)=> MN1) ->
      origin p <> m0 ->
      exists m0' m1' dm1,
        measure_lock_chain MN1 n0 L n1 p = Some (m0', m1', dm1)
        /\ dm_ltb dm1 dm0 = true.

  Proof.
    intros.
    have (measure_lock_chain MN0 n0 L n1 p = Some (m0, m1, dm0)).
    apply measure_lock_chain_split_nth in H4; eauto.
    hsimpl in *.

    destruct (dm_flush dm0) eqn:?.
    1: {
      clear - H10.
      exfalso.
      unfold measure_ms in *.
      destruct (MN0 m1). simpl in *.
      destruct (measure_mon m0 p mserv_m0) eqn:?.
      hsimpl in *.
      blast_cases; attac.
      - induction mserv_m0; attac. blast_cases; attac.
      - rewrite PeanoNat.Nat.add_succ_r in *. lia.
    }

    destruct n.
    - eapply measure_ms_net_send in H10; eauto.
      subst.
      enough (exists m' dm1,
                 measure_lock_chain MN1 n0 (L0 ++ m0 :: m1 :: L1) n1 p = Some (m', m0, dm1) /\
                 dm_ltb dm1 dm0 = true)
        by attac.

      re_have eauto using measure_lock_chain_pass with LTS.
    - assert (measure_ms m0 p (MN1 m1) = Some (S n)) by eauto using measure_ms_net_decr.

      clear H8.
      assert (a = NComm m1 m0 R ^ p \/ a <> NComm m1 m0 R ^ p) as [|].
      {
        clear; destruct a; attac.
        destruct p0; attac;
          destruct (MProbe_eq_dec m p); attac;
          smash_eq n m1; smash_eq n0 m0; attac; destruct t; attac. right; intros ?; attac.
      }
      1: { subst; eapply measure_ms_net_send_zero in H6; bs. }

      assert (m0 <> m1) by (apply NoDup_app_remove_l in H0; kill H0; attac).
      assert (~ In m1 L0).
      {
        change (L0 ++ m0 :: m1 :: L1) with (L0 ++ [m0;m1] ++ L1) in H0.
        rewrite app_assoc in H0.
        apply NoDup_app_remove_r in H0.
        apply NoDup_remove_1 in H0.
        apply NoDup_rev in H0.
        rewrite rev_app_distr in H0.
        simpl in *.
        consider (NoDup (_ :: _)).
        rewrite in_rev in H16.
        rewrite rev_involutive in H16.
        auto.
      }

      destruct (measure_lock_chain MN1 n0 L0 m0 p) as [[[m0' m1'] dm'] | ] eqn:?.
      2: {
        exists m0, m1.
        eexists _.
        split.
        - eapply measure_lock_chain_cut.
          eauto using measure_lock_chain_extend.
        - destruct dm0; attac.
          unfold dm_ltb; attac.
      }

      have (measure_lock_chain MN1 n0 L0 m0 p = Some (m0', m1', dm')).
      eapply measure_lock_chain_split in Heqo.
      hsimpl in Heqo.
      destruct L2; destruct L3 using rev_ind; simpl in *.
      + assert (L0 = []).
        {
          clear - Heqo; induction L0; attac.
        }
        attac.
        eexists _, _, _.
        split; eauto.
        eapply dm_ltb_pass.
        simpl.
        attac.
      + clear IHL3.
        assert (L0 = m1' :: L3 /\ x = m0).
        {
          clear - Heqo; kill Heqo.
          destruct L0; kill H0.
          bs.
          split; f_equal.
          - generalize dependent L3.
            induction L0; attac.
            induction L3; attac.
            destruct L3; kill H1.
            attac.
            apply IHL0 in H0.
            attac.
          - generalize dependent L3.
            induction L0; attac.
            induction L3; attac.
            destruct L3; kill H1.
            attac.
            apply IHL0 in H0.
            attac.
        }

        attac.
        eexists _, _, _.
        split; eauto.
        eapply dm_ltb_pass.
        simpl.
        attac.
      + assert (L0 = L2 ++ [m0'] /\ m1' = m0).
        {
          clear - Heqo; kill Heqo.
          split; f_equal.
          - generalize dependent L2.
            induction L0; attac.
            induction L2; attac.
            destruct L2; kill H0.
            attac.
            destruct L0; attac.
            apply IHL0 in H1.
            attac.
          - generalize dependent L2.
            induction L0; attac.
            induction L2; attac.
            destruct L2; kill H0.
            attac.
            induction L0; attac.
            apply IHL0 in H1.
            attac.
        }
        attac.
        eexists _, _, _.
        rewrite <- app_assoc.
        split.
        kill H17.
        eapply measure_lock_chain_cut in H23; re_have eauto.
        eapply H23.
        eapply dm_ltb_pass.
        attac.
      + clear IHL3.
        assert (L0 = L2 ++ m0' :: m1' :: L3 /\ x = m0).
        {
          clear - Heqo.
          kill Heqo.
          generalize dependent L2 L3.
          induction L0; attac.
          - induction L2; attac.
          - induction L2; attac.
          - destruct L2; simpl in *; kill H0.
            + induction L3; attac.
              * destruct L0; attac.
                induction L0; attac.
              * destruct L0; kill H1.
                clear - H0.
                destruct L0; kill H0.
                induction L3; attac.
                enough (L0 = L3) by attac.
                generalize dependent L3 x m0.
                induction L0; attac.
                induction L3; attac.
                destruct L3; kill H1.
                attac.
                apply eq_sym in H0.
                eapply IHL0 in H0.
                attac.
            + eapply IHL0 in H1.
              attac.

          - destruct L2; simpl in *; kill H0.
            + induction L3; attac.
              * destruct L0; attac.
                induction L0; attac.
              * destruct L0; kill H1.
                clear - H0.
                destruct L0; kill H0.
                induction L3; attac.
                enough (L0 = L3) by attac.
                generalize dependent L3 x m0.
                induction L0; attac.
                induction L3; attac.
                destruct L3; kill H1.
                attac.
                apply eq_sym in H0.
                eapply IHL0 in H0.
                attac.
            + eapply IHL0 in H1.
              attac.
        }
        attac.
        eexists m0', m1', dm'.
        rewrite <- app_assoc.
        rewrite <- app_comm_cons.
        rewrite <- app_comm_cons.
        split.
        kill H17.
        eapply measure_lock_chain_behead in H26; re_have eauto.
        eapply measure_lock_chain_cut; eauto.
        eapply dm_ltb_pass.
        attac.
  Qed.


  Lemma measure_lock_chain_head : forall (MN0 : MNet) (n0 n1 m1 : Name)
                                    (L : list Name) dm0 p,
      measure_lock_chain MN0 n0 L n1 p = Some (n0, m1, dm0) ->
      measure_ms n0 p (MN0 m1) = Some (dm_flush dm0).

  Proof.
    intros.
    apply measure_lock_chain_split in H.
    hsimpl in *.
    auto.
  Qed.

  Lemma measure_lock_chain_finish : forall (MN0 MN1 : MNet) (n0 n1 m1 : Name)
                                      (L : list Name) dm0 a,
      KIC MN0 ->
      NoDup L ->
      lock_chain MN0 n0 L n1 ->
      measure_lock_chain MN0 n0 L n1 (active_probe_of MN0 n0) = Some (n0, m1, dm0) ->
      Flushing_NAct m1 a ->
      (MN0 =(a)=> MN1) ->
      (exists dm, measure_ms_fin (MN1 n0) = Some dm) \/
        exists dm1, measure_lock_chain MN1 n0 L n1 (active_probe_of MN0 n0) = Some (n0, m1, dm1) /\ dm_ltb dm1 dm0 = true.

  Proof.
    intros.

    assert ((L = [] /\ m1 = n1) \/ exists L', L = m1 :: L').
    {
      remember (active_probe_of MN0 n0) as p.
      destruct L; attac.
      - left.
        split; auto.
        blast_cases; attac.
      - right.
        blast_cases; attac.
        enough (n = m1) by attac.
        enough (lock MN0 n0 m1) by (eapply SRPC_lock_set_uniq; eattac).
        clear - Heqo0 H5.
        generalize dependent n dm_flush0 dm_pass0.
        induction L; attac.
        blast_cases; attac.
        blast_cases; attac.
    }

    assert (dm_pass dm0 = 1).
    {
      assert (measure_ms n0 (active_probe_of MN0 n0) (MN0 m1) = Some (dm_flush dm0))
        by (apply measure_lock_chain_head in H2; attac).
      destruct dm0.
      destruct `(_ \/ _); attac.
    }

    apply measure_lock_chain_head in H2.
    destruct dm0; simpl in *.
    destruct dm_flush0.
    {
      clear - H2.
      exfalso.
      unfold measure_ms in *.
      remember (active_probe_of MN0 n0) as p. clear Heqp.
      remember (MN0 m1) as MS1. clear HeqMS1.
      destruct (measure_mon n0 p MS1) eqn:?.
      hsimpl in H2.
      blast_cases; attac.
      induction MS1; attac.
      induction mserv_m0; attac.
      blast_cases; attac.
      induction n; attac.
    }

    destruct dm_flush0.
    - left.
      eapply measure_ms_net_send in H2; eauto.
      subst.
      destruct `(_ \/ _); hsimpl in *.
      + eapply measure_ms_fin_net_recv with (n1:=n1); eauto.
      + eapply measure_ms_fin_net_recv with (n1:=m1); eauto.
    - right.
      eapply measure_ms_net_decr in H2; eauto.
      destruct `(_ \/ _); hsimpl in *.
      + blast_cases; attac.
        eexists. split; eauto.
        unfold dm_ltb; attac.
      + blast_cases; attac.
        eexists. split; eauto.
        unfold dm_ltb; attac.
  Qed.


  Lemma measure_lock_chain_point : forall (MN0 : MNet) (n0 n1 m0 m1 : Name)
                                     (L0 L1 : list Name) p dmf,
      measure_ms m0 p (MN0 m1) = Some dmf
      exists dm m0' m1',
        measure_lock_chain MN0 n0 (L0 ++ m0 :: m1 :: L1) n1 p = Some (m0', m1', dm)
        /\ dm_leb dm {|dm_pass := S (length L0); dm_flush :=  |}



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
      exists m0' m1' dm1, measure_lock_chain MN1 n0 L n1 p = Some (m0', m1', dm1) /\ dm_ltb dm1 dm0 = true.

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
        clear - H12. rewrite PeanoNat.Nat.add_1_r. unfold dm_leb, dm_ltb in *.
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
          unfold dm_ltb, dm_leb; simpl.
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
          unfold dm_ltb, dm_leb; simpl.
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
      exists m0' m1' dm1, measure_loop MN1 n L = Some (m0', m1', dm1) /\ alarm (MN0 n) || dm_ltb dm1 dm0 = true.

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
      admit.
    - unfold NetGet in *.
      consider (_ =(_)=> _); compat_hsimpl in *.
      + consider (exists dm1, measure_ms_fin &S = Some dm1 /\ dm1 <= n0) by
          eauto using measure_ms_fin_noincr.
        attac.
      + consider (exists dm1, measure_ms_fin &S0 = Some dm1 /\ dm1 <= n0) by
          eauto using measure_ms_fin_noincr.
        attac.
        smash_eq m1 n'; attac.
        consider (exists dm2, measure_ms_fin &S = Some dm2 /\ dm2 <= dm1)
          by eauto using measure_ms_fin_noincr.
        bs.
    - eexists _, _, _. split; eauto.
      destruct (alarm (MN0 n)) eqn:?; attac.

      unfold NetGet in *.
      destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.
      destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.
      unfold measure_ms_fin in *.
      simpl in *.
      destruct a.
      + consider (_ =(_)=> _); compat_hsimpl in *; simpl in *.
        smash_eq n m1.
        * rewrite `(NetMod.get n MN0 = _) in *.
          exfalso.
          unfold option_map in *.
          blast_cases; attac;
            compat_hsimpl in *;
            blast_cases; attac.
          blast_cases; attac;
            compat_hsimpl in *;
            blast_cases; attac.
        * exfalso.
          blast_cases; attac;
            compat_hsimpl in *;
            blast_cases; attac.
      + smash_eq m1 n1.
        destruct (alarm M1) eqn:?.
        {
          exfalso.
          consider (_ =(_)=> _); compat_hsimpl in *; simpl in *.
          smash_eq n m1 n2; destruct p; compat_hsimpl in *; attac.
        }

  (*       hsimpl in *. *)
  (*       destruct MQ1; attac. *)
  (*       consider (_ =(_)=> _); compat_hsimpl in *; simpl in *. *)
  (*       unfold option_map in *. *)
  (*       destruct (measure_mon_fin M1) eqn:?. *)
  (*       destruct (measure_mq_fin (mon_handle e m) MQ1) eqn:?; doubt. *)
  (*       hsimpl in *. *)
  (*       destruct L; simpl in *; unfold measure_ms, active_probe_of, NetGet in *. *)
  (*       ++ smash_eq n n2 m1; *)
  (*            blast_cases; doubt; *)
  (*            hsimpl in *; *)
  (*            blast_cases; attac; *)
  (*            compat_hsimpl in *; *)
  (*            blast_cases; attac. *)
  (*       ++ hsimpl in *. *)
  (*          blast_cases; simpl in *; attac. *)

  (*   - destruct (dm_pass dm0) as [|dm_pass0] eqn:?. *)
  (*     1: { *)
  (*       exfalso. *)
  (*       destruct L; simpl in *; blast_cases; attac. *)
  (*     } *)

  (*     destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?. *)
  (*     destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?. *)

  (*     destruct dm_pass0. *)
  (*     + destruct dm0. *)
  (*       simpl in *. *)

  (*       destruct a. *)
  (*       * hsimpl in *. *)
  (*         destruct dm_flush0. *)
  (*         1: { *)
  (*           clear - H5 Heqo Heqm. *)
  (*           exfalso. *)
  (*           destruct L; simpl in *. *)
  (*           - unfold measure_ms, NetGet in *. *)
  (*             hsimpl in *. *)
  (*             destruct (measure_mon n (active_probe_of MN0 n) M0) eqn:?. *)
  (*             hsimpl in *. *)
  (*             destruct b; attac. *)
  (*             + clear - Heqp. *)
  (*               induction M0; attac. blast_cases; attac. *)
  (*             + blast_cases; attac. *)
  (*               rewrite PeanoNat.Nat.add_succ_r in *. *)
  (*               lia. *)
  (*           - unfold measure_ms, NetGet in *. *)
  (*             hsimpl in *. *)
  (*             blast_cases; attac. *)
  (*             + destruct (NetMod.get m1 MN0). *)
  (*               simpl in *. *)
  (*               destruct (measure_mon m0 (active_probe_of MN0 m0) mserv_m0) eqn:?. *)
  (*               hsimpl in *. *)
  (*               blast_cases; attac. *)
  (*               * clear  - Heqp. *)
  (*                 induction mserv_m0; attac; blast_cases; attac. *)
  (*               * blast_cases; attac. *)
  (*                 rewrite PeanoNat.Nat.add_succ_r in *. *)
  (*                 lia. *)
  (*             + generalize dependent n0 n. *)
  (*               induction L; attac; unfold measure_ms, NetGet in *; simpl in *. *)
  (*               * destruct (NetMod.get n0 MN0). *)
  (*                 destruct (NetMod.get n MN0). *)
  (*                 destruct (measure_mon n0 (active_probe_of MN0 n) M0) eqn:?. *)
  (*                 hsimpl in *. *)
  (*                 blast_cases; attac. *)
  (*               * destruct (NetMod.get a MN0). *)
  (*                 destruct (NetMod.get n0 MN0). *)
  (*                 destruct (measure_mon n0 (active_probe_of MN0 n) mserv_m0) eqn:?. *)
  (*                 hsimpl in *. *)
  (*                 blast_cases; attac. *)
  (*         } *)

  (*         exists m0 *)


  (*               * clear  - Heqp. *)
  (*                 induction mserv_m0; attac; blast_cases; attac. *)
  (*               * blast_cases; attac. *)
  (*                 rewrite PeanoNat.Nat.add_succ_r in *. *)
  (*                 lia. *)
  (*             + *)

  (*             destruct (measure_mon n (active_probe_of MN0 n) M0) eqn:?. *)
  (*             hsimpl in *. *)
  (*             destruct b; attac. *)
  (*             + clear - Heqp. *)
  (*               induction M0; attac. blast_cases; attac. *)
  (*             + blast_cases; attac. *)
  (*               rewrite PeanoNat.Nat.add_succ_r in *. *)
  (*               lia. *)
  (*           induction L; simpl in *; unfold measure_ms_fin, measure_ms, NetGet in *. *)
  (*           - attac. *)
  (*             blast_cases; attac. *)
  (*             destruct MQ0; attac. *)
  (*             admit. *)
  (*             blast_cases; unfold option_map in *; blast_cases; attac. *)

  (*             generalize dependent M0. *)
  (*             induction MQ0; attac. *)
  (*             + blast_cases; attac. *)
  (*               induction M0; attac. *)
  (*               blast_cases; attac. *)
  (*             + blast_cases; attac. *)
  (*               unfold option_map in *; attac. *)
  (*               blast_cases; attac. *)
  (*         } *)
  (*         exists m0, m1,  *)
  (*         exfalso. *)
  (*         destruct L; simpl in *; blast_cases; attac. *)

  (*       destruct L; simpl in *; unfold measure_ms, active_probe_of, NetGet in *. *)
  (*       * hsimpl in *. *)
  (*         destruct (measure_mq n {| origin := n; lock_id := lock_count M0 |} M0 MQ0) eqn:?; doubt. *)
  (*         hsimpl in *. *)
  (*         destruct (measure_mq m1 {| origin := m1; lock_id := lock_count M0 |} M1 MQ1) eqn:?. *)
  (*         -- eexists _, _, _; split; eauto. *)
  (*            destruct (alarm M0) eqn:?; attac. *)
  (*            unfold dm_ltb; attac. *)
  (*            destruct_mna a; consider (_ =(_)=> _); compat_hsimpl in *; doubt. *)
  (*            all: hsimpl in *. *)
  (*            all: subst; simpl in *. *)

  (*            all: repeat (Control.enter *)
  (*                           (fun () => match! goal with *)
  (*                                     [_ : context [match ?x with _ => _ end] |-_] => *)
  (*                                       destruct $x eqn:?; simpl in * *)
  (*                                   end)). *)
  (*            all: hsimpl in *. *)
  (*            all: attac. *)
  (*            all: Control.enter *)
  (*                   (fun () => *)
  (*                      try (match! goal with *)
  (*                             [|- (if n =? S n then _ else _) = _] => *)
  (*                               clear; *)
  (*                               destruct (n =? S n) eqn:?; hsimpl in *; *)
  (*                               doubt; *)
  (*                               apply PeanoNat.Nat.leb_le; lia *)
  (*                           end *)
  (*                        ) *)
  (*                   ). *)
  (*            ++ rewrite `(NetMod.get m1 _ = _) in *. *)
  (*               smash_eq m1 n1; attac. *)
  (*               ** unfold measure_ms_fin in *. *)
  (*                  simpl in *. *)
  (*                  ltac1:(rewrite_strat innermost fold (MQ ++ [MqProbe (m1, Q) m]) in Heqo0). *)
  (*                  ltac1:(rewrite_strat innermost fold (MQ ++ [MqProbe (m1, Q) m]) in Heqo2). *)
  (*                  rewrite `(NetMod.get m1 _ = _) in *. *)
  (*                  simpl in *. *)
  (*                  hsimpl in *. *)
  (*                  unfold option_map in *. *)
  (*                  destruct MQ; attac. *)
  (*                  --- destruct (measure_mon m1 {| origin := m1; lock_id := lock_count M1 |} M1) eqn:?. *)
  (*                      destruct b; attac. *)
  (*                      destruct (measure_mon_fin M1) eqn:?. *)
  (*                      clear; *)
  (*                        destruct (n =? S n) eqn:?; hsimpl in *; *)
  (*                        doubt; *)
  (*                        apply PeanoNat.Nat.leb_le; lia. *)
  (*                  --- destruct (measure_mon m1 {| origin := m1; lock_id := lock_count M1 |} M1) eqn:?. *)
  (*                      destruct (measure_mon_fin M1) eqn:?. *)
  (*                      destruct b; attac. *)
  (*                      +++ clear; *)
  (*                            destruct (n =? S n) eqn:?; hsimpl in *; *)
  (*                            doubt; *)
  (*                            apply PeanoNat.Nat.leb_le; lia. *)
  (*                      +++ *)
  (*                        destruct (measure_mq_fin (mon_handle e m0) MQ) eqn:?; attac. *)
  (*                        destruct ( measure_mq_fin (mon_handle e m0) (MQ ++ [MqProbe (m1, Q) m])) eqn:?; attac. *)
  (*                        destruct (measure_mq m1 {| origin := m1; lock_id := lock_count m0 |} (mon_handle e m0) MQ) eqn:?; attac. *)
  (*                        assert ( measure_mq m1 {| origin := m1; lock_id := lock_count m0 |} (mon_handle e m0) (MQ ++ [MqProbe (m1, Q) m]) = Some n2) *)
  (*                          by eauto using measure_mq_push. *)
  (*                          ltac1:(rewrite_strat (fix s := *)
  (*                                                  (subterms (try s); try (fold (_ + _))))). *)
  (*                          attac. *)
  (*                          replace (n0 + S n2) with (S (n0 + n2)) *)
  (*                            by eauto using PeanoNat.Nat.add_succ_r. *)
  (*                          destruct (S (n0 + n2) =? S (S (n0 + n2))) eqn:?; hsimpl in *. *)
  (*                          bs. *)
  (*                          rewrite PeanoNat.Nat.ltb_lt. *)
  (*                          ltac1:(rewrite_strat (fix s := *)
  (*                                                  (subterms (try s); try (fold (_ + _))))). *)
  (*                          replace (n0 + S n2) with (S (n0 + n2)) *)
  (*                            by eauto using PeanoNat.Nat.add_succ_r. *)
  (*                          attac. *)
  (*               ** rewrite `(NetMod.get m1 MN0 = _) in *. *)
  (*                  destruct MQ1; attac. *)
  (*                  --- destruct ( measure_mon m1 {| origin := m1; lock_id := lock_count M1 |} M1 ) eqn:?; attac. *)
  (*                      destruct b; attac. *)
  (*                      clear; *)
  (*                        destruct (n =? S n) eqn:?; hsimpl in *; *)
  (*                        doubt; *)
  (*                        apply PeanoNat.Nat.leb_le; lia. *)
  (*                  --- destruct ( measure_mon m1 {| origin := m1; lock_id := lock_count M1 |} M1 ) eqn:?; attac. *)
  (*                      destruct b; attac. *)
  (*                      clear; *)
  (*                        destruct (n =? S n) eqn:?; hsimpl in *; *)
  (*                        doubt; *)
  (*                        apply PeanoNat.Nat.leb_le; lia. *)
  (*                      destruct (measure_mq m1 {| origin := m1; lock_id := lock_count M1 |} (mon_handle e M1) MQ1); attac. *)

  (*                      ltac1:(rewrite_strat (fix s := *)
  (*                                              (subterms (try s); try (fold (_ + _))))). *)
  (*                      replace (n0 + S n2) with (S (n0 + n2)) *)
  (*                        by eauto using PeanoNat.Nat.add_succ_r. *)
  (*                      destruct (S (n0 + n2) =? S (S (n0 + n2))) eqn:?; hsimpl in *. *)
  (*                      bs. *)

  (*                      ltac1:(rewrite_strat (fix s := *)
  (*                                              (subterms (try s); try (fold (_ + _))))). *)
  (*                      rewrite PeanoNat.Nat.ltb_lt. *)
  (*                      lia. *)
  (*            ++ destruct (PeanoNat.Nat.eq_dec n0 n); subst. *)
  (*               1: { clear; *)
  (*                    destruct (n =? S n) eqn:?; hsimpl in *; *)
  (*                    doubt; *)
  (*                    apply PeanoNat.Nat.leb_le; lia. *)
  (*               } *)
  (*               smash_eq n1 m1; attac. *)
  (*               1: { *)
  (*                 rewrite `(NetMod.get n1 _ = _) in *. *)
  (*                 erewrite measure_mq_push in Heqo2; eauto. *)
  (*                 bs. *)
  (*               } *)
  (*               destruct s; simpl in *. *)
  (*               subst. *)
  (*               setoid_rewrite Heqo2 in Heqo3. *)
  (*               attac. *)
  (*            ++ smash_eq n1 m1; attac. *)
  (*               ** rewrite `(NetMod.get n1 _ = _) in *. *)

  (*                  (* destruct (measure_mon n1 {|origin:=n1; lock_id:=lock_count M1|} M1) eqn:?. *) *)
  (*                  (* hsimpl in *. *) *)
  (*                  (* destruct b; attac. *) *)

  (*                  clear - Heqo0 Heqo2 Heqo1 Heqb. *)
  (*                  generalize dependent M1 n. *)
  (*                  induction MQ; attac. *)
  (*                  --- generalize dependent n. *)
  (*                      induction M1; attac. *)
  (*                      +++ destruct state; simpl in *. *)
  (*                          destruct locked; attac. *)
  (*                          unfold probe_eqb in *. *)
  (*                          destruct m. *)
  (*                          unfold andb in *. *)
  (*                          blast_cases. *)
  (*                          all: simpl in *; hsimpl in *. *)
  (*                          all: doubt. *)
  (*                          destruct wait; simpl in *; doubt. *)
  (*                          unfold andb in *. *)
  (*                          blast_cases; attac. *)

  (*                        blast_cases; attac. *)
  (*                          simpl in *. *)
  (*                          unfold measure_ms_fin in *. *)
  (*                          hsimpl in *. *)
  (*                          unfold option_map in *. *)
  (*                          rewrite next_state_Send_all in *. *)
  (*                          simpl in *. *)
  (*                          remember ({| *)
  (*                                       self := &self; *)
  (*                                       lock_count := &lock_count; *)
  (*                                       locked := Some &t; *)
  (*                                       wait := &wait; *)
  (*                                       alarm := false *)
  (*                                     |}) as s. *)
  (*                          assert (self s = &self) by attac. *)
  (*                          assert (alarm s = false) by (subst; simpl; auto). *)
  (*                          assert (lock_count s = &lock_count) by (subst; simpl; auto). *)
  (*                          clear Heqs. *)
  (*                          remember true as b. *)
  (*                          clear Heqb. *)
  (*                          generalize dependent n2 b. *)
  (*                          induction wait; attac. *)
  (*                          unfold andb in *. *)
  (*                          destruct m; simpl in *. *)
  (*                          unfold probe_eqb in *. *)
  (*                          unfold andb in *. *)
  (*                          simpl in *. *)
  (*                          blast_cases; attac. *)

  (*                          assert (fst (measure_mon t {| origin := t; lock_id := lock_count |} *)
  (*                                    (Params.Transp.Mon.MonHandle.MSend_all wait R m *)
  (*                                       (Mon.P.MRecv *)
  (*                                          {| *)
  (*                                            self := self; *)
  (*                                            lock_count := lock_count; *)
  (*                                            locked := Some t; *)
  (*                                            wait := wait; *)
  (*                                            alarm := false *)
  (*                                          |}))) = n2). *)
  (*                          generalize dependent n2. *)
  (*                          induction wait; attac. *)
  (*                          unfold andb in *. *)
  (*                          destruct m; simpl in *. *)
  (*                          unfold probe_eqb in *. *)
  (*                          unfold andb in *. *)
  (*                          simpl in *. *)
  (*                          blast_cases; attac. *)

  (*                          eapply IH *)
  (*                          rewrite next_state_Send_all in *. *)
  (*                      eapply IHM1; attac. *)
  (*                  assert (self M1 = n1). *)
  (*                  { *)
  (*                    assert (self (MN0 n1) = n1) by attac. *)
  (*                    unfold NetGet in *. *)
  (*                    attac. *)
  (*                  } *)
  (*                  attac. *)
  (*                  clear - Heqo0 Heqb. *)
  (*                  exfalso. *)
  (*                  unfold measure_ms_fin in *. *)
  (*                  generalize dependent M1. *)
  (*                  induction MQ; attac. *)
  (*                  induction M1; attac. *)
  (*                  unfold option_map in *. *)
  (*                  destruct state; attac. *)
  (*                  blast_cases; attac. *)
  (*                  erewrite measure_mq_push *)
  (*                      in Heqo2; eauto. *)
  (*                 bs. *)
  (*               } *)
  (*               destruct s; simpl in *. *)
  (*               subst. *)
  (*               setoid_rewrite Heqo2 in Heqo3. *)
  (*               attac. *)


  (*       consider (_ =(_)=> _); compat_hsimpl in *; simpl in *. *)

  (*       smash_eq n n' m1; hsimpl in *. *)
  (*       all: try (rewrite `(NetMod.get n MN0 = _) in * ). *)
  (*       all: destruct v; compat_hsimpl in *. *)
  (*       all: simpl in *. *)
  (*       * exfalso. *)
  (*         destruct (MQ0 ++ [MqProbe (n, &t) m]) eqn:?; doubt. *)
  (*         unfold option_map in *. *)
  (*         destruct (measure_mon_fin M) eqn:?. *)
  (*         destruct (measure_mq_fin (mon_handle e m1) l) eqn:?; doubt. *)
  (*         hsimpl in *. *)
  (*         blast_cases; attac; *)
  (*           blast_cases; attac. *)

  (*     consider (exists n', lock MN0 n n') by (consider (lock_chain '' MN0 n L n); attac). *)
  (*      eapply measure_lock_chain_decr; eauto. *)
  (*      simpl; lia. *)

  (*     unfold NetGet in *. *)
  (*     destruct_mna a; consider (Flushing_NAct m1 _); consider (MN0 =(_)=> MN1). *)
  (*     all: compat_hsimpl in *; attac. *)
  (*     all: unfold measure_ms_fin in *; simpl in *. *)
  (*     all: rewrite `(NetMod.get m1 MN0 = _) in *. *)
  (*     all: simpl in *; hsimpl in *. *)
  (*     all: unfold option_map in *; blast_cases; attac. *)
  (*     all: unfold option_map in *; blast_cases; attac. *)
  (*     all: unfold dm_ltb, dm_leb; simpl. *)

  (*     all: try (Control.enter (fun () => match! goal with [|- (if ?x then _ else _) = _] => destruct $x eqn:? end)). *)
  (*     all: try (rewrite PeanoNat.Nat.eqb_eq in * ). *)
  (*     all: try (rewrite PeanoNat.Nat.eqb_neq in * ). *)
  (*     all: try (rewrite PeanoNat.Nat.leb_le in * ). *)
  (*     all: try (rewrite PeanoNat.Nat.ltb_lt in * ). *)
  (*     all: try (lia). *)

  (*     smash_eq n2 m1; attac; unfold option_map in *; blast_cases; attac. *)
  (*     ltac1:(rewrite_strat innermost progress fold (n3 + n) in Heqo0). *)
  (*     ltac1:(rewrite_strat innermost progress fold (n3 + n4) in Heqo0). *)
  (*     simpl in *. *)
  (*     assert (n = S n4). clear - Heqo0. induction n3; attac. *)
  (*     erewrite measure_mq_fin_push in Heqo; eauto. *)
  (*     attac. *)

  (*     smash_eq n2 m1; attac; unfold option_map in *; blast_cases; attac. *)
  (*     ltac1:(rewrite_strat innermost progress fold (_ + _) in Heqb0). *)
  (*     ltac1:(rewrite_strat innermost progress fold (n3 + n4) in Heqb0). *)
  (*     ltac1:(rewrite_strat innermost progress fold (_ + _)). *)
  (*     ltac1:(rewrite_strat innermost progress fold (n3 + n4)). *)
  (*     erewrite measure_mq_fin_push in Heqo; eauto. *)
  (*     attac. *)

  (*     smash_eq n2 m1; attac; unfold option_map in *; blast_cases; attac. *)
  (*     erewrite measure_mq_fin_push in Heqo; eauto. *)
  (*     attac. attac. *)

  (*     attac. *)
  (*     destruct s; attac. *)
  (*     setoid_rewrite Heqo2 in Heqo. attac. *)

  (*     smash_eq n2 m1; attac; unfold option_map in *; blast_cases; attac. *)
  (*     erewrite measure_mq_fin_push in Heqo; eauto. *)
  (*     attac. attac. *)

  (*     destruct s; attac. *)
  (*     erewrite measure_mq_fin_push in Heqo; eauto. *)
  (*     attac. *)

  (*     erewrite measure_mq_fin_push in Heqo; eauto. *)
  (*     attac. *)


  (*     attac. *)
  (*     attac. *)
  (*     ltac1:(rewrite_strat innermost progress fold (_ + _) in Heqb0). *)
  (*     ltac1:(rewrite_strat innermost progress fold (n3 + n4) in Heqb0). *)
  (*     ltac1:(rewrite_strat innermost progress fold (_ + _)). *)
  (*     ltac1:(rewrite_strat innermost progress fold (n3 + n4)). *)
  (*     erewrite measure_mq_fin_push in Heqo; eauto. *)
  (*     attac. *)
  (*     unfold lt. *)


  (*     ltac1:(rewrite_strat innermost progress fold (n3 + n4) in Heqo0). *)
  (*     simpl in *. *)
  (*     assert (n = S n4). clear - Heqo0. induction n3; attac. *)
  (*     erewrite measure_mq_fin_push in Heqo; eauto. *)
  (*     attac. *)


  (*   - consider (exists n', lock MN0 n n') by (consider (lock_chain '' MN0 n L n); attac). *)
  (*     eapply measure_lock_chain_decr; eauto. *)
  (*     simpl; lia. *)



  (* Lemma measure_lock_chain_split : forall MN n0 L n1 m0 m1 p, *)
  (*     measure_lock_chain MN n1 L1 n2 p = Some (m0, m1,. ) -> *)
  (*     measure_lock_chain MN n0 (L0 ++ (n1::L1)) n2 p <> None. *)


  (* Lemma measure_ac : forall (MN0 : MNet) (n : Name) (L : list Name), *)
  (*     (KIC MN0) -> *)
  (*     (lock_chain '' MN0 n L n) -> *)
  (*     alarm_condition n MN0 -> *)
  (*     measure_loop MN0 n L <> None. *)

  (* Proof. *)
  (*   intros. *)
  (*   kill H1. *)
  (*   - unfold measure_loop, NetGet, measure_ms_fin in *. *)
  (*     destruct (NetMod.get n MN0); simpl in *. *)
  (*     destruct (measure_mon_fin mserv_m0) eqn:?. *)
  (*     compat_hsimpl. *)
  (*     congruence. *)
  (*   - unfold measure_loop. *)
  (*     blast_cases; eattac. *)

  (*     smash_eq m n. *)
  (*     + destruct L; hsimpl in *. *)
  (*       * consider (m' = m) by (eapply SRPC_lock_set_uniq; eauto with LTS). *)
  (*         eattac. *)
  (*         blast_cases; eattac. *)
  (*         unfold measure_ms, NetGet in *; simpl in *. *)
  (*         destruct (NetMod.get m MN0) as [MQ0 M0 S0] eqn:?. *)
  (*         simpl in *. *)
  (*         apply measure_sp_true in H4; unfold measure_ms in *; simpl in *. *)
  (*         eattac. *)
  (*       * consider (m' = n) by (eapply SRPC_lock_set_uniq; eauto with LTS). *)
  (*         eattac. *)
  (*         blast_cases; eattac. *)
  (*         unfold measure_ms, NetGet in *; simpl in *. *)
  (*         destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?. *)
  (*         simpl in *. *)
  (*         apply measure_sp_true in H4; unfold measure_ms in *; simpl in *. *)
  (*         eattac. *)
  (*     + destruct `(_ \/ _); doubt. *)

  (*       assert (In m L \/ m = n) as [|]. *)
  (*       { *)
  (*         consider (exists L', lock_chain '' MN0 n L' m /\ ~ In m L') *)
  (*           by eauto using dep_lock_chain with LTS. *)
  (*         eapply lock_chain_loop_in; eauto with LTS; consider (KIC _); eapply SRPC_lock_set_uniq; eauto with LTS. *)
  (*       } *)
  (*       2: bs. *)

  (*       apply lock_chain_split_in with (n1:=m) in H0; eauto. *)
  (*       hsimpl in *. *)
  (*       apply measure_sp_true in H4. *)
  (*       destruct L1; hsimpl in *. *)
  (*       * consider (m' = n) by (eapply SRPC_lock_set_uniq; eauto with LTS). *)
  (*         eapply measure_lock_chain_tip. attac. *)
  (*       * consider (n0 = m') by (eapply SRPC_lock_set_uniq; eauto with LTS). *)
  (*         eapply measure_lock_chain_mid. attac. *)

  (*   - unfold measure_loop, measure_ms_fin, active_ev_of, active_probe_of in *. *)
  (*     apply in_split in H3 as (MQ & MQ' & ?). *)
  (*     rewrite H1. *)

  (*     assert (locked (MN0 n) = Some n') by attac. *)
  (*     assert (NoRecvR_from n' (mserv_q (MN0 n))) by eauto using lock_NoRecvR_from. *)
  (*     assert (no_sends_in n MN0) by eauto using lock_M_no_sends_in. *)
  (*     clear H0 H2. *)

  (*     assert (self (MN0 n) = n) by attac. *)
  (*     destruct (alarm (MN0 n)) eqn:?. *)
  (*     1: { compat_hsimpl; congruence. } *)

  (*     destruct (measure_mq_fin (MN0 n) *)
  (*                 (MQ ++ MqProbe (n', R) {| origin := n; lock_id := lock_count (MN0 n) |} :: MQ')) eqn:?. *)
  (*     1: eattac. *)
  (*     exfalso. *)
  (*     unfold no_sends_in in *. *)
  (*     apply measure_mq_fin_skip in Heqo. *)
  (*     unfold NetGet in *. *)
  (*     destruct (NetMod.get n MN0); simpl in *. *)
  (*     hsimpl in *. *)
  (*     clear - Heqo Heqb H3 H0 H4 H5. *)

  (*     clear Heqb. *)
  (*     generalize dependent mserv_m0. *)
  (*     induction MQ; attac. *)
  (*     + unfold option_map in *. *)
  (*       induction mserv_m0; attac. *)
  (*       * destruct state; attac. attac. *)
  (*       * compat_hsimpl in *. *)
  (*         destruct (measure_mon_fin mserv_m0) eqn:?. *)
  (*         destruct m; attac. *)
  (*         attac. *)
  (*     + unfold option_map in *. *)
  (*       destruct (measure_mon_fin mserv_m0) eqn:?. *)
  (*       destruct (alarm (mon_handle a m)) eqn:?; compat_hsimpl in *; doubt. *)
  (*       unfold option_map in *. *)
  (*       specialize (IHMQ (mon_handle a mserv_m0)). *)
  (*       replace (self (mon_handle a mserv_m0)) with (self mserv_m0) *)
  (*         by (clear; destruct a; simpl; blast_cases; attac; rewrite next_state_Send_all; attac). *)
  (*       replace (lock_count (mon_handle a mserv_m0)) with (lock_count mserv_m0) *)
  (*         by (clear - H5; destruct a; simpl; blast_cases; attac; rewrite next_state_Send_all; attac). *)
  (*       replace (locked (mon_handle a mserv_m0)) with (locked mserv_m0) *)
  (*         by (clear - H4 H3 H5; unfold NoRecvR_from in *; destruct a; simpl; blast_cases; attac; try (specialize H4 with v); try (rewrite next_state_Send_all); attac). *)

  (*       specialize (IHMQ ltac:(auto)). *)
  (*       specialize (IHMQ ltac:(auto) ltac:(auto)). *)

  (*       assert (NoRecvR_from n' *)
  (*                 (MQ ++ *)
  (*                    MqProbe (n', R) {| origin := self mserv_m0; lock_id := lock_count mserv_m0 |} :: MQ')). *)
  (*       { *)
  (*         unfold NoRecvR_from in *. *)
  (*         intros ? ?. *)
  (*         eapply H4 with (v:=v). *)
  (*         eattac. *)
  (*       } *)
  (*       specialize (IHMQ ltac:(auto)). *)
  (*       destruct (MQ ++ [MqProbe (n', R) {| origin := self mserv_m0; lock_id := lock_count mserv_m0 |}]) eqn:?; doubt. *)
  (*       setoid_rewrite Heql in Heqo. *)
  (*       setoid_rewrite Heql in IHMQ. *)
  (*       clear H4. *)
  (*       blast_cases; attac. *)
  (*       blast_cases; attac. *)
  (*       blast_cases; attac. *)
  (* Qed. *)


  (* Lemma measure_lock_chain_find : forall (MN0 : MNet) p (n0 n1 m : Name) (L : list Name), *)
  (*     snd (measure_lock_chain p MN0 L n0) = Some m -> *)
  (*     measure_ms n0 p (NetMod.get m MN0) = *)
  (*       ( ( dm_mon (fst (measure_lock_chain p MN0 L n0)), *)
  (*           dm_mque (fst (measure_lock_chain p MN0 L n0)) *)
  (*         ), *)
  (*         true *)
  (*       ). *)

  (* Proof. *)
  (*   intros. *)
  (*   induction L; intros; simpl in *. *)
  (*   - destruct (measure_ms n0 p (NetMod.get n0 MN0)) as [? [|]] eqn:?. *)
  (*     2: { destruct p0; bs. } *)

  (*     destruct p0. *)
  (*     attac. *)
  (*   - destruct (measure_ms n0 p (NetMod.get a MN0)) as [? [|]] eqn:?. *)
  (*     2: { destruct p0; attac. } *)

  (*     destruct p0. *)
  (*     attac. *)
  (* Qed. *)

  (* Lemma measure_mq_push : forall n p MQ0 e mq0, *)
  (*     (mq0, true) = measure_mq n p MQ0 -> *)
  (*     (mq0, true) = measure_mq n p (MQ0 ++ [e]). *)

  (* Proof. *)
  (*   induction MQ0. *)
  (*   1: { attac. } *)

  (*   intros. *)
  (*   specialize (IHMQ0 e). *)
  (*   hsimpl in *. *)
  (*   blast_cases; attac. *)
  (*   all: specialize (IHMQ0 _ eq_refl); attac. *)
  (* Qed. *)



  (* (** ********************** *) *)
  (* Inductive DetectMeasure := DM {dm_mon : nat; dm_mque : nat; dm_vis : nat}. *)

  (* Definition dm_leb (dm0 dm1 : DetectMeasure) : bool := *)
  (*   let c0 := dm_mon in *)
  (*   let c1 := dm_mque in *)
  (*   let c2 := dm_vis in *)
  (*   let next c f := *)
  (*     match (c dm0 =? c dm1) with *)
  (*     | true => f *)
  (*     | _ => (c dm0 <=? c dm1) *)
  (*     end *)
  (*   in next c2 (next c1 (next c0 true)). *)

  (* Definition dm_ltb (dm0 dm1 : DetectMeasure) : bool := *)
  (*   let c0 := dm_mon in *)
  (*   let c1 := dm_mque in *)
  (*   let c2 := dm_vis in *)
  (*   let next c f := *)
  (*     match (c dm0 =? c dm1) with *)
  (*     | true => f *)
  (*     | _ => (c dm0 <? c dm1) *)
  (*     end *)
  (*   in next c2 (next c1 (next c0 false)). *)

  (* Definition dm_eqb (dm0 dm1 : DetectMeasure) : bool := *)
  (*   match *)
  (*     (dm_mon dm0 =? dm_mon dm1)%nat, *)
  (*     (dm_mque dm0 =? dm_mque dm1)%nat, *)
  (*     (dm_vis dm0 =? dm_vis dm1)%nat with *)
  (*   | true, true, true => true *)
  (*   | _, _, _ => false *)
  (*   end. *)

  (* Fixpoint measure_mq nl p MQ0 : nat * bool := *)
  (*   match MQ0 with *)
  (*   | [] => (0, false) *)
  (*   | MqProbe (n, R) p' :: MQ0 => *)
  (*       if NAME.eqb (origin p) (origin p') *)
  (*          && (lock_id p =? lock_id p')%nat *)
  (*          && (NAME.eqb n nl) *)
  (*       then (1, true) *)
  (*       else *)
  (*         let (m, found) := measure_mq nl p MQ0 in *)
  (*         (S m, found) *)
  (*   | _ :: MQ0 => *)
  (*       let (m, found) := measure_mq nl p MQ0 *)
  (*       in (S m, found) *)
  (*   end. *)

  (* Fixpoint measure_init n_to MQ0 : nat * bool := *)
  (*   match MQ0 with *)
  (*   | [] => (0, false) *)
  (*   | MqRecv (n_from, Q) _ :: MQ0 => *)
  (*       if NAME.eqb n_from n_to *)
  (*       then (1, true) *)
  (*       else *)
  (*         let (m, found) := measure_init n_to MQ0 *)
  (*         in (S m, found) *)
  (*   | _::MQ0 => *)
  (*       let (m, found) := measure_init n_to MQ0 *)
  (*       in (S m, found) *)
  (*   end. *)

  (* Fixpoint measure_mon p M0 : (nat * bool) := *)
  (*   match M0 with *)
  (*   | MRecv _ => (0, false) *)
  (*   | MSend _ p' M0 => *)
  (*       if NAME.eqb (origin p) (origin p') *)
  (*          && (lock_id p =? lock_id p')%nat *)
  (*       then (1, true) *)
  (*       else *)
  (*         let (m, found) := measure_mon p M0 in *)
  (*         (S m, found) *)
  (*   end. *)

  (* Definition measure_ms p MS : ((nat * nat) * bool) := (* M MQ *) *)
  (*   let (mm, found_m) := measure_mon p (mserv_m MS) in *)
  (*   if found_m then ((mm, 0), true) *)
  (*   else *)
  (*     match locked MS with *)
  (*     | None => (0, 0, false) *)
  (*     | Some nl => *)
  (*         let (mq, found_q) := measure_mq nl p (mserv_q MS) in *)
  (*         ((mm, mq), found_q) *)
  (*     end. *)

  (* Definition measure_ms_init n_to (MS : MServ) : ((nat * nat) * bool) := (* M MQ *) *)
  (*   let (mm, found_m) := measure_mon {|origin:=self MS; lock_id:=lock_count MS|} (mserv_m MS) in *)
  (*   if found_m then ((mm, 0), true) *)
  (*   else *)
  (*     let (mq, found_q) := measure_init n_to (mserv_q MS) in *)
  (*     ((mm, mq), found_q). *)


  (* Fixpoint measure_lock_chain (p : MProbe) (MN : MNet) (n_prev : Name) (L : list Name) (n : Name) : (DetectMeasure * option Name) := *)
  (*   match L with *)
  (*   | [] => *)
  (*       match measure_ms_init n_prev (NetMod.get n MN) with *)
  (*         ((mm, mq), found) => *)
  (*           ({|dm_mon := mm; dm_mque := mq; dm_vis := 1|}, *)
  (*             if found then Some n else None *)
  (*           ) *)
  (*       end *)
  (*   | m::L => *)
  (*       match measure_ms p (NetMod.get m MN) with *)
  (*       | ((mm, mq), true) => *)
  (*           ({|dm_mon := mm; dm_mque := mq; dm_vis := 1|}, Some m) *)
  (*       | _ => *)
  (*           let (dm, found_name) := measure_lock_chain p MN m L n in *)
  (*           ({|dm_mon := dm_mon dm; dm_mque := dm_mque dm; dm_vis := S (dm_vis dm)|}, *)
  (*             found_name *)
  (*           ) *)
  (*       end *)
  (*   end. *)



  (* Definition measure_loop (MN : MNet) (L : list Name) (n : Name) : (DetectMeasure * option Name) := *)
  (*   if alarm (MN n) *)
  (*   then ({|dm_mon := 0; dm_mque := 0; dm_vis := 0|}, Some n) *)
  (*   else *)
  (*     match measure_mq n (active_probe_of MN n) (mserv_q (MN n)) with *)
  (*     | (mq, true) => *)
  (*         ({|dm_mon := ; dm_mque := mq; dm_vis := 0|}, Some n) *)
  (*     | _ => *)
  (*         measure_lock_chain (active_probe_of MN n) MN n L n *)
  (*     end. *)

  (* Lemma measure_loop_end : forall MN L n m, *)
  (*   measure_loop MN L n = ({|dm_mon := 0; dm_mque := 0; dm_vis := 0|}, Some m) -> *)
  (*   alarm (MN n) = true. *)

  (* Proof. *)
  (*   intros. *)
  (*   destruct (alarm (MN n)) eqn:?; auto. *)
  (*   exfalso. *)

  (*   unfold measure_loop, NetGet, measure_ms, active_probe_of in *. *)
  (*   rewrite Heqb in *. *)
  (*   blast_cases; attac. *)
  (*   destruct (NetMod.get m MN); attac. *)
  (*   attac. *)
  (* Qed. *)


  (* Lemma measure_sp_true : forall (n : Name) p MS, *)
  (*     sends_probe (n, R) p MS -> *)
  (*     snd (measure_ms p MS) = true. *)

  (* Proof. *)
  (*   intros. *)
  (*   unfold measure_ms. *)
  (*   induction H. *)
  (*   - blast_cases; attac. *)

  (*     (* destruct c; simpl in *; destruct alarm; doubt. *) *)
  (*     (* hsimpl in *. *) *)

  (*     generalize dependent n0 n2 n' p b0. *)
  (*     induction MQ; intros; attac. *)
  (*     + blast_cases; attac. *)
  (*       destruct b0; auto. *)
  (*       exfalso. *)
  (*       setoid_rewrite <- H2 in Heqb1. *)
  (*       setoid_rewrite <- H3 in Heqb1. *)
  (*       setoid_rewrite NAME_H.same_eqb_inv in Heqb1. *)
  (*       rewrite PeanoNat.Nat.eqb_refl in Heqb1. *)
  (*       bs. *)
  (*     + blast_cases; attac. *)
  (*       * eapply IHMQ; eauto. *)
  (*         unfold NoRecvR_from in *. *)
  (*         intros. *)
  (*         specialize (H v1). *)
  (*         attac. *)
  (*       * eapply IHMQ; eauto. *)
  (*         unfold NoRecvR_from in *. *)
  (*         intros. *)
  (*         specialize (H v1). *)
  (*         attac. *)
  (*       * eapply IHMQ; eauto. *)
  (*         unfold NoRecvR_from in *. *)
  (*         intros. *)
  (*         specialize (H v0). *)
  (*         attac. *)
  (*       * eapply IHMQ; eauto. *)
  (*         unfold NoRecvR_from in *. *)
  (*         intros. *)
  (*         specialize (H v0). *)
  (*         attac. *)
  (*   - blast_cases; attac. *)

  (*     destruct c; simpl in *; doubt. *)
  (*     hsimpl in *. *)

  (*     destruct b0; auto. *)
  (*     exfalso. *)

  (*     generalize dependent n0 n2 n' p. *)
  (*     induction MQ; intros; attac. *)
  (*     + blast_cases; attac. *)
  (*       rewrite PeanoNat.Nat.eqb_refl in Heqb0. *)
  (*       simpl in *. *)
  (*       bs. *)
  (*     + unfold NoRecvR_from in *; hsimpl in *. *)
  (*       blast_cases; attac. *)
  (*       * eapply IHMQ; eauto. *)
  (*         intros. *)
  (*         specialize (H v0). *)
  (*         attac. *)

  (*         destruct `(_ \/ _). attac. *)
  (*         specialize (H v0). *)
  (*         eattac. *)
  (*       * eapply IHMQ; eauto. *)
  (*         unfold NoRecvR_from in *. *)
  (*         intros. *)
  (*         specialize (H v). *)
  (*         attac. *)
  (*   - blast_cases; attac. *)
  (*     rewrite PeanoNat.Nat.eqb_refl in *. *)
  (*     bs. *)
  (*   - blast_cases; attac. *)
  (*     destruct p, p'. *)
  (*     simpl in *. *)
  (*     blast_cases; attac. *)
  (* Qed. *)


  (* Lemma measure_ac : forall (MN0 : MNet) (n : Name) (L : list Name), *)
  (*     (KIC MN0) -> *)
  (*     (lock_chain '' MN0 n L n) -> *)
  (*     alarm_condition n MN0 -> *)
  (*     exists m, snd (measure_loop MN0 L n) = Some m. *)

  (* Proof. *)
  (*   intros. *)
  (*   kill H1. *)
  (*   - exists n. *)
  (*     unfold measure_loop. *)
  (*     rewrite `(alarm _ = true); eauto. *)
  (*   - unfold measure_loop. *)
  (*     blast_cases; eattac. *)
  (*     blast_cases; eattac. *)
  (*     unfold measure_ms in *. *)
  (*     destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?. *)
  (*     simpl in *. *)
  (*     blast_cases; eattac. *)

  (*     destruct `(_ \/ _); subst. *)
  (*     + destruct L. *)
  (*       * hsimpl in *. *)
  (*         consider (m' = m) by (eapply SRPC_lock_set_uniq; eauto with LTS). *)
  (*         eattac. *)
  (*         blast_cases; eattac. *)
  (*         apply measure_sp_true in H4. *)
  (*         unfold measure_ms in *; simpl in *. *)
  (*         blast_cases; eattac. *)
  (*       * hsimpl in *. *)
  (*         consider (m' = n) by (eapply SRPC_lock_set_uniq; eauto with LTS). *)
  (*         eattac. *)
  (*         blast_cases; eattac. *)
  (*         apply measure_sp_true in H4. *)
  (*         unfold measure_ms in *; simpl in *. *)
  (*         blast_cases; eattac. *)
  (*     + apply measure_sp_true in H4; unfold measure_ms in *; simpl in *. *)
  (*       consider (exists L', lock_chain '' MN0 n L' m' /\ ~ In m' L') *)
  (*         by eauto using dep_lock_chain with LTS. *)

  (*       assert (In m' L \/ m' = n) as [|] by *)
  (*         (eapply lock_chain_loop_in; eauto with LTS; consider (KIC _); eapply SRPC_lock_set_uniq; eauto with LTS). *)
  (*       2: { eattac. } *)

  (*       apply (lock_chain_split_in `(In m' L)) in H0. *)
  (*       hsimpl in *. *)

  (*       clear H7 H3 H2 H1 H5 H6 L'. *)

  (*       generalize dependent n L1 m' d o n0 n1. *)
  (*       induction L0; intros; simpl in *. *)
  (*       * hsimpl in *. *)
  (*         unfold measure_ms in *. *)
  (*         blast_cases; eattac. *)
  (*       * blast_cases; eattac. *)
  (*         -- eapply IHL0 in Heqp4; eauto. *)
  (*            blast_cases; eattac. *)
  (*         -- eapply IHL0 in Heqp4; eauto. *)
  (*            blast_cases; eattac. *)
  (*   - unfold active_ev_of, NetGet in *. *)
  (*     destruct (NetMod.get n MN0) eqn:?. *)
  (*     simpl in *. *)
  (*     exists n. *)
  (*     unfold measure_loop, measure_ms in *. *)
  (*     destruct (alarm (MN0 n)); eauto. *)
  (*     hsimpl in *. subst. *)
  (*     destruct b; auto. *)

  (*     unfold active_probe_of, NetGet, measure_ms in *. *)
  (*     rewrite `(NetMod.get _ _ = _) in *; simpl in *. *)
  (*     clear - Heqp H3. *)
  (*     exfalso. *)
  (*     generalize dependent n0 n1. *)
  (*     induction mserv_m0; intros; eattac. *)
  (*     + generalize dependent n0 n1. *)
  (*       induction mserv_q0; eattac. *)
  (*       destruct a; attac. *)
  (*       * eapply IHmserv_q0. eauto. *)
  (*         rewrite <- Heqp. *)
  (*         blast_cases; attac. *)
  (*       * eapply IHmserv_q0. eauto. *)
  (*         rewrite <- Heqp. *)
  (*         blast_cases; attac. *)
  (*       * kill H3; attac. *)
  (*         -- blast_cases; attac. *)
  (*            bs (&lock_count <> &lock_count) by (eapply PeanoNat.Nat.eqb_neq; eauto). *)
  (*         -- eapply IHmserv_q0. eauto. *)
  (*            rewrite <- Heqp. *)
  (*            blast_cases; attac. *)
  (*     + blast_cases; attac. *)
  (* Qed. *)


  (* Lemma measure_lock_chain_find : forall (MN0 : MNet) p (n0 n1 m : Name) (L : list Name), *)
  (*     snd (measure_lock_chain p MN0 L n0) = Some m -> *)
  (*     measure_ms n0 p (NetMod.get m MN0) = *)
  (*       ( ( dm_mon (fst (measure_lock_chain p MN0 L n0)), *)
  (*           dm_mque (fst (measure_lock_chain p MN0 L n0)) *)
  (*         ), *)
  (*         true *)
  (*       ). *)

  (* Proof. *)
  (*   intros. *)
  (*   induction L; intros; simpl in *. *)
  (*   - destruct (measure_ms n0 p (NetMod.get n0 MN0)) as [? [|]] eqn:?. *)
  (*     2: { destruct p0; bs. } *)

  (*     destruct p0. *)
  (*     attac. *)
  (*   - destruct (measure_ms n0 p (NetMod.get a MN0)) as [? [|]] eqn:?. *)
  (*     2: { destruct p0; attac. } *)

  (*     destruct p0. *)
  (*     attac. *)
  (* Qed. *)

  (* Lemma measure_mq_push : forall n p MQ0 e mq0, *)
  (*     (mq0, true) = measure_mq n p MQ0 -> *)
  (*     (mq0, true) = measure_mq n p (MQ0 ++ [e]). *)

  (* Proof. *)
  (*   induction MQ0. *)
  (*   1: { attac. } *)

  (*   intros. *)
  (*   specialize (IHMQ0 e). *)
  (*   hsimpl in *. *)
  (*   blast_cases; attac. *)
  (*   all: specialize (IHMQ0 _ eq_refl); attac. *)
  (* Qed. *)
