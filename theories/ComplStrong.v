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
    in next c0 (next c1 (next c2 true)).

  Definition dm_ltp (dm0 dm1 : DetectMeasure) : bool :=
    let c0 := dm_mon in
    let c1 := dm_mque in
    let c2 := dm_vis in
    let next c f :=
      match (c dm0 =? c dm1) with
      | true => f
      | _ => (c dm0 <? c dm1)
      end
    in next c0 (next c1 (next c2 false)).

  Definition dm_eqb (dm0 dm1 : DetectMeasure) : bool :=
    match
      (dm_mon dm0 =? dm_mon dm1)%nat,
      (dm_mque dm0 =? dm_mque dm1)%nat,
      (dm_vis dm0 =? dm_vis dm1)%nat with
    | true, true, true => true
    | _, _, _ => false
    end.

  Fixpoint measure_mq n p MQ0 : nat * bool :=
    match MQ0 with
    | [] => (0, false)
    | MqProbe _ p' :: MQ0 =>
        if NAME.eqb (origin p) (origin p')
           && (lock_id p =? lock_id p')%nat
        then (1, true)
        else
          let (m, found) := measure_mq n p MQ0
          in (S m, found)
    | MqRecv (_, Q) _ :: MQ0 =>
        if NAME.eqb (origin p) n
        then (1, true)
        else
          let (m, found) := measure_mq n p MQ0
          in (S m, found)
    | _::MQ0 =>
        let (m, found) := measure_mq n p MQ0
        in (S m, found)
    end.

  Fixpoint measure_mon p M0 : (nat * bool) :=
    match M0 with
    | MRecv {|alarm:=true|} => (0, true)
    | MRecv _ => (0, false)
    | MSend _ p' M0 =>
        if NAME.eqb (origin p) (origin p')
           && (lock_id p =? lock_id p')%nat
        then (1, true)
        else
          let (m, found) := measure_mon p M0 in
          (S m, found)
    end.

  Definition measure_ms n p MS : ((nat * nat) * bool) := (* M MQ *)
    let (mm, found_m) := measure_mon p (mserv_m MS) in
    if found_m then ((mm, 0), true)
    else
      let (mq, found_q) := measure_mq n p (mserv_q MS) in
      ((mm, mq), found_q).

  Fixpoint measure_lock_chain (p : MProbe) (MN : MNet) (L : list Name) (n : Name) : (DetectMeasure * option Name) :=
    match L with
    | [] =>
        match measure_ms n p (NetMod.get n MN) with
          ((mm, mq), found) =>
            ({|dm_mon := mm; dm_mque := mq; dm_vis := 1|},
              if found then Some n else None
            )
        end
    | m::L =>
        match measure_ms n p (NetMod.get m MN) with
        | ((mm, mq), true) =>
            ({|dm_mon := mm; dm_mque := mq; dm_vis := 1|}, Some m)
        | _ =>
            let (dm, found_name) := measure_lock_chain p MN L n in
            ({|dm_mon := dm_mon dm; dm_mque := dm_mque dm; dm_vis := S (dm_vis dm)|},
              found_name
            )
        end
    end.

  (* Definition measure_loop (MN : MNet) (L : list Name) (n : Name) : (DetectMeasure * option Name) := *)
  (*   measure_lock_chain (active_probe_of MN n) MN (n::L) n. *)

  (* Lemma measure_loop_alarm : forall (MN : MNet) (L : list Name) (n : Name), *)
  (*     alarm (MN n) = true -> *)
  (*     measure_loop MN L n = ({|dm_mon := 0; dm_mque := 0; dm_vis := 0|}, Some n). *)

  (* Proof. *)
  (*   intros. *)
  (*   unfold measure_loop, NetGet; simpl in *. *)
  (*   destruct (NetMod.get n MN). *)
  (* Admitted. *)


  Definition measure_loop (MN : MNet) (L : list Name) (n : Name) : (DetectMeasure * option Name) :=
    match (alarm (MN n)) with
    | true => ({|dm_mon := 0; dm_mque := 0; dm_vis := 0|}, Some n)
    | false => measure_lock_chain (active_probe_of MN n) MN (n::L) n
    end.


  Lemma measure_loop_end : forall MN L n m,
    measure_loop MN L n = ({|dm_mon := 0; dm_mque := 0; dm_vis := 0|}, Some m) ->
    alarm (MN n) = true.

  Proof.
    intros.
    destruct (alarm (MN n)) eqn:?; auto.
    exfalso.

    unfold measure_loop in *.
    rewrite Heqb in *.
    unfold measure_lock_chain in *.
    blast_cases; doubt.
  Qed.

  Ltac2 Notation "destruct_mna" a(constr) :=
    destruct $a as [? [[[? [|]]|[? [|]]|]|[[? ?]|[? ?]|]|[[? ?]|[? ?]|]] | ? ? [|] [?|?]]; doubt.


  Lemma measure_sp_true : forall (n : Name) p MS,
      sends_probe (n, R) p MS ->
      snd (measure_ms (origin p) p MS) = true.

  Proof.
    intros.
    unfold measure_ms.
    induction H.
    - blast_cases; attac.

      destruct c; simpl in *; destruct alarm; doubt.
      hsimpl in *.

      generalize dependent n0 n2 n' p b0.
      induction MQ; intros; attac.
      + blast_cases; attac.
      + blast_cases; attac.
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
    - blast_cases; attac.
      destruct c; simpl in *; destruct alarm; doubt.
      hsimpl in *.

      generalize dependent n0 n2 n' p b0.
      induction MQ; intros; attac.
      + blast_cases; attac.
        apply PeanoNat.Nat.eqb_neq in Heqb1; bs.
      + blast_cases; attac.
        * eapply IHMQ; eauto.
          unfold NoRecvR_from in *.
          intros.
          specialize (H v0).
          attac.
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
             apply PeanoNat.Nat.eqb_neq in Heqb0.
             bs.
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

  Lemma measure_ms_tau_non_incr : forall n p MS0 MS1 a mm0 mm1 mq0 mq1,
      ia a ->
      (MS0 =(a)=> MS1) ->
      (mm0, mq0, true) = measure_ms n p MS1 ->
      (mm1, mq1, true) = measure_ms n p MS0 ->
      if mm0 =? mm1 then mq0 <=? mq1  = true else mm0 <=? mm1 = true.

  Proof.
    intros.
    destruct_ma a; doubt; consider (_ =(_)=> _).
    - unfold measure_ms in *; compat_hsimpl in *.

      generalize dependent mm1 mq1 mm0 mq0.
      induction MQ; attac.
      + 
        generalize dependent mm1 mq1 mm0 mq0.
        induction M; attac.
        eapply IHM.

      induction M; attac.
      + generalize dependent mm1 mq1 mm0 mq0.
        induction MQ; attac.
        destruct a; eattac.
        * eapply IHMQ; eauto.



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
