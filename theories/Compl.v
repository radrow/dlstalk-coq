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
Require Import DlStalk.ModelData.
Require Import DlStalk.Que.
Require Import DlStalk.Model.
Require Import DlStalk.Network.
Require Import DlStalk.Locks.
Require Import DlStalk.NetLocks.
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

Record MProbe' {n : Set} : Set := {init : n; index : nat}.

Record MState' {n : Set} : Set :=
  { self : n
  ; lock_id : nat
  ; lock : option n
  ; waitees : list n
  ; alarm : bool
  }.


Module Type DETECT_CONF.
  Include SRPC_NET_CONF.
  Include MON_CONF with Definition Msg := @MProbe' NAME.t'
            with Definition MState := @MState' NAME.t'.
End DETECT_CONF.


Module Type DETECT_PARAMS(Conf : DETECT_CONF).
  Declare Module Locks : LOCKS(Conf).
  Declare Module NetLocks : NET_LOCKS(Conf) with Module Locks := Locks.
  Declare Module Mon : MON(Conf) with Module Proc := Locks.Proc.
  Declare Module Export Transp : TRANSP(Conf)
  with Module Mon := Mon
  with Module Net := NetLocks.Net.
  Declare Module Export Srpc : SRPC(Conf)
  with Module Locks := Locks.
  Declare Module Export SrpcNet : SRPC_NET(Conf)
  with Module Srpc := Srpc
  with Module NetLocks := NetLocks.
End DETECT_PARAMS.

Module Type COMPL_F(Import Conf : DETECT_CONF)(Import Params : DETECT_PARAMS(Conf)).

  Include NetLocks.LOCKS_UNIQ.
  Import SrpcDefs.

  Notation MProbe := (@MProbe' Name).

  Module ThomasNet.
    Parameter nat_Name : nat -> Name.
    Parameter Name_nat : Name -> nat.
    Axiom nat_Name_bij : forall n, nat_Name (Name_nat n) = n.
    Axiom Name_nat_bij : forall n, Name_nat (nat_Name n) = n.

    CoInductive Mover (N : PNet) : Name -> Prop :=
    | mover_ [n0 n1] : Mover N n0 -> net_lock_on N n0 n1 -> Mover N n1.

    CoFixpoint Echo : Proc :=
      PRecv (
          fun m =>
            let (c, t) := m in
            match t with
            | R => None
            | Q => Some (fun v => PSend (c, R) v Echo)
            end
        ).

    Definition MoverFinger (self : Name) : Proc :=
      PRecv (
          fun m =>
            let (s, t) := m in
            match t with
            | Q => None
            | R => if S (Name_nat s) =? Name_nat self
                  then Some (fun v => PSend (nat_Name (S (Name_nat self)), R) v Echo)
                  else None
            end
        ).

    Definition MoverNail : Proc :=
      PSend (nat_Name 0, Q) some_val (MoverFinger (nat_Name 1)).


    Lemma Decisive_Echo : Decisive Echo.
      ltac1:(cofix C).
      unfold Echo.
      rewrite unfold_Proc.
      apply DecRecv; intros.
      - kill H.
        split; auto.
        intros.
        constructor.
        Guarded.
        assumption.
      - split; try (bullshit).
    Qed.

    Lemma SRPC_Echo : SRPC Free Echo.
      ltac1:(cofix C).
      unfold Echo in *.
      rewrite unfold_Proc.
      constructor; intros.
      - eexists.
        attac.
      - kill H.
        destruct n as [c [|]]; doubt.
        exists c, v.
        split; auto.
        hsimpl in *.
        constructor; intros; auto; doubt.
        + constructor; bullshit.
        + kill H.
          apply C.
    Qed.

    Lemma SRPC_Finger : forall n, SRPC (Lock (nat_Name (S (S n))) (nat_Name n)) (MoverFinger (nat_Name (S n))).
      intros.
      constructor; intros; doubt.
      - constructor; intros; doubt.
        + eexists; econstructor.
          rewrite Name_nat_bij in *.
          rewrite Name_nat_bij in *.
          rewrite PeanoNat.Nat.eqb_refl.
          attac.
        + kill H.
          exists v.
          destruct n0, t; doubt.
          rewrite Name_nat_bij in *.
          destruct (Name_nat n0 =? n) eqn:?; doubt.
          rewrite PeanoNat.Nat.eqb_eq in Heqb; attac.
          now rewrite nat_Name_bij in *.
        + kill H.
          destruct n0, t; doubt.
          rewrite Name_nat_bij in *.
          destruct (Name_nat n0 =? n) eqn:?; doubt.
          hsimpl in *.
          constructor; intros; doubt.
      - unfold MoverFinger in H.
        kill H.
        rewrite Name_nat_bij in *.
        destruct (Name_nat s =? n) eqn:?; doubt.
        rewrite PeanoNat.Nat.eqb_eq in Heqb.
        hsimpl in *.
        constructor; intros; doubt.
        1: constructor; intros; doubt; auto.
        kill H.
        apply SRPC_Echo.
    Qed.


    Lemma SRPC_Nail : SRPC (Work (nat_Name 2)) MoverNail.
      constructor; intros; doubt.
      - assert (SRPC (Lock (nat_Name 2) (nat_Name 0)) (MoverFinger (nat_Name 1)))
          by apply SRPC_Finger.

        constructor; intros; doubt.
        kill H; attac.
      - kill H; attac.
        apply SRPC_Finger.
    Qed.

    Lemma SRPC_sane_Echo : SRPC_sane Free (pq [] Echo []).
      constructor; intros; doubt.
      eauto using SRPC_Echo with LTS.
    Qed.

    Lemma SRPC_sane_Finger : forall n, SRPC_sane (Lock (nat_Name (S (S n))) (nat_Name n)) (pq [] (MoverFinger (nat_Name (S n))) []).
      intros.
      constructor; intros; doubt.
      eauto using SRPC_Finger with LTS.
    Qed.

    Lemma SRPC_sane_Nail : SRPC_sane (Work (nat_Name 2)) (pq [] MoverNail []).
      constructor; intros; doubt.
      eauto using SRPC_Nail with LTS.
    Qed.

    Example t_Net : {N : PNet | Mover N (nat_Name 1) /\ net_sane N}.
    pose (N := NetMod.init
                 (
                   fun n => (pq [] (
                                 match Name_nat n with
                                 | 0 => Echo
                                 | S 0 => MoverNail
                                 | n' => MoverFinger (nat_Name n')
                                 end
                               ) [])
         )).
    exists N.

    assert (forall n, Decisive_q (NetMod.get n N)) as HD.
    {
      clear C.
      intros.
      subst N.
      rewrite NetMod.init_get.
      simpl.

      destruct (Name_nat n) eqn:?.
      - apply Decisive_Echo.
      - destruct n0; unfold MoverNail, MoverFinger.
        + constructor.
          constructor; attac.
          rewrite Name_nat_bij in *.
          destruct (Name_nat n0 =? 0); doubt.
          hsimpl in *.
          constructor.
          apply Decisive_Echo.
        + constructor; split; intros; auto; doubt.
          rewrite Name_nat_bij in *.
          destruct (S (Name_nat n1) =? S (S n0)); doubt.
          hsimpl in *.
          constructor.
          apply Decisive_Echo.
    }

    split.
    - enough (forall n, n <> 0 -> Mover N (nat_Name n)) by auto.
      ltac1:(cofix C).

      subst N.
      intros.
      constructor 1 with (n0:=(nat_Name (S n)))(n1:=(nat_Name n)); auto; doubt.
      unfold net_lock_on, net_lock.
      exists [nat_Name n].
      split. 1: attac.
      rewrite NetMod.init_get.

      constructor.
      + rewrite Name_nat_bij.
        destruct n; doubt.
        clear C H.
        revert n.
        ltac1:(cofix C).
        intros.
        specialize (HD (nat_Name (S (S n)))).
        rewrite NetMod.init_get in HD.
        rewrite Name_nat_bij in HD.
        constructor; split; intros; auto; doubt.
        rewrite Name_nat_bij in *.
        destruct (S (Name_nat n0) =? S (S n)) eqn:?; doubt.
        unfold MoverFinger in *.
        simpl in *.
        kill HD.
        rewrite Name_nat_bij in *.
        specialize (HDecR n0 P).
        rewrite Heqb in HDecR.
        specialize (HDecR H).
        attac.
      + rewrite Name_nat_bij.
        destruct n; doubt.
        constructor; auto.
        split; intros.
        * rewrite Name_nat_bij.
          kill H0.
          rewrite Name_nat_bij.
          rewrite PeanoNat.Nat.eqb_refl.
          attac.
        * rewrite Name_nat_bij in *.
          destruct (S (Name_nat n0) =? S (S n)) eqn:?; doubt.
          apply PeanoNat.Nat.eqb_eq in Heqb.
          hsimpl in * |-.
          constructor.
          rewrite <- Heqb.
          now rewrite nat_Name_bij.
      + bullshit.
    - assert (forall n, n <> 0 -> net_lock_on N (nat_Name (S n)) (nat_Name n)) as HL.
      {
        intros.
        exists [nat_Name n]; split; attac.
        unfold net_lock.
        destruct n; doubt. clear H.
        specialize (HD (nat_Name (S (S n)))).
        subst N.
        rewrite NetMod.init_get in *.
        rewrite Name_nat_bij in *.
        simpl in HD.
        constructor; auto.
        clear HD.
        constructor; split; intros; rewrite Name_nat_bij in *.
        - kill H.
          rewrite Name_nat_bij in *.
          rewrite PeanoNat.Nat.eqb_refl.
          attac.
        - destruct (S (Name_nat n0) =? S (S n)) eqn:?; doubt.
          apply PeanoNat.Nat.eqb_eq in Heqb.
          kill Heqb.
          rewrite nat_Name_bij. attac.
      }

      assert (forall n, n <> 0 -> pq_client (nat_Name (S n)) (NetMod.get (nat_Name n) N)) as HC.
      {
        intros.
        clear HL HD.
        subst N.
        rewrite NetMod.init_get.
        rewrite Name_nat_bij.
        destruct n; doubt. clear H.
        constructor 2.
        destruct n.
        - econstructor 1. apply SRPC_Nail.
        - econstructor 1. apply SRPC_Finger.
      }

      assert (forall n0 n1, net_lock_on N n1 n0 -> S (Name_nat n0) = (Name_nat n1) /\ Name_nat n0 <> 0) as HL'.
      {
        intros.
        subst N.
        unfold net_lock_on, net_lock in H.
        hsimpl in *.
        rewrite NetMod.init_get in *.
        kill H0.
        assert (AnySRPC (match Name_nat n1 with
                         | 0 => Echo
                         | 1 => MoverNail
                         | S (S n1) => MoverFinger (nat_Name (S (S n1)))
                         end)).
        {
          destruct (Name_nat n1).
          eexists; eauto using SRPC_Echo.
          destruct n; eexists; eauto using SRPC_Finger, SRPC_Nail.
        }
        assert (proc_lock [n0] (match Name_nat n1 with
                                | 0 => Echo
                                | 1 => MoverNail
                                | S (S n1) => MoverFinger (nat_Name (S (S n1)))
                                end)).
        {
          edestruct (SRPC_get_lock).
          apply H0.
          apply H2.
          enough (n0 = x) by (subst; auto).
          enough (List.In n0 [x]) by attac.
          apply (proc_lock_incl `(proc_lock L _)); auto.
        }
        destruct (Name_nat n1) eqn:?.
        - eapply lock_SRPC_Lock in H0.
          + hsimpl in *.
            absurd (Lock c n0 = Free); attac.
            eapply SRPC_inv; eauto using SRPC_Echo.
          + auto.
        - clear H2 H3.
          eapply lock_SRPC_Lock in H4. 2: auto.
          hsimpl in *.
          destruct n.
          + absurd (Lock c n0 = Work (nat_Name 2)); doubt.
          + assert (Lock c n0 = Lock (nat_Name (S (S (S n)))) (nat_Name (S n))); doubt.
            eapply SRPC_inv; eauto using SRPC_Finger.
            hsimpl in *.
            rewrite Name_nat_bij.
            attac.
      }

      assert (forall n0 n1, pq_client n1 (NetMod.get n0 N) -> S (Name_nat n0) = (Name_nat n1) /\ Name_nat n0 <> 0) as HC'.
      {
        intros.
        subst N.
        rewrite NetMod.init_get in *.
        kill H.
        kill H0; doubt.
        destruct (Name_nat n0) eqn:?; doubt.
        - absurd (Busy x = Free); attac.
          eapply SRPC_inv; eauto using SRPC_Echo.
        - destruct n.
          + split; attac.

            assert (SRPC (Work (nat_Name (2))) MoverNail) by auto using SRPC_Nail.
            apply (SRPC_inv H0) in H.
            hsimpl in *.
            now rewrite Name_nat_bij.
          + split; attac.
            assert (SRPC (Lock (nat_Name (S (S (S n)))) (nat_Name (S n))) (MoverFinger (nat_Name (S (S n))))) by auto using SRPC_Finger.
            apply (SRPC_inv H0) in H.
            hsimpl in *.
            now rewrite Name_nat_bij.
      }

      constructor.
      + intros n.
        subst N.
        rewrite NetMod.init_get.
        destruct (Name_nat n) eqn:?.
        * eexists; eapply SRPC_sane_Echo.
        * destruct n0 eqn:?.
          -- eexists; eapply SRPC_sane_Nail.
          -- eexists; eapply SRPC_sane_Finger.
      + intros n0 n1 HL0.
        apply HL' in HL0.
        hsimpl in *.
        specialize (HC (Name_nat n1) ltac:(auto)).
        rewrite <- HL0 in *.
        rewrite nat_Name_bij in *.
        rewrite nat_Name_bij in *.
        auto.
      + intros n0 n1 HC0.
        apply HC' in HC0.
        hsimpl in *.
        specialize (HL (Name_nat n1) ltac:(auto)).
        rewrite <- HC0 in *.
        rewrite nat_Name_bij in *.
        rewrite nat_Name_bij in *.
        auto.
    Qed.

  End ThomasNet.


  Definition _of [A] (f : MState -> A) (N : MNet) (n : Name) : A :=
    f (next_state (get_Mc N n)).

  #[export] Hint Unfold _of : LTS_get.
  #[export] Hint Transparent _of : LTS.


  Notation "'' MN" := (net_deinstr MN) (at level 1).

  Notation NoRecvQ_MQ := (Forall (fun e => match e with TrRecv (_, Q) _ => False | _ => True end)).
  Notation NoRecvR_MQ := (Forall (fun e => match e with TrRecv (_, R) _ => False | _ => True end)).

  Lemma Clear_NoRecvQ_MQ : forall MQ, MQ_Clear MQ -> NoRecvQ_MQ MQ.
  Proof. induction MQ; attac. Qed.
  Lemma Clear_NoRecvR_MQ : forall MQ, MQ_Clear MQ -> NoRecvR_MQ MQ.
  Proof. induction MQ; attac. Qed.

  #[export] Hint Immediate Clear_NoRecvQ_MQ Clear_NoRecvR_MQ : LTS.

  Definition NoRecvQ_from n MQ := forall v, ~ List.In (TrRecv (n, Q) v) MQ.

  Lemma NoRecvQ_MQ_from [MQ] v : NoRecvQ_MQ MQ -> NoRecvQ_from v MQ.
  Proof. unfold NoRecvQ_from in *. intros. intros ?. induction MQ; kill H0; attac. Qed.


  Definition NoRecvR_from n MQ := forall v, ~ List.In (TrRecv (n, R) v) MQ.

  Lemma NoRecvR_MQ_from [MQ] v : NoRecvR_MQ MQ -> NoRecvR_from v MQ.
  Proof. unfold NoRecvR_from in *. intros. intros ?. induction MQ; kill H0; attac. Qed.

  #[export] Hint Resolve NoRecvQ_MQ_from NoRecvR_MQ_from : LTS.


  Lemma pq_TrRecvQ_pop [MQ0 M0 S0 MQ1 M1 S1 a n] :
    (mq MQ0 M0 S0 =(a)=> mq MQ1 M1 S1) ->
    ~ NoRecvQ_from n MQ0 ->
    NoRecvQ_from n MQ1 ->
    exists v, a = MActP (Recv (n, Q) v).

  Proof.
    unfold NoRecvQ_from.
    intros.
    kill H; eattac.
    - exfalso.
      apply H0.
      intros ? ?.
      specialize (H1 v0).
      bullshit.
    - exfalso.
      apply H0.
      intros ? ?.
      specialize (H1 v0).
      bullshit.
    - destruct n0.
      destruct t.
      + exists v.
        enough (n = n0) by attac.
        smash_eq n n0.
        bullshit.
      + bullshit.
    - exfalso.
      apply H0.
      intros ? ?.
      specialize (H1 v0).
      bullshit.
  Qed.


  Lemma NoRecvQ_from_dec n0 MQ0 :
    NoRecvQ_from n0 MQ0 \/ ~ NoRecvQ_from n0 MQ0.

  Proof.
    unfold NoRecvQ_from.
    induction MQ0; attac.
    destruct IHMQ0.
    - destruct a.
      + left; attac.
      + destruct n.
        smash_eq n0 n; destruct t; attac.
        right. attac.
        specialize (H0 v).
        attac.
      + left; attac.
    - right.
      intros ?.
      apply H.
      attac.
      specialize (H0 v).
      attac.
  Qed.


  Lemma NoRecvR_from_dec n0 MQ0 :
    NoRecvR_from n0 MQ0 \/ ~ NoRecvR_from n0 MQ0.

  Proof.
    unfold NoRecvR_from.
    induction MQ0; attac.
    destruct IHMQ0.
    - destruct a.
      + left; attac.
      + destruct n.
        smash_eq n0 n; destruct t; attac.
        right. attac.
        specialize (H0 v).
        attac.
      + left; attac.
    - right.
      intros ?.
      apply H.
      attac.
      specialize (H0 v).
      attac.
  Qed.


  Lemma NoRecvQ_dec MQ :
    NoRecvQ_MQ MQ \/ ~ NoRecvQ_MQ MQ.

  Proof.
    induction MQ; attac.
    destruct IHMQ.
    - destruct a.
      + left; attac.
      + destruct n, t; eattac.
      + left; attac.
    - right.
      intros ?; attac.
  Qed.


  Lemma NoRecvR_dec MQ :
    NoRecvR_MQ MQ \/ ~ NoRecvR_MQ MQ.

  Proof.
    induction MQ; attac.
    destruct IHMQ.
    - destruct a.
      + left; attac.
      + destruct n, t; eattac.
      + left; attac.
    - right.
      intros ?; attac.
  Qed.


  Lemma NoSends_dec MQ :
    NoSends_MQ MQ \/ ~ NoSends_MQ MQ.

  Proof.
    induction MQ; attac.
    destruct IHMQ.
    - destruct a.
      + right; intros ?; attac.
      + left; attac.
      + left; attac.
    - right.
      intros ?; attac.
  Qed.


  Lemma flushed_in_NoRecvQ_MQ : forall MN n, flushed_in n MN -> NoRecvQ_MQ (get_MQ MN n).
  Proof. unfold flushed_in, get_MQ. intros. destruct (NetMod.get n MN); attac. Qed.
  Lemma flushed_in_NoRecvR_MQ : forall MN n, flushed_in n MN -> NoRecvR_MQ (get_MQ MN n).
  Proof. unfold flushed_in, get_MQ. intros. destruct (NetMod.get n MN); attac. Qed.

  #[export] Hint Immediate flushed_in_NoRecvQ_MQ flushed_in_NoRecvR_MQ : LTS.

  Lemma flushed_NoRecvQ_from [MN n] v : flushed_in n MN -> NoRecvQ_MQ (get_MQ MN n) -> NoRecvQ_from v (get_MQ MN n).
  Proof.
    unfold NoRecvQ_from in *. intros. intros ?.
    ltac1:(autounfold with LTS_get in * ). destruct (NetMod.get n MN).
    induction l; kill H0; attac.
  Qed.

  #[export] Hint Resolve flushed_NoRecvQ_from : LTS.


  Lemma net_vis_TrRecvQ_pop [MN0 MN1 a n m n'] :
    (MN0 ~(n' @ a)~> MN1) ->
    ~ NoRecvQ_from n (get_MQ MN0 m) ->
    NoRecvQ_from n (get_MQ MN1 m) ->
    exists v, a = MActP (Recv (n, Q) v) /\ n' = m.

  Proof.
    intros.
    smash_eq m n'.
    - ltac1:(autounfold with LTS_get in * ). hsimpl in *. hsimpl in *.
      destruct (NetMod.get m MN0).
      destruct S.
      assert (exists v, a = MActP (Recv (n, Q) v)) by eauto using pq_TrRecvQ_pop.
      hsimpl in *.
      exists v; auto.
    - ltac1:(autounfold with LTS_get in * ).
      assert (NetMod.get m MN1 = NetMod.get m MN0) by eauto using NV_stay, eq_sym with LTS.
      rewrite `(NetMod.get m MN1 = _) in *.
      bullshit.
  Qed.


  Lemma net_TrRecvQ_pop [MN0 MN1 a n m] :
    (MN0 =(a)=> MN1) ->
    ~ NoRecvQ_from n (get_MQ MN0 m) ->
    NoRecvQ_from n (get_MQ MN1 m) ->
    exists v, a = NTau m (MActP (Recv (n, Q) v)).

  Proof.
    intros.
    kill H.
    - consider (exists v, a0 = MActP (Recv (n, Q) v) /\ n0 = m) by (eapply net_vis_TrRecvQ_pop; eauto).
      exists v. auto.
    - assert (NoRecvQ_from n (get_MQ N0' m) \/ ~ NoRecvQ_from n (get_MQ N0' m)) as [|] by eauto using NoRecvQ_from_dec.
      + eapply net_vis_TrRecvQ_pop in H2; eauto.
        hsimpl in *. destruct v; bullshit.
      + eapply net_vis_TrRecvQ_pop in H3; eauto.
        hsimpl in *. destruct v; bullshit.
  Qed.


  Module Rad.

    Open Scope nat_scope.

    Definition initial (self : Name) : MState :=
      {|self := self
      ; lock_id := 0
      ; lock := None
      ; waitees := []
      ; alarm := false
      |}.


    Definition MSend_all (ns : list Name) t v P :=
      List.fold_right (fun n P' => MSend (n, t) v P') P ns.


    Definition Rad_handle (ev : Event) (mstate : MState) : MCode :=
      match ev, mstate with
      (* Back probe *)
      | EvRecv (from, R) probe, {|lock := Some l|} =>
          if NAME.eqb from l
          then
            if NAME.eqb (init probe) (self mstate)
            then
              if (lock_id mstate =? index probe)%nat
              then
                (* ALARM *)
                MRecv {|self := self mstate
                      ; lock_id := lock_id mstate
                      ; lock := lock mstate
                      ; waitees := waitees mstate
                      ; alarm := true
                      |}
              else
                MRecv mstate
            else
              (* Propagate *)
              MSend_all (waitees mstate) R probe (MRecv mstate)
          else (MRecv mstate)

      (* Send query *)
      | TrSend (to, Q) _, _ =>
          MRecv {|self := self mstate
                ; lock_id := S (lock_id mstate)
                ; lock := Some to
                ; waitees := waitees mstate
                ; alarm := alarm mstate
                |}

      (* Send reply *)
      | TrSend (to, R) _, _ =>
          MRecv {|self := self mstate
                ; lock_id := lock_id mstate
                ; lock := lock mstate
                ; waitees := List.remove NAME.eq_dec to (waitees mstate)
                ; alarm := alarm mstate
                |}

      (* Receive query while locked *)
      | TrRecv (from, Q) _, {|lock := Some l|} =>
          MSend (from, R) {|init:=self mstate; index:=lock_id mstate|}
            (MRecv {|self := self mstate
                   ; lock_id := lock_id mstate
                   ; lock := lock mstate
                   ; waitees := from :: waitees mstate
                   ; alarm := alarm mstate
                   |})

      (* Receive query while not locked *)
      | TrRecv (from, Q) _, {|lock := None|} =>
          MRecv {|self := self mstate
                ; lock_id := lock_id mstate
                ; lock := lock mstate
                ; waitees := from :: waitees mstate
                ; alarm := alarm mstate
                |}

      (* Receive reply *)
      | TrRecv (from, R) _, {|lock := Some l|} =>
          if NAME.eqb from l
          then
            MRecv {|self := self mstate
                  ; lock_id := lock_id mstate
                  ; lock := None (* Release lock *)
                  ; waitees := waitees mstate
                  ; alarm := alarm mstate
                  |}
          else
            MRecv mstate

      (* Ignore anything else *)
      | _, _ => MRecv mstate
      end.

    Lemma next_state_Send_all M w t p :
      next_state (Rad.MSend_all w t p M) = next_state M.

    Proof. induction w; attac. Qed.

    #[export] Hint Rewrite next_state_Send_all using spank : LTS LTS_concl.

  End Rad.

  (** A probe is hot when it has the current index of the initiator *)
  (* add lock requirement? *)
  Definition hot MN p n := init p = n /\ index p = _of lock_id MN n.

  Definition hot_of MN n := {|init:=n;index:=_of lock_id MN n|}.

  Fact hot_hot_of MN n : hot MN (hot_of MN n) n.
  Proof. attac. Qed.

  Definition hot_ev MN e n := match e with
                              | EvRecv (_, R) p => hot MN p n
                              | _ => False
                              end.

  Definition hot_ev_of MN n' n := EvRecv (n', R) (hot_of MN n).

  Fact hot_hot_ev_of MN n' n : hot_ev MN (hot_ev_of MN n' n) n.
  Proof. attac. Qed.

  (** Monitor is going to send a probe (inevitably) *)
  Inductive sends_probe : NChan -> MProbe -> MQued -> Prop :=
  | sp_init MQ MQ' c S n n' v p :
    NoRecvR_from n' MQ -> (* We won't unlock *)
    NoSends_MQ MQ -> (* We won't change the lock_id *)
    lock c = Some n' -> (* We are locked *)
    init p = self c -> index p = lock_id c -> (* Our hot probe *)
    sends_probe (n, R)
      p
      (mq
         (MQ ++ TrRecv (n, Q) v :: MQ') (* There is a query incoming... *)
         {|handle:=Rad.Rad_handle; state:=MRecv c|} (* We are ready to take it *)
         S
      )

  | sp_prop MQ MQ' c S n n' p :
    NoRecvR_from n' MQ -> (* We won't unlock *)
    NoSends_MQ MQ -> (* We won't change the lock_id *)
    lock c = Some n' -> (* We are locked *)
    init p <> self c -> (* The probe is not ours *)
    List.In n (waitees c) \/ (exists v, List.In (TrRecv (n, Q) v) MQ) -> (* The receiver will be in waitees *)
    sends_probe (n, R) p (mq (MQ ++ EvRecv (n', R) p :: MQ') {|handle:=Rad.Rad_handle; state:=MRecv c|} S)

  | sp_send MQ M h S nc p :
    sends_probe nc p (mq MQ {|handle:=h; state:=MSend nc p M|} S)

  | sp_late MQ M h S nc nc' p p' :
    (nc' <> nc \/ p' <> p) ->
    sends_probe nc p (mq MQ {|handle:=h; state:=M|} S) ->
    sends_probe nc p (mq MQ {|handle:=h; state:=MSend nc' p' M|} S)
  .

  Hint Constructors sends_probe : LTS.


  (** ** Alarm condition *)
  (** Either there is an alarm, or an alarm is inevitable due to probe and lock alignment *)
  Inductive ac (n : Name) (MN : MNet) : Prop :=
  | ac_alarm :
    _of alarm MN n = true ->
    ac n MN

  | ac_seek [m m'] :
    (n = m \/ dep_on '' MN n m) ->
    net_lock_on '' MN m m' ->  (* TODO: try to relate to mon states exlusively *)
    sends_probe (m, R) (hot_of MN n) (NetMod.get m' MN) ->
    ac n MN

  | ac_fin [n'] :
    net_lock_on '' MN n n' ->
    List.In (hot_ev_of MN n' n) (get_MQ MN n) ->
    ac n MN
  .


  Hint Constructors ac : LTS.

  Lemma _of_put_neq_inv [A] [MN] [F : MState -> A] MQ M S n m :
    n <> m ->
    _of F (NetMod.put n (mq MQ M S) MN) m = _of F MN m.
  Proof. ltac1:(autounfold with LTS_get in * ); attac. Qed.


  Lemma _of_put_eq_inv [A] [MN] [F : MState -> A] MQ M S n :
    _of F (NetMod.put n (mq MQ M S) MN) n = F (next_state (state M)).
  Proof. ltac1:(autounfold with LTS_get in * ); attac. Qed.

  Lemma get_MQ_put_eq_inv [MN] MQ M S n :
    get_MQ (NetMod.put n (mq MQ M S) MN) n = MQ.
  Proof. ltac1:(autounfold with LTS_get in * ); attac. Qed.

  Lemma get_MQ_put_neq_inv [MN] MQ M S n m :
    n <> m ->
    get_MQ (NetMod.put n (mq MQ M S) MN) m = get_MQ MN m.
  Proof. ltac1:(autounfold with LTS_get in * ); attac. Qed.

  Hint Rewrite -> @_of_put_eq_inv @_of_put_neq_inv @get_MQ_put_eq_inv @get_MQ_put_neq_inv using spank : LTS LTS_concl.

  Import Rad.


  Lemma mq_preserve_self [a MQ0 s0 S0 MQ1 M1 S1] :
    (mq MQ0 {|handle:=Rad_handle;state:=s0|} S0 =(a)=> mq MQ1 M1 S1) ->
    self (next_state s0) = self (next_state (state M1)).

  Proof.
    intros.
    destruct M1 as [h1 s1].

    destruct_ma &a; destruct s0, s1; kill H; auto; Control.enter (fun () => consider ({|handle:=_;state:=_|} =(_)=> _));
      repeat (match! goal with
              | [h : (match ?x with _ => _ end = _) |- _] => destruct $x
              end); simpl in *; doubt; hsimpl in *; attac.
    all: destruct waitees0; hsimpl in *; attac.
  Qed.


  Lemma mq_preserve_alarm [a MQ0 s0 S0 MQ1 M1 S1] :
    (mq MQ0 {|handle:=Rad_handle;state:=s0|} S0 =(a)=> mq MQ1 M1 S1) ->
    alarm (next_state s0) = true ->
    alarm (next_state (state M1)) = true.

  Proof.
    intros.
    destruct M1 as [h1 s1].

    destruct_ma &a; destruct s0, s1; kill H; auto; Control.enter (fun () => consider ({|handle:=_;state:=_|} =(_)=> _));
      repeat (match! goal with
              | [h : (match ?x with _ => _ end = _) |- _] => destruct $x
              end); simpl in *; doubt; attac.
    all: destruct waitees0; attac.
  Qed.


  Inductive KIC (MN : MNet) : Prop :=
  | KIC_
      (* We are sane *)
      (H_sane_C : net_sane '' MN)
      (* `self` is correct *)
      (H_self_C : forall n, _of self MN n = n)
      (* We are using the algorithm *)
      (H_Rad_C : forall n, handle (get_M MN n) = Rad.Rad_handle)
      (* Monitor knows about its lock. Note that if there was any R in MQ, it would not be locked. *)
      (H_lock_C : forall n0 n1, net_lock_on '' MN n0 n1 -> _of lock MN n0 = Some n1)
      (* Flushed monitor knows about everyone who waits on it *)
      (H_wait_C : forall n0 n1, net_lock_on '' MN n0 n1 -> NoRecvQ_from n0 (get_MQ MN n1) -> List.In n0 (_of waitees MN n1))
      (* Self-dependency implies alarm condition *)
      (H_alarm_C : forall n0, dep_on '' MN n0 n0 -> exists n1, dep_on '' MN n0 n1 /\ ac n1 MN)
      (* Dependency is decidable *)
      (H_dep_dec_C : forall n0 n1, dep_on '' MN n0 n1 \/ ~ dep_on '' MN n0 n1)
    : KIC MN.


  Lemma net_vis_preserve_alarm [a MN0 MN1 n n'] :
    handle (get_M MN0 n) = Rad.Rad_handle ->
    (MN0 ~(n' @ a)~> MN1) ->
    _of alarm MN0 n = true ->
    _of alarm MN1 n = true.

  Proof.
    intros.

    smash_eq n n'.
    2: ltac1:(autounfold with LTS_get in * );
    replace (NetMod.get n MN0) with (NetMod.get n MN1) by eauto using NV_stay, eq_sym; auto.

    destruct (NetMod.get n MN0) as [MQ0 [h0 s0] S0] eqn:?.
    consider (h0 = Rad.Rad_handle) by
      ( ltac1:(autounfold with LTS_get in * );
        rewrite `(NetMod.get n MN0 = _) in *;
        auto
      ).
    hsimpl in *.
    ltac1:(autounfold with LTS_get in * ).
    rewrite `(NetMod.get n MN0 = _) in *.
    hsimpl in |- *.
    destruct S.
    eauto using mq_preserve_alarm.
  Qed.


  Lemma net_preserve_alarm [na MN0 MN1 n] :
    handle (get_M MN0 n) = Rad.Rad_handle ->
    (MN0 =(na)=> MN1) ->
    _of alarm MN0 n = true ->
    _of alarm MN1 n = true.

  Proof.
    intros.
    consider (MN0 =(_)=> _).
    - eauto using net_vis_preserve_alarm.
    - enough (_of alarm N0' n = true);
        eauto using net_vis_preserve_alarm.
      assert (handle (get_M N0' n) = Rad_handle)
        by (rewrite <- `(_ = Rad_handle); eauto using net_vis_preserve_handle, eq_sym).
      eauto using net_vis_preserve_alarm.
  Qed.



  Lemma net_vis_preserve_self [a MN0 MN1 n n'] :
    handle (get_M MN0 n) = Rad.Rad_handle ->
    (MN0 ~(n' @ a)~> MN1) ->
    _of self MN0 n = _of self MN1 n.

  Proof.
    intros.

    smash_eq n n'.
    2: ltac1:(autounfold with LTS_get in * );
    replace (NetMod.get n MN0) with (NetMod.get n MN1) by eauto using NV_stay, eq_sym; auto.

    destruct (NetMod.get n MN0) as [MQ0 [h0 s0] S0] eqn:?.
    consider (h0 = Rad.Rad_handle) by
      ( ltac1:(autounfold with LTS_get in * );
        rewrite `(NetMod.get n MN0 = _) in *;
        auto
      ).
    hsimpl in * |-.
    ltac1:(autounfold with LTS_get in * ).
    rewrite `(NetMod.get n MN0 = _) in *.
    destruct S.
    rewrite NetMod.get_put_eq. simpl.
    eauto using mq_preserve_self.
  Qed.


  Lemma net_preserve_self [na MN0 MN1 n] :
    handle (get_M MN0 n) = Rad.Rad_handle ->
    (MN0 =(na)=> MN1) ->
    _of self MN0 n = _of self MN1 n.

  Proof.
    intros.
    consider (MN0 =(_)=> _).
    - eauto using net_vis_preserve_self.
    - enough (_of self N0' n = _of self MN0 n);
        eauto using net_vis_preserve_self, eq_sym.
      assert (handle (get_M N0' n) = Rad_handle)
        by (rewrite <- `(_ = Rad_handle); eauto using net_vis_preserve_handle, eq_sym).
      rewrite <- `(_of self _ _ = _ ).
      eauto using net_vis_preserve_self, eq_sym.
  Qed.


  Lemma SRPC_no_immediate_relock [n0 n1 P0 P1 a] :
    AnySRPC P0 ->
    (P0 =(a)=> P1) ->
    proc_lock [n0] P0 ->
    ~ proc_lock [n1] P1.

  Proof.
    intros.
    intros ?.
    assert (AnySRPC P1) by attac.
    consider (exists c, SRPC (Lock c n0) P0) by eauto using lock_SRPC_Lock.
    consider (exists c1, SRPC (Lock c1 n1) P1) by eauto using lock_SRPC_Lock.
    destruct SRPC H4 H0.
    assert (SRPC (Work c) P1) by auto.
    absurd (Work c = Lock c1 n1). intros Hx; kill Hx.
    attac.
  Qed.


  Lemma SRPC_pq_no_immediate_relock [n0 n1 S0 S1 a] :
    AnySRPC_pq S0 ->
    (S0 =(a)=> S1) ->
    pq_lock [n0] S0 ->
    pq_lock [n1] S1 ->
    n0 = n1.

  Proof.
    intros.
    specialize (pq_lock_recv `(pq_lock _ S0) `(S0 =(a)=> S1)) as ?.
    destruct a; doubt.
    compat_hsimpl in *.
    consider (pq_lock [n0] _).
    do 2 (consider (pq_lock [n1] _)).
    enough (List.In n0 [n1]) by attac.
    enough (incl [n0] [n1]) by (unfold incl in *; attac).
    eauto using proc_lock_incl.
  Qed.

  Import Srpc.


  (* Lemma SRPC_net_vis_no_immediate_relock [n n' m0 m1 N0 N1 a] : *)
  (*   SRPC_net N0 -> *)
  (*   (N0 ~(n' @ a)~> N1) -> *)
  (*   net_lock_on N0 n m0 -> *)
  (*   net_lock_on N1 n m1 -> *)
  (*   m0 = m1. *)

  (* Proof. *)
  (*   intros. *)
  (*   assert (SRPC_net N1). (* TODO extract as invariant any name it *) *)
  (*   { *)
  (*     intros ?. *)
  (*     smash_eq n' n0. *)
  (*     - kill H0. *)
  (*       hsimpl in |- *. *)
  (*       eauto with LTS. *)
  (*     - assert (NetMod.get n0 N0 = NetMod.get n0 N1) by eauto using NV_stay. *)
  (*       rewrite <- `(NetMod.get n0 N0 = _) in *. *)
  (*       auto. *)
  (*   } *)


  (*   smash_eq n' n. *)
  (*   - kill H0. *)
  (*     hsimpl in H2. *)
  (*     eapply SRPC_pq_no_immediate_relock; eauto. *)
  (*   - assert (NetMod.get n N0 = NetMod.get n N1) by eauto using NV_stay. *)
  (*     rewrite <- `(NetMod.get n N0 = _) in *. *)
  (*     enough (List.In m0 [m1]) by attac. *)
  (*     enough (incl [m0] [m1]) by (unfold incl in *; attac). *)
  (*     eauto using pq_lock_incl. *)
  (* Qed. *)


  (* Lemma SRPC_net_no_immediate_relock [n m0 m1 N0 N1 a] : *)
  (*   (forall n, AnySRPC_pq (NetMod.get n N0)) -> *)
  (*   (N0 =(a)=> N1) -> *)
  (*   net_lock_on N0 n m0 -> *)
  (*   net_lock_on N1 n m1 -> *)
  (*   m0 = m1. *)

  (* Proof. *)
  (*   intros. *)
  (*   kill H0. *)
  (*   - eauto using SRPC_net_vis_no_immediate_relock. *)
  (*   - *)
  (*     eauto using SRPC_net_vis_no_immediate_relock. *)
  (*     assert (SRPC_net N1). *)
  (*     { *)
  (*       intros ?. *)
  (*       smash_eq n0 n1. *)
  (*       - kill H3. *)
  (*         kill H4. *)
  (*         hsimpl in *. *)
  (*         smash_eq n0 n'; attac. *)
  (*       - assert (NetMod.get n1 N0 = NetMod.get n1 N0') by eauto using NV_stay. *)
  (*         hsimpl in *. *)
  (*         hsimpl in *. *)
  (*         smash_eq n1 n'; attac. *)
  (*     } *)
  (*     assert (net_lock_on N0' n m0). *)
  (*     { *)
  (*       apply lock_singleton in H1; eauto with LTS. *)
  (*       exists [m0]. split. 1: attac. *)
  (*       unfold net_lock in *. *)
  (*       smash_eq n n0. *)
  (*       - kill H3. *)
  (*         specialize (pq_lock_recv `(pq_lock [m0] (NetMod.get n N0)) `(NetMod.get n N0 =(send (n', &t) v)=> &S)) as ?. *)
  (*         bullshit. *)
  (*       - assert (NetMod.get n N0 = NetMod.get n N0') by eauto using NV_stay. *)
  (*         rewrite <- `(NetMod.get n N0 = _) in *. *)
  (*         auto. *)
  (*     } *)
  (*     eauto using SRPC_net_vis_no_immediate_relock with LTS. *)
  (* Qed. *)


  Lemma SRPC_M_net_no_immediate_relock [n m0 m1 N0 N1 a] :
    (forall n, AnySRPC_pq (NetMod.get n '' N0)) ->
    (N0 =(a)=> N1) ->
    net_lock_on '' N0 n m0 ->
    net_lock_on '' N1 n m1 ->
    m0 = m1.

  Proof.
    intros.
    destruct (MNAct_to_PNAct a) eqn:?.
    - assert ('' N0 =(p)=> '' N1) by eauto with LTS.
      eauto using SRPC_net_no_relock.
    - replace ('' N1) with ('' N0) in H2 by eauto using eq_sym with LTS.
      eapply SRPC_net_lock_uniq; eauto with LTS.
  Qed.


  (* Theorem SRPC_net_new_lock_query [N0 N1 : PNet] [n0 n1 a] : *)
  (*   net_sane N0 -> *)
  (*   ~ net_lock_on N0 n0 n1 -> *)
  (*   net_lock_on N1 n0 n1 -> *)
  (*   (N0 =(a)=> N1) -> *)
  (*   exists v, a = NComm n0 n1 Q v. *)

  (* Proof. *)
  (*   intros. *)

  (*   destruct (NetMod.get n0 N0) as [I0 P0 O0] eqn:?. *)
  (*   destruct (NetMod.get n0 N1) as [I1 P1 O1] eqn:?. *)

  (*   assert (exists c, SRPC_pq (Lock c n1) (NetMod.get n0 N1)). *)
  (*   { *)
  (*     apply lock_singleton in H1. 2: attac. *)
  (*     unfold net_lock in *. *)
  (*     eapply lock_SRPC_Lock_pq; eattac. *)
  (*   } *)
  (*   hsimpl in *. *)

  (*   assert (O1 = [] /\ (exists h, P1 = PRecv h) /\ forall m v, ~ List.In (m, R, v) I1). *)
  (*   { *)
  (*     apply lock_singleton in H1. 2: attac. *)
  (*     unfold net_lock in *. *)
  (*     rewrite `(NetMod.get n0 N1 = _) in *. *)
  (*     compat_hsimpl in *. *)
  (*     consider (pq_lock [n1] (pq _ _ _)). *)
  (*     destruct P1; doubt. *)
  (*     eattac 3. *)
  (*     consider (exists c', SRPC_pq (Lock c' m) (NetMod.get n0 N1)) by eauto with LTS. *)
  (*     consider (Lock c' m = Lock c n1) by eauto with LTS. *)
  (*     bullshit (List.In (n1, R, v) I1). *)
  (*   } *)
  (*   hsimpl in *. *)

  (*   destruct a. *)
  (*   - kill H2. *)
  (*     exfalso. *)
  (*     hsimpl in *. *)
  (*     smash_eq n0 n. *)
  (*     2: unfold net_lock_on, net_lock in *; hsimpl in *; bullshit. *)

  (*     rewrite `(NetMod.get n0 N0 = _) in *. *)
  (*     hsimpl in *. *)

  (*     kill H. *)
  (*     specialize (H_Sane_SRPC n0) as [srpc0 ?]. *)
  (*     kill H. *)
  (*     hsimpl in *. *)
  (*     kill H5. *)
  (*     + kill Hsrpc. *)
  (*       * apply HQueryOnly in H. *)
  (*         hsimpl in H. *)
  (*         absurd (Work c0 = Lock c n1); eauto with LTS. *)
  (*         intros Hx; kill Hx. *)
  (*       * destruct n. *)
  (*         destruct t0. *)
  (*         -- kill HBusy. *)
  (*            ++ kill H. *)
  (*            ++ apply HReplyOnly in H. *)
  (*               attac. *)
  (*         -- apply HRecv in H. *)
  (*            absurd (Work c0 = Lock c n1); eauto with LTS. *)
  (*            intros Hx; kill Hx. *)
  (*     + bullshit. *)
  (*     + kill Hsrpc. *)
  (*       * apply HQueryOnly in H. *)
  (*         hsimpl in *. *)
  (*         bullshit. *)
  (*       * apply HTau in H. *)
  (*         absurd (Work c0 = Lock c n1); eauto with LTS. *)
  (*         intros Hx; kill Hx. *)
  (*   - exists p. *)
  (*     smash_eq n0 n. *)
  (*     + destruct t0. *)
  (*       * enough (n2 = n1) by (subst; auto). *)
  (*         enough (net_lock_on N1 n0 n2) by eauto using lock_uniq with LTS. *)
  (*         enough (pq_client n0 (NetMod.get n2 N1)) by eauto with LTS. *)
  (*         kill H2. *)
  (*         compat_hsimpl in *. *)
  (*         attac. *)
  (*       * exfalso. *)
  (*         assert (net_sane N1) by eauto with LTS. *)
  (*         kill H2. *)
  (*         compat_hsimpl in *. *)
  (*         absurd (exists v, (List.In (n1, Q, v) ((n2, R, p) :: O2))). *)
  (*         -- intros ?; hsimpl in *. *)
  (*            smash_eq n0 n2; hsimpl in *; bullshit. *)
  (*         -- kill H. *)
  (*            specialize (H_Sane_SRPC n0) as [? ?]. *)
  (*            kill H. *)
  (*            smash_eq n0 n2; hsimpl in *. *)
  (*            ++ assert (x = Lock c n1) by eauto with LTS. subst. *)
  (*               bullshit. *)
  (*            ++ assert (x = Lock c n1) by eauto with LTS. subst. *)
  (*               specialize (H_lock_Q _ _ eq_refl). *)
  (*               clear - H_lock_Q. *)
  (*               attac. *)
  (*     + absurd (net_lock_on N0 n0 n1); auto. *)
  (*       kill H2. *)
  (*       smash_eq n0 n2; hsimpl in *. *)
  (*       -- unfold net_lock_on, net_lock in *. *)
  (*          compat_hsimpl in *. *)
  (*          rewrite `(NetMod.get n0 N0 = _) in *. *)
  (*          kill H2. *)
  (*          exists L; split; auto. *)
  (*          constructor; auto. *)
  (*          intros. *)
  (*          eattac. *)
  (*       -- unfold net_lock_on, net_lock in *. *)
  (*          hsimpl in *. *)
  (*          rewrite `(NetMod.get n0 N0 = _) in *. *)
  (*          kill H2. *)
  (*          exists L; split; auto. *)
  (*          constructor; auto. *)
  (* Qed. *)


  Theorem SRPC_M_net_new_lock_query [N0 N1 : MNet] [n0 n1 a] :
    net_sane '' N0 ->
    ~ net_lock_on '' N0 n0 n1 ->
    net_lock_on '' N1 n0 n1 ->
    (N0 =(a)=> N1) ->
    exists v, a = NComm n0 n1 Q (MValP v).
  Proof.
    intros.
    destruct (MNAct_to_PNAct a) eqn:?.
    - assert ('' N0 =(p)=> '' N1) by eauto with LTS.
      consider (exists v, p = NComm n0 n1 Q v) by eauto using net_sane_new_lock_send_Q.
      exists v.
      destruct a; attac; blast_cases; attac.
    - unfold net_lock_on in *.
      replace ('' N1) with ('' N0) in H1 by eauto using eq_sym with LTS.
      bullshit.
  Qed.


  Import SrpcNet. (* TODO why is this needed here?! *)

  Theorem SRPC_M_net_unlock_reply [N0 N1 : MNet] [n0 n1 a] :
    net_sane '' N0 ->
    net_lock_on '' N0 n0 n1 ->
    ~ net_lock_on '' N1 n0 n1 ->
    (N0 =(a)=> N1) ->
    exists v, a = NComm n1 n0 R (MValP v).

  Proof.
    intros.
    destruct (MNAct_to_PNAct a) eqn:?.
    - assert ('' N0 =(p)=> '' N1) by eauto with LTS.
      consider (exists v, p = NComm n1 n0 R v) by (eapply net_unlock_on_reply; eauto with LTS).
      exists v.
      destruct a; attac; blast_cases; attac.
    - unfold net_lock_on in *.
      replace ('' N1) with ('' N0) in H1 by eauto using eq_sym with LTS.
      bullshit.
  Qed.


  Lemma SRPC_M_net_new_lock_uniq [N0 N1 : MNet] [na] [n0 n1 m0 m1] :
    net_sane '' N0 ->
    (N0 =(na)=> N1) ->
    ~ net_lock_on '' N0 n0 n1 ->
    ~ net_lock_on '' N0 m0 m1 ->
    net_lock_on '' N1 n0 n1 ->
    net_lock_on '' N1 m0 m1 ->
    n0 = m0 /\ n1 = m1.

  Proof.
    intros.
    assert (exists v, na = NComm n0 n1 Q (MValP v)) by eauto using SRPC_M_net_new_lock_query.
    assert (exists v, na = NComm m0 m1 Q (MValP v)) by eauto using SRPC_M_net_new_lock_query.
    attac.
  Qed.


  Theorem SRPC_net_query_new_lock [N0 N1 : PNet] [n0 n1 v] :
    net_sane N0 ->
    (N0 =(NComm n0 n1 Q v)=> N1) ->
    (~ net_lock_on N0 n0 n1 /\ net_lock_on N1 n0 n1).

  Proof.
    split; intros.
    - intros HL.
      unfold net_lock_on, net_lock in *.
      hsimpl in *.
      kill H0; compat_hsimpl in *; bullshit.
    - eauto using net_sane_send_Q_new_lock.
  Qed.


  Theorem SRPC_M_net_query_new_lock [N0 N1 : MNet] [n0 n1 v] :
    net_sane '' N0 ->
    (N0 =(NComm n0 n1 Q (MValP v))=> N1) ->
    (~ net_lock_on '' N0 n0 n1 /\ net_lock_on '' N1 n0 n1).

  Proof.
    intros.
    assert ('' N0 =(@NComm _ gen_Act_PAct n0 n1 Q v)=> '' N1)
      by (eapply net_deinstr_act_do; eauto with LTS; simpl; eauto with LTS).
    eauto using SRPC_net_query_new_lock.
  Qed.


  Theorem SRPC_net_reply_unlock [N0 N1 : PNet] [n0 n1 v] :
    net_sane N0 ->
    (N0 =(NComm n0 n1 R v)=> N1) ->
    (net_lock_on N0 n1 n0 /\ ~ net_lock_on N1 n1 n0).

  Proof.
    intros.
    split.
    - eauto using net_sane_send_R_lock_l.
    - eauto using net_sane_send_R_receiver_no_lock.
  Qed.


  Theorem SRPC_M_net_reply_unlock [N0 N1 : MNet] [n0 n1 v] :
    net_sane '' N0 ->
    (N0 =(NComm n0 n1 R (MValP v))=> N1) ->
    (net_lock_on '' N0 n1 n0 /\ ~ net_lock_on '' N1 n1 n0).

  Proof.
    intros.
    assert ('' N0 =(@NComm _ gen_Act_PAct n0 n1 R v)=> '' N1)
      by (eapply net_deinstr_act_do; eauto with LTS; simpl; eauto with LTS).
    eauto using SRPC_net_reply_unlock.
  Qed.


  Lemma SRPC_proc_client_dec n P :
    AnySRPC P ->
    proc_client n P \/ ~ proc_client n P.

  Proof.
    intros.
    destruct H as [srpc Hsrpc].
    hsimpl in *.
    destruct srpc.
    - right; intros ?.
      kill H.
      absurd (Busy x = Free); eauto using SRPC_inv with LTS.
    - smash_eq c n.
      + eauto with LTS.
      + right; intros ?.
        kill H.
        absurd (Busy x = Busy s); eauto using SRPC_inv with LTS.
  Qed.


  Lemma SRPC_pq_client_dec [n S] :
    AnySRPC_pq S ->
    pq_client n S \/ ~ pq_client n S.

  Proof.
    intros.
    destruct S as [I P O].
    destruct (SRPC_proc_client_dec n P);
      destruct (@in_dec_v _ (n, Q) &I);
      destruct (@in_dec_v _ (n, R) &O);
      eattac.

    right; intros ?.
    kill H3; eattac.
  Qed.


  Lemma net_sane_lock_dec N n0 n1 :
    net_sane N ->
    net_lock_on N n0 n1 \/ ~ net_lock_on N n0 n1.

  Proof.
    intros.
    enough (pq_client n0 (NetMod.get n1 N) \/ ~ pq_client n0 (NetMod.get n1 N)) as [|] by eattac.
    eauto using SRPC_pq_client_dec with LTS.
  Qed.


  Theorem SRPC_net_tau_preserve_lock [N0 N1 : PNet] [n a] :
    net_sane N0 ->
    (N0 =(NTau n a)=> N1) ->
    forall n0 n1, net_lock_on N0 n0 n1 <-> net_lock_on N1 n0 n1.

  Proof.
    intros.
    split; intros.
    - assert (net_sane N1) by auto with LTS.
      destruct (net_sane_lock_dec N1 n0 n1); eauto.
      absurd (exists v, NTau n a = NComm n1 n0 R v); eauto using net_unlock_on_reply.
      attac.
      eapply net_unlock_on_reply with (N0:=N0)(N1:=N1); eauto with LTS.
    - destruct (net_sane_lock_dec N0 n0 n1); eauto.
      absurd (exists v, NTau n a = NComm n0 n1 Q v); eauto using net_sane_new_lock_send_Q.
      intros ?; attac.
  Qed.


  Theorem SRPC_M_net_tau_preserve_lock [N0 N1 : MNet] [n a] :
    net_sane '' N0 ->
    (N0 =(NTau n a)=> N1) ->
    forall n0 n1, net_lock_on '' N0 n0 n1 <-> net_lock_on '' N1 n0 n1.

  Proof.
    intros.
    destruct (MNAct_to_PNAct (NTau n a)) eqn:?.
    - assert ('' N0 =(p)=> '' N1) by eauto with LTS.
      destruct a; doubt; destruct p0; doubt.
      hsimpl in *; eauto using SRPC_net_tau_preserve_lock.
    - unfold net_lock_on in *.
      replace ('' N1) with ('' N0) by eauto using eq_sym with LTS.
      attac.
  Qed.


  (* TODO move up *)
  Definition Rad_MQued MS :=
    match MS with
    | mq _ {|handle:=h;state:=s|} _ => h = Rad_handle
    end.

  Definition Rad_net N := forall n, Rad_MQued (NetMod.get n N).


  Lemma Rad_net_invariant : trans_invariant Rad_net always.

  Proof.
    unfold trans_invariant, Rad_net, Rad_MQued.
    intros.
    assert (handle (get_M N0 n) = handle (get_M N1 n)) by eauto using net_preserve_handle.
    ltac1:(autounfold with LTS_get in * ).
    specialize (H0 n).
    destruct (NetMod.get n N0).
    destruct (NetMod.get n N1).
    destruct m, m0.
    attac.
  Qed.

  Hint Resolve Rad_net_invariant : inv.
  Hint Extern 0 (Rad_net _) => solve_invariant : LTS.


  Lemma Rad_MQued_inv MQ M S :
    Rad_MQued (mq MQ M S) <-> handle M = Rad_handle.
  Proof. split; intros; destruct M; attac. Qed.


  Lemma Rad_net_inv MN n :
    Rad_net MN ->
    handle (get_M MN n) = Rad_handle.
  Proof. intros; specialize (H n); ltac1:(autounfold with LTS_get in * ); destruct (NetMod.get n MN);
           unfold Rad_MQued in *; destruct m; attac.
  Qed.

  Hint Rewrite -> Rad_MQued_inv Rad_net_inv using spank : LTS LTS_concl.


  Lemma Rad_net_get MN n MQ h s S:
    Rad_net MN ->
    NetMod.get n MN = mq MQ {|handle:=h; state:=s|} S ->
    h = Rad_handle.

  Proof.
    intros.
    assert (Rad_MQued (NetMod.get n MN)) by attac.
    rewrite `(NetMod.get n MN = _) in *.
    auto.
  Qed.

  Hint Resolve Rad_net_get : LTS.


  Lemma M_vis_preserve_steady_lock [MN0 MN1 : MNet] [a n n' m0 m1] :
    Rad_net MN0 ->
    (MN0 ~(n' @ a)~> MN1) ->
    _of lock MN0 n = Some m0 ->
    _of lock MN1 n = Some m1 ->
    (forall v, a <> MActT (Send (m1, Q) v)) ->
    m0 = m1.

  Proof.
    intros.
    destruct (NetMod.get n MN0) as [MQ0 [h0 s0] S0] eqn:?.
    destruct (NetMod.get n MN1) as [MQ1 [h1 s1] S1] eqn:?.

    assert (h0 = Rad_handle) by eauto with LTS.
    smash_eq n n'.
    - ltac1:(autounfold with LTS_get in * ).
      rewrite `(NetMod.get n MN0 = _) in *.
      rewrite `(NetMod.get n MN1 = _) in *.
      compat_hsimpl in *.
      destruct_ma &a; try (destruct t0); doubt; auto; compat_hsimpl in *; auto; try (destruct s); simpl in *; subst;
        repeat (match! goal with
                | [_ : lock (next_state (match ?x with _ => _ end)) = _ |- _] => destruct $x
                end); simpl in *; doubt; compat_hsimpl in *; attac.

    - enough (Some m0 = Some m1) by attac.
      enough (_of lock MN0 n = _of lock MN1 n) by (rewrite `(_of lock MN0 n = _) in *; attac).
      ltac1:(autounfold with LTS_get in * ).
      assert (NetMod.get n MN0 = NetMod.get n MN1) by eauto using NV_stay with LTS.
      attac.
  Qed.


  (* TODO move up *)
  Lemma NV_preserve_Rad_net [MN0 MN1 : MNet] [n a] :
    (MN0 ~(n @ a)~> MN1) ->
    Rad_net MN0 ->
    Rad_net MN1.

  Proof.
    intros.
    compat_hsimpl in *.
    intros ?.
    smash_eq n n0; hsimpl; attac.
    assert (Rad_MQued (NetMod.get n MN0)) by attac.
    destruct S as [MQ1 M1 S1].
    destruct (NetMod.get n MN0) as [MQ0 M0 S0].
    assert (handle M0 = handle M1) by eauto using mq_preserve_handle1.
    destruct M0, M1.
    eattac.
  Qed.

  Hint Resolve NV_preserve_Rad_net : LTS.


  Lemma M_preserve_steady_lock [MN0 MN1 : MNet] [na n m0 m1] :
    Rad_net MN0 ->
    SRPC_net '' MN0 ->
    (MN0 =(na)=> MN1) ->
    _of lock MN0 n = Some m0 ->
    _of lock MN1 n = Some m1 ->
    (forall v, na <> NComm n m1 Q (MValP v)) ->
    m0 = m1.

  Proof.
    intros.
    destruct (NetMod.get n MN0) as [MQ0 [h0 s0] S0] eqn:?.
    destruct (NetMod.get n MN1) as [MQ1 [h1 s1] S1] eqn:?.

    assert (h0 = Rad_handle) by eauto with LTS. subst.

    consider (MN0 =(_)=> _).
    - eapply M_vis_preserve_steady_lock; eauto with LTS.
      intros ? ?. attac.
    - destruct (_of lock N0' n) as [n1|] eqn:?.
      + transitivity 'n1.
        * smash_eq n0 n.
          -- kill H5.
             clear H5.
             eapply M_vis_preserve_steady_lock; eauto with LTS.
             intros ? ?. hsimpl in *.
             destruct v; doubt.
             hsimpl in *.
             ltac1:(autounfold with LTS_get in * ).
             rewrite `(NetMod.get n0 (NetMod.put _ _ _) = _) in *.
             rewrite `(NetMod.get n0 MN0 = _) in *.
             hsimpl in *. hsimpl in *.
             smash_eq n0 n1; compat_hsimpl in *; compat_hsimpl in *.
             ++ bullshit (NComm m1 m1 Q # v0  <> NComm m1 m1 Q # v0).
             ++ bullshit (NComm n0 m1 Q # v0 <> NComm n0 m1 Q # v0).
          -- enough (Some m0 = Some n1) by attac.
             enough (_of lock MN0 n = _of lock N0' n)
               by (rewrite `(_of lock MN0 n = _) in *;
                   rewrite `(_of lock N0' n = _) in *;
                   attac
                  ).
             ltac1:(autounfold with LTS_get in * ).
             hsimpl in *. hsimpl in *. hsimpl in |- *.
             auto.

        * assert (Rad_net N0') by eauto with LTS.
          eapply M_vis_preserve_steady_lock;
            eauto with LTS.
          intros ? ?. hsimpl in *.
          destruct v; bullshit.
      + exfalso.
        ltac1:(autounfold with LTS_get in * ).
        destruct (NetMod.get n N0') as [MQ0' [h0' s0'] S0'] eqn:?.
        smash_eq n n'; compat_hsimpl in *.
        * destruct v; kill H5; attac.
        * destruct v; kill H5; attac.
  Qed.


  Lemma M_lock_decide [MN0 MN1 : MNet] [na n] :
    Rad_net MN0 ->
    SRPC_net '' MN0 ->
    (MN0 =(na)=> MN1) ->
    (forall n' v, na <> NComm n n' Q (MValP v)) ->
    _of lock MN0 n <> _of lock MN1 n -> (_of lock MN0 n = None \/ _of lock MN1 n = None).

  Proof.
    intros.
    destruct (_of lock MN0 n) as [n0|] eqn:?; auto.
    destruct (_of lock MN1 n) as [n1|] eqn:?; auto.
    assert (forall v, na <> NComm n n1 Q (MValP v)) by auto.
    assert (n0 = n1) by eauto using M_preserve_steady_lock.
    bullshit.
  Qed.


  Lemma M_vis_set_lock [MN0 MN1 : MNet] [a n n' n''] :
    Rad_net MN0 ->
    (MN0 ~(n'' @ a)~> MN1) ->
    _of lock MN0 n = None ->
    _of lock MN1 n = Some n' ->
    exists v, a = send (n', Q) (MValP v).

  Proof.
    intros.
    destruct (NetMod.get n MN0) as [MQ0 [h0 s0] S0] eqn:?.
    destruct (NetMod.get n MN1) as [MQ1 [h1 s1] S1] eqn:?.

    assert (h0 = Rad_handle) by eauto with LTS. subst.
    smash_eq n n''.
    - ltac1:(autounfold with LTS_get in * ).
      rewrite `(NetMod.get n MN0 = _) in *.
      rewrite `(NetMod.get n MN1 = _) in *.
      compat_hsimpl in *.
      destruct_ma &a; try (destruct t0); doubt; auto; compat_hsimpl in *; auto;
        try (destruct s); simpl in *; subst;
        repeat (match! goal with
                | [_ : lock (next_state (match ?x with _ => _ end)) = _ |- _] => destruct $x
                end); simpl in *; doubt; compat_hsimpl in *; attac.

    - ltac1:(autounfold with LTS_get in * ).
      assert (NetMod.get n MN0 = NetMod.get n MN1) by eauto using NV_stay with LTS.
      rewrite `(NetMod.get n MN1 = _) in *.
      compat_hsimpl in *. compat_hsimpl in *.
      bullshit.
  Qed.


  Lemma M_set_lock [MN0 MN1 : MNet] [na n n'] :
    Rad_net MN0 ->
    (MN0 =(na)=> MN1) ->
    _of lock MN0 n = None ->
    _of lock MN1 n = Some n' ->
    exists v, na = NComm n n' Q (MValP v).

  Proof.
    intros.
    consider (MN0 =(_)=> MN1).
    - consider (exists v, a = send (n', Q) (MValP v)) by eauto using M_vis_set_lock.
      bullshit.
    - enough (exists v', n0 = n /\ n'0 = n' /\ &t = Q /\ v = MValP v') by (hsimpl in *; exists v'; f_equal; eattac).
      assert (_of lock N0' n = _of lock MN1 n).
      {
        hsimpl in *.
        ltac1:(autounfold with LTS_get in * ).
        smash_eq n n'0; hsimpl in *.
        * destruct v; hsimpl in *; attac.
        * attac.
      }
      rewrite <- `(_of lock N0' n = _) in *.

      destruct (_of lock N0' n) as [n1|] eqn:?; doubt.

      consider (exists v', send (n'0, &t) v = send (n1, Q) (MValP v')) by eauto using M_vis_set_lock.
      destruct v; doubt; hsimpl in *.
      smash_eq n n0; eattac.
  Qed.


  Lemma M_vis_unlock [MN0 MN1 : MNet] [a n n' n''] :
    Rad_net MN0 ->
    (MN0 ~(n'' @ a)~> MN1) ->
    _of lock MN0 n = Some n' ->
    _of lock MN1 n = None ->
    exists v, a = MActP (Recv (n', R) v) /\ n'' = n.

  Proof.
    intros.
    destruct (NetMod.get n MN0) as [MQ0 [h0 s0] S0] eqn:?.
    destruct (NetMod.get n MN1) as [MQ1 [h1 s1] S1] eqn:?.

    assert (h0 = Rad_handle) by eauto with LTS. subst.
    smash_eq n n''.
    - ltac1:(autounfold with LTS_get in * ).
      rewrite `(NetMod.get n MN0 = _) in *.
      rewrite `(NetMod.get n MN1 = _) in *.
      hsimpl in *.
      destruct_ma &a; try (destruct t0); doubt; auto; hsimpl in *; auto;
        try (destruct s); simpl in *; subst;
        repeat (match! goal with
                | [_ : lock (next_state (match ?x with _ => _ end)) = _ |- _] => destruct $x eqn:?
                end); simpl in *; doubt; hsimpl in *; attac.

    - ltac1:(autounfold with LTS_get in * ).
      assert (NetMod.get n MN0 = NetMod.get n MN1) by eauto using NV_stay with LTS.
      rewrite `(NetMod.get n MN1 = _) in *.
      compat_hsimpl in *. compat_hsimpl in *.
      bullshit.
  Qed.


  Lemma Rad_set_unlock [MN0 MN1 : MNet] [na n n'] :
    Rad_net MN0 ->
    (MN0 =(na)=> MN1) ->
    _of lock MN0 n = Some n' ->
    _of lock MN1 n = None ->
    exists v, na = NTau n (MActP (Recv (n', R) v)).

  Proof.
    intros.
    consider (MN0 =(_)=> MN1).
    - consider (exists v, a = MActP (Recv (n', R) v) /\ n0 = n) by eauto using M_vis_unlock.
      exists v; auto.
    - exfalso.
      destruct (_of lock N0' n) as [n1|] eqn:?.
      + assert (Rad_net N0') by eauto with LTS.
        consider (exists v', recv (n0, &t) v = MActP (Recv (n1, R) v') /\ n'0 = n) by eauto using M_vis_unlock.
        destruct v; bullshit.
      + consider (exists v', send (n'0, &t) v = MActP (Recv (n', R) v') /\ n0 = n) by eauto using M_vis_unlock.
        destruct v; bullshit.
  Qed.


  Lemma MProbe_eq_dec : forall (p0 p1 : MProbe), {p0 = p1}+{p0 <> p1}.

  Proof.
    intros.
    destruct p0, p1.
    smash_eq init0 init1; destruct (PeanoNat.Nat.eq_dec index0 index1); attac.
  Qed.


  (* Lemma Event_eq_dec : forall (e0 e1 : Event), {e0 = e1}+{e0 <> e1}. *)

  (* Proof. *)
  (*   intros. *)
  (*   destruct e0, e1; destruct (NChan_eq_dec n n0); attac. *)
  (*   - destruct (Val_eq_dec v v0); attac. *)
  (*   - destruct (Val_eq_dec v v0); attac. *)
  (*   - destruct (MProbe_eq_dec m m0); attac. *)
  (* Qed. *)


  Lemma hot_dec MN p n : hot MN p n \/ ~ hot MN p n.
  Proof.
    destruct (MProbe_eq_dec p (hot_of MN n)); subst.
    - auto using hot_hot_of.
    - right.
      intros ?.
      apply `(p <> _).
      consider (hot _ _ _).
      unfold hot_of.
      destruct p.
      auto.
  Qed.


  Lemma wtf [A : Type] (l : list A) (P0 P1 : list A -> Prop) :
    (forall l, P0 l \/ ~ P0 l) ->
    (forall l, P1 l \/ ~ P1 l) ->
    (exists l0 l1, l = l0 ++ l1 /\ P0 l0 /\ P1 l0) \/
      ~ exists l0 l1, l = l0 ++ l1 /\ P0 l0 /\ P1 l0.
    intros.
    ltac1:(rev_induction l).
    - specialize (H []).
      specialize (H0 []).
      destruct H, H0.
      1: left; attac.
      all: right; intros ?; hsimpl in *; destruct l0, l1; bullshit.
    - intros.
      destruct H1.
      + hsimpl in *.
        rewrite <- app_assoc.
        left. exists l0, (l1 ++ [a]). auto.
      + assert (forall T (l : list T), l = [] \/ exists l' a, l = l' ++ [a]) as snoc_inv.
        {
          clear. induction l; attac. destruct IHl; attac. exists [], a; attac.
        }

        destruct (H (l ++ [a])), (H0 (l ++ [a])).
        * left. exists (l ++ [a]), []. attac.
        * right.
          intros Hx; apply H1; clear H1; hsimpl in *.
          specialize (snoc_inv _ l1) as [|]; hsimpl in *.
          -- bullshit.
          -- exists l0, l'.
             rewrite app_assoc in Hx.
             apply app_inj_tail in Hx.
             eattac.
        * right.
          intros Hx; apply H1; clear H1; hsimpl in *.
          specialize (snoc_inv _ l1) as [|]; hsimpl in *.
          -- bullshit.
          -- exists l0, l'.
             rewrite app_assoc in Hx.
             apply app_inj_tail in Hx.
             eattac.
        * right.
          intros Hx; apply H1; clear H1; hsimpl in *.
          specialize (snoc_inv _ l1) as [|]; hsimpl in *.
          -- bullshit.
          -- exists l0, l'.
             rewrite app_assoc in Hx.
             apply app_inj_tail in Hx.
             eattac.
  Qed.

  Lemma wtf' [A : Type] (l : list A) (P0 : list A -> Prop) :
    (forall l, P0 l \/ ~ P0 l) ->
    (exists l0 l1, l = l0 ++ l1 /\ P0 l0) \/
      ~ exists l0 l1, l = l0 ++ l1 /\ P0 l0.
    intros.
    ltac1:(rev_induction l).
    - specialize (H []).
      destruct H.
      1: left; attac.
      all: right; intros ?; hsimpl in *; destruct l0, l1; bullshit.
    - intros.
      destruct H0.
      + hsimpl in *.
        rewrite <- app_assoc.
        left. exists l0, (l1 ++ [a]). auto.
      + assert (forall T (l : list T), l = [] \/ exists l' a, l = l' ++ [a]) as snoc_inv.
        {
          clear. induction l; attac. destruct IHl; attac. exists [], a; attac.
        }

        destruct (H (l ++ [a])).
        * left. exists (l ++ [a]), []. attac.
        * right.
          intros Hx; apply H0; clear H0; hsimpl in *.
          specialize (snoc_inv _ l1) as [|]; hsimpl in *.
          -- bullshit.
          -- exists l0, l'.
             rewrite app_assoc in Hx.
             apply app_inj_tail in Hx.
             eattac.
  Qed.


  Lemma sends_probe_dec n p MS :
    Rad_MQued MS ->
    sends_probe n p MS \/ ~ sends_probe n p MS.

  Proof.
    intros.
    destruct MS as [MQ M S].
    destruct M.
    induction state0.

    (* Rare case where inductive step is simpler than the base! *)
    2: destruct (NChan_eq_dec n to);
    destruct (MProbe_eq_dec p msg);
    destruct IHstate0; subst; eattac; right; intros Hx; kill Hx.

    destruct n.
    destruct t.
    1: right; attac.

    pose (init_case :=
            exists (MQ' MQ'' : list Event)
                   (n' : Name) (v : Val),
              NoRecvR_from n' MQ' /\
                NoSends_MQ MQ' /\
                lock state0 = Some n' /\
                init p = self state0 /\
                index p = lock_id state0 /\
                MQ = (MQ' ++ TrRecv (n, Q) v :: MQ'')
         ).

    pose (prop_case :=
            exists (MQ' MQ'' : list Event)
                   (n' : Name),
              NoRecvR_from n' MQ' /\
                NoSends_MQ MQ' /\
                lock state0 = Some n' /\
                init p <> self state0 /\
                (List.In n (waitees state0) \/ (exists v : Val, List.In (TrRecv (n, Q) v) MQ')) /\
                MQ = (MQ' ++ EvRecv (n', R) p :: MQ'')
         ).

    enough ((init_case \/ ~ init_case) /\ (prop_case \/ ~ prop_case)).
    {
      hsimpl in *.
      consider (init_case \/ ~ init_case); hsimpl in *.
      1: subst init_case; hsimpl in *; left; econstructor 1; eauto.
      consider (prop_case \/ ~ prop_case).
      1: subst prop_case; hsimpl in *; left; econstructor 2; eauto.

      right.
      intros Hx.
      kill Hx.
      - apply `(~ init_case); subst init_case; eexists _, _, _; eattac.
      - apply `(~ prop_case); subst init_case; eexists _, _, _; eattac.
    }

    split; subst init_case prop_case; clear.
    - induction MQ.
      1: right; intros Hx; hsimpl in Hx; bullshit.

      destruct a.
      + right; intros ?; hsimpl in *; destruct MQ'; attac.
      + destruct (lock state0) as [n1|] eqn:?.
        2: right; intros Hx; hsimpl in *; bullshit.
        destruct (NAME.eq_dec (init p) (self state0)).
        2: right; intros Hx; hsimpl in *; bullshit.
        destruct (PeanoNat.Nat.eq_dec (index p) (lock_id state0)).
        2: right; intros Hx; hsimpl in *; bullshit.
        hsimpl in * |-.

        destruct (NChan_eq_dec n0 (n, Q)); subst.
        * destruct IHMQ.
          -- left.
             hsimpl in * |- .
             exists (TrRecv (n, Q) v :: MQ'), MQ'', n', v0.
             eattac.
          -- left.
             exists [], MQ, n1, v.
             attac.
        * destruct IHMQ.
          -- hsimpl in * |- .
             destruct (NChan_eq_dec n0 (n', R)).
             ++ right.
                intros Hx; hsimpl in Hx.
                destruct MQ'0; kill Hx4.
                specialize (Hx v). bullshit.
             ++ left.
                exists (TrRecv n0 v :: MQ'), MQ'', n', v0.
                eattac.
          -- hsimpl in * |- .
             right; intros Hx; apply H; clear H; hsimpl in * |-.
             destruct MQ'; kill Hx4.
             exists MQ', MQ'', n', v0.
             hsimpl in * |-.
             repeat split; auto.
             intros ? ?.
             specialize (Hx v1). bullshit.
      + destruct IHMQ.
        * hsimpl in * |- .
          left.
          exists (EvRecv n0 m :: MQ'), MQ'', n', v. eattac.
        * right.
          intros Hx; apply H; clear H; hsimpl in * |-.
          destruct MQ'; kill Hx4.
          hsimpl in * |-.
          exists (MQ'), MQ'', n', v.
          eattac.
          specialize (Hx v0). eapply Hx. eattac.

    - destruct (lock state0) as [n0|] eqn:?.
      2: right; intros Hx; hsimpl in *; bullshit.
      destruct (NAME.eq_dec (init p) (self state0)) as [|Heqi].
      1: right; intros Hx; hsimpl in *; bullshit.

      pose (my_prop :=
              fun MQ => NoRecvR_from n0 MQ
                        /\ NoSends_MQ MQ
                        /\ (List.In n (waitees state0) \/ (exists v, List.In (TrRecv (n, Q) v) MQ))
                        /\ exists MQ', MQ = MQ' ++ [(EvRecv (n0, R) p)]
           ).

      assert (forall MQ, my_prop MQ \/ ~ my_prop MQ) as my_prop_dec.
      {
        clear.
        subst my_prop.
        intros.
        simpl in *.
        destruct (NoRecvR_from_dec n0 MQ).
        2: right; intros Hx; hsimpl in *; bullshit.
        destruct (NoSends_dec MQ).
        2: right; intros Hx; hsimpl in *; bullshit.

        assert (forall T (l : list T), l = [] \/ exists l' a, l = l' ++ [a]) as snoc_inv.
        {
          clear. induction l; attac. destruct IHl; attac. exists [], a; attac.
        }
        specialize (snoc_inv _ MQ) as [|]; hsimpl in *.
        1: right; intros Hx; hsimpl in *; bullshit.
        destruct a; subst; doubt.
        1: right; intros Hx; hsimpl in *; apply app_inj_tail in Hx3; attac.
        destruct (NChan_eq_dec n1 (n0, R)); subst.
        2: {right; intros Hx; eapply `(n1 <> (n0, R)); hsimpl in *; apply app_inj_tail in Hx3; attac.
        }
        destruct (MProbe_eq_dec m p); subst.
        2: {right; intros Hx; eapply `(m <> p); hsimpl in *; apply app_inj_tail in Hx3; attac.
        }
        destruct (in_dec NAME.eq_dec n (waitees state0)).
        1: { left. repeat split; eauto; eattac. }
        assert ((exists v, List.In (TrRecv (n, Q) v) (l' ++ [EvRecv (n0, R) p])) \/ ~ (exists v, List.In (TrRecv (n, Q) v) (l' ++ [EvRecv (n0, R) p]))) as [|].
        {
          clear.
          generalize (l' ++ [EvRecv (n0, R) p]); intros.
          induction l.
          1: right; intros ?; attac.
          destruct IHl; hsimpl in *; eattac.
          destruct a as [[? ?] ?|[? [|]] ?| [? ?] ?].
          all: try (solve [right; attac]).
          smash_eq n n1.
          - left; exists v; attac.
          - right; attac.
        }
        - left; eattac.
          specialize (H v).
          hsimpl in *. bullshit.
        - right; eattac.
      }

      specialize (wtf' MQ my_prop my_prop_dec) as [|].
      + subst my_prop.
        hsimpl in *.
        left.
        exists MQ', l1, n0.
        eattac.
        specialize (H0 v).
        eapply `(~ _).
        attac.
      + right.
        intros ?; apply H; subst my_prop; hsimpl in *.
        exists (MQ' ++ [EvRecv (n', R) p]), MQ''.
        eattac.
        destruct `(_ \/ _); attac.
  Qed.


  Lemma net_lock_on_M_no_sends_in [n n' MN] :
    net_lock_on '' MN n n' ->
    no_sends_in n MN.
  Proof.
    intros.
    unfold no_sends_in, NoTrSend, net_lock_on, net_lock in *.
    unfold net_deinstr in *.
    ltac1:(autorewrite with LTS in * ).
    hsimpl in *.
    destruct (NetMod.get n MN) as [MQ0 M0 [I0 P0 O0]].
    apply Forall_forall.
    intros.
    destruct x; auto.
    destruct (deinstr (mq MQ0 M0 (pq I0 P0 O0))) as [I' P' O'] eqn:?.
    absurd (List.In (n0, v) O').
    - intros ?.
      unfold deinstr in *.
      hsimpl in *.
      kill H0.
      assert (MQ_s l = [] /\ O0 = []) by eauto using app_eq_nil.
      attac.
      (* TODO TO LEMMA *)
      clear - H0 H1.
      induction l; attac.
      destruct a; attac.
    - assert (deinstr (mq l m p) = pq I' P' O') by attac.
      eapply (deinstr_In_send `(List.In _ l)). attac.
  Qed.


  Lemma locked_M_no_send [MN0 MN1 : MNet] [n0 n1] [m0 m1 v t] :
    net_lock_on '' MN0 n0 n1 ->
    (MN0 =(NComm m0 m1 t (MValP v))=> MN1) ->
    n0 <> m0.

  Proof.
    intros.
    intros ?; subst.
    assert (no_sends_in m0 MN0) by eauto using net_lock_on_M_no_sends_in.
    unfold net_lock_on, net_lock, no_sends_in, NoTrSend in *.
    kill H0.
    hsimpl in *.
    bullshit.
  Qed.


  Lemma dep_self_deadlocked [N n] :
    net_sane N ->
    dep_on N n n -> deadlocked n N.

  Proof.
    intros.
    eapply dep_self_deadset; eauto with LTS.
  Qed.


  (* Lemma net_dep_open [N0 N1 a n0 n1] : *)
  (*   net_sane '' N0 -> *)
  (*   (N0 =(a)=> N1) -> *)
  (*   dep_on '' N0 n0 n1 -> *)
  (*   ~ dep_on '' N1 n0 n1 -> (* TODO relation between m1 and n1 *) *)
  (*   exists m0 m1 v, (n0 = m0 \/ dep_on '' N0 n0 m0) /\ a = NComm m1 m0 R v. *)


  (* Lemma SRPC_net_unlock_uniq [N0 N1 : PNet] [na] [n0 n1 m0 m1] : *)
  (*   net_sane '' N0 -> *)
  (*   (N0 =(na)=> N1) -> *)
  (*   net_lock_on N0 n0 n1 -> *)
  (*   ~ net_lock_on N1 n0 n1 -> *)
  (*   net_lock_on N0 m0 m1 -> *)
  (*   ~ net_lock_on N1 m0 m1 -> *)
  (*   n0 = m0 /\ n1 = m1. *)

  (* Proof. *)
  (*   intros. *)
  (*   assert (exists v', na = NComm m1 m0 R v') by eauto using SRPC_net_unlock_reply. *)
  (*   assert (exists v', na = NComm n1 n0 R v') by eauto using SRPC_net_unlock_reply. *)
  (*   hsimpl in *. *)
  (*   auto. *)
  (* Qed. *)


  Lemma net_sane_lock_chain_dec (N : PNet) n0 L n1 :
    net_sane N ->
    lock_chain N n0 L n1 \/ ~ lock_chain N n0 L n1.

  Proof.
    intros.
    generalize dependent n0.
    induction L; intros; hsimpl in *.
    1: eauto using net_sane_lock_dec with LTS.

    rename a into n0'.
    assert (net_lock_on N n0 n0' \/ ~ net_lock_on N n0 n0') as [|]
        by eauto using net_sane_lock_dec with LTS.

    - specialize (IHL n0') as [|]; attac.
      right; attac.
    - right; attac.
  Qed.


  (* Lemma lock_chain_no_immediate_relock [N0 N1] [na] [n0 n1] [L] : *)
  (*   net_sane N0 -> *)
  (*   (N0 =(na)=> N1) -> *)
  (*   lock_chain N0 n0 L n1 -> *)
  (*   (lock_chain N1 n0 L n1 \/ ~ dep_on N1 n0 n1). *)

  (* Proof. *)
  (*   intros. *)
  (*   generalize dependent n0. *)
  (*   induction L; intros; hsimpl in *. *)
  (*   - destruct (net_sane_lock_dec N1 n0 n1); eauto 2 with LTS. *)
  (*     right; intros ?. *)
  (*     consider (dep_on _ _ _). *)
  (*     consider (n2 = n1) by eauto using SRPC_net_no_relock, eq_sym with LTS. *)
  (*   - rename a into n0'. *)

  (*     smash_eq n0 n0'. *)
  (*     { *)
  (*       assert (deadlocked n0 N0) by (eapply dep_self_deadlocked; eauto with LTS). *)
  (*       assert (net_lock_on N1 n0 n0) by eauto 3 with LTS. *)
  (*       left; constructor; eauto. *)
  (*       clear - H3 H2 H0 H. *)
  (*       generalize dependent n0. *)
  (*       induction L; intros; hsimpl in *; eauto 3 with LTS. *)

  (*       rename a into n0'. *)
  (*       constructor; eauto 3 with LTS. *)
  (*     } *)

  (*     specialize (IHL n0' ltac:(auto)) as [|]. *)
  (*     + destruct (net_sane_lock_dec N1 n0 n0'); eauto 3 with LTS. *)
  (*       right; intros ?. *)
  (*       consider (dep_on N1 _ _). *)
  (*       * consider (n0' = n1) by eauto using SRPC_net_no_immediate_relock, eq_sym with LTS. *)
  (*       * consider (n0' = n2) by eauto using SRPC_net_no_immediate_relock, eq_sym with LTS. *)
  (*     + destruct (net_sane_lock_dec N1 n0 n0'); eauto 2 with LTS. *)
  (*       * right; intros ?. *)
  (*         consider (dep_on N1 _ _). *)
  (*         -- consider (n0' = n1) by eauto using lock_uniq with LTS. *)
  (*            absurd (dep_on N1 n1 n1); eauto 2 with LTS. *)
  (*            enough (deadlocked n1 N0); eauto 3 using dep_self_deadlocked with LTS. *)
  (*         -- consider (n0' = n2) by eauto using lock_uniq with LTS. *)
  (*       * right; intros ?. *)

  (*         consider (dep_on N1 _ _). *)
  (*         -- consider (n0' = n1) by eauto using SRPC_net_no_immediate_relock, eq_sym with LTS. *)
  (*         -- consider (n0' = n2) by eauto using SRPC_net_no_immediate_relock, eq_sym with LTS. *)
  (* Qed. *)


  (* Lemma lock_chain_no_immediate_relock_dep [N0 N1] [na] [n0 n1] [L] : *)
  (*   net_sane '' N0 -> *)
  (*   (N0 =(na)=> N1) -> *)
  (*   lock_chain N0 n0 L n1 -> *)
  (*   dep_on N1 n0 n1 -> *)
  (*   lock_chain N1 n0 L n1. *)

  (* Proof. *)
  (*   intros. *)
  (*   assert (lock_chain N1 n0 L n1 \/ ~ dep_on N1 n0 n1) as [|] *)
  (*       by eauto using lock_chain_no_immediate_relock; *)
  (*     attac. *)
  (* Qed. *)


  (* Lemma lock_chain_dup_alarm [N] [n0 n1] [L] : *)
  (*   net_sane '' N -> *)
  (*   ~ NoDup L -> *)
  (*   lock_chain N n0 L n1 -> *)
  (*   deadlocked n0 N. *)

  (* Proof. *)
  (*   intros. *)

  (*   enough (deadlocked n1 N) by eauto 4 with LTS. *)

  (*   generalize dependent n0. *)
  (*   induction L; intros. *)
  (*   1: absurd (@NoDup Name []); eauto; constructor. *)

  (*   rename a into n0'. *)
  (*   hsimpl in *. *)
  (*   normalize_hyp @IHL. *)

  (*   destruct (in_dec NAME.eq_dec n0' L). *)
  (*   - consider (exists L0 L1, *)
  (*       L = L0 ++ n0' :: L1 *)
  (*       /\ lock_chain N n0' L0 n0' *)
  (*       /\ lock_chain N n0' L1 n1) by eauto using lock_chain_split_in. *)
  (*     eauto 3 using dep_self_deadlocked with LTS. *)
  (*   - apply (IHL n0'); auto. *)
  (*     intros ?. *)
  (*     apply `(~ NoDup _). *)
  (*     constructor; attac. *)
  (* Qed. *)


  (* Lemma unlock_dependency [N0 N1] [na] [n0 n1 n2] : *)
  (*   net_sane '' N0 -> *)
  (*   (N0 =(na)=> N1) -> *)
  (*   net_lock_on N0 n0 n1 -> *)
  (*   net_lock_on N0 n1 n2 -> *)
  (*   net_lock_on N1 n0 n1. *)

  (* Proof. *)
  (*   intros. *)
  (*   destruct (net_sane_lock_dec N1 n0 n1); eauto 2 with LTS. *)
  (*   consider (exists v, na = NComm n1 n0 R v) by eauto using SRPC_net_unlock_reply. *)
  (*   exfalso. *)
  (*   consider (_ =(_)=> _); hsimpl in *. *)
  (*   apply lock_singleton in H2. 2: attac. *)
  (*   unfold net_lock in *. *)
  (*   compat_hsimpl in *. *)
  (*   bullshit. *)
  (* Qed. *)


  (* Lemma unlock_dependency_dep [N0 N1] [na] [n0 n1 n2] : *)
  (*   net_sane '' N0 -> *)
  (*   (N0 =(na)=> N1) -> *)
  (*   net_lock_on N0 n0 n1 -> *)
  (*   dep_on N0 n1 n2 -> *)
  (*   net_lock_on N1 n0 n1. *)

  (* Proof. *)
  (*   intros. *)
  (*   consider (dep_on _ _ _); eauto using unlock_dependency. *)
  (* Qed. *)


  (* Lemma lock_chain_unlock_tip [N0 N1] [na] [n0 n1] [L] : *)
  (*   net_sane '' N0 -> *)
  (*   (N0 =(na)=> N1) -> *)
  (*   lock_chain N0 n0 L n1 -> *)
  (*   ~ lock_chain N1 n0 L n1 -> *)
  (*   exists n1' v, na = NComm n1 n1' R v *)
  (*            /\ ((n1' = n0 /\ L = []) \/ exists L', L = L' ++ [n1']). *)

  (* Proof. *)
  (*   intros. *)

  (*   generalize dependent n0 n1. *)
  (*   induction L; intros; hsimpl in *. *)
  (*   1: consider (exists v, na = NComm n1 n0 R v) by eauto using SRPC_net_unlock_reply; exists n0, v; eattac. *)

  (*   rename a into n0'. *)

  (*   assert (net_lock_on N1 n0 n0') by eauto 2 using unlock_dependency_dep with LTS. *)
  (*   assert (~ lock_chain N1 n0' L n1) by eattac. clear H2. *)

  (*   specialize (IHL n1 n0' ltac:(auto) ltac:(auto)). *)
  (*   hsimpl in IHL. *)
  (*   destruct `(_ \/ _); hsimpl in *. *)
  (*   - hsimpl in *. *)
  (*     exists n0', v. eattac. *)
  (*   - hsimpl in *. *)
  (*     exists n1', v. *)
  (*     eattac. *)
  (* Qed. *)


  Lemma lock_chain_connect [N0 N1] [na] [n0 n1] [L] :
    net_sane N0 ->
    (N0 =(na)=> N1) ->
    ~ List.In n1 L ->
    NoDup L ->
    ~ lock_chain N0 n0 L n1 ->
    lock_chain N1 n0 L n1 ->
    exists m0 m1 v, na = NComm m0 m1 Q v
                    /\ ((m0 = n0 /\ m1 = n1 /\ L = [])
                        \/ (m0 = n0 /\ m1 <> n1 /\ exists L1, L = m1 :: L1 /\ lock_chain N0 m1 L1 n1)
                        \/ (m0 <> n0 /\ m1 = n1 /\ exists L0, L = L0 ++ [m0] /\ lock_chain N0 n0 L0 m0)
                        \/ (exists L0 L1, L = L0 ++ [m0;m1] ++ L1 /\ lock_chain N0 n0 L0 m0  /\ lock_chain N0 m1 L1 n1)
                       ).

  Proof.
    intros.

    generalize dependent n0 n1.
    induction L; intros; hsimpl in *.
    1: consider (exists v, na = NComm n0 n1 Q v) by eauto using net_sane_new_lock_send_Q; eattac.

    rename a into n0'.

    smash_eq n0 n0'.
    {
      consider (n0 = n1).
      {
        enough (Forall (eq n0) L /\ n1 = n0) as Hx. 1: destruct Hx; eauto.
        eauto using lock_self_lock_chain_uniq with LTS.
      }
      bullshit.
    }

    assert (net_sane N1) by attac.

    destruct (net_sane_lock_dec N0 n0 n0'); eauto 2 with LTS.
    - assert (~ lock_chain N0 n0' L n1) by eattac.

      kill H2. (* TODO autorewrite NoDup *)
      normalize_hyp @IHL.
      specialize (IHL n1 n0').
      repeat (specialize (IHL ltac:(auto))).
      hsimpl in IHL.
      destruct `(_ \/ _) as [|[|[|]]]; hsimpl in *; hsimpl in *; eexists _,_,_; split; eauto.
      + do 2 right. left; eattac.
      + do 3 right.
        (* split; eauto. split; eauto. *)
        exists []; eattac.
      + assert (~ net_lock_on N0 m0 n1) by attac.
        smash_eq m0 n0.
        2: right; right; left; eattac.
        consider (n0' = n1) by (eapply SRPC_net_lock_uniq; eauto with LTS).
        bullshit.
      + smash_eq m0 n0.
        2: right; right; right; repeat split; auto; eattac.
        consider (n0' = m1) by (eapply SRPC_net_lock_uniq; eauto with LTS).
        bullshit.
    - consider (exists v, na = NComm n0 n0' Q v) by eauto using net_sane_new_lock_send_Q.
      eexists _,_,_; split; eauto.

      (* remember (NComm _ _ _ _) as a. clear Heqa. *)

      destruct (net_sane_lock_chain_dec N0 n0' L n1); eauto 2 with LTS.
      + smash_eq n0' n1.
        right; left; repeat split; auto; exists L; split; auto.

      + kill H2.
        normalize_hyp @IHL.
        specialize (IHL n1 n0').
        repeat (specialize (IHL ltac:(auto))).
        hsimpl in IHL.
        repeat (destruct `(_ \/ _) as [|]); hsimpl in IHL0; attac.
        exfalso.
        hsimpl in *.
        bullshit (List.In m1 (L0 ++ m0 :: m1 :: L1)).
  Qed.


  (* Lemma lock_chain_connect' [N0 N1] [na] [n0 n1] [L] : *)
  (*   net_sane '' N0 -> *)
  (*   (N0 =(na)=> N1) -> *)
  (*   ~ lock_chain N0 n0 L n1 -> *)
  (*   lock_chain N1 n0 L n1 -> *)
  (*   exists m0 m1 v, na = NComm m0 m1 Q v *)
  (*              /\ ((m0 = n0 /\ m1 = n1 /\ L = []) *)
  (*                 \/ (m0 = n0 /\ exists L1, L = m1 :: L1) *)
  (*                 \/ (m1 = n1 /\ exists L0, L = L0 ++ [m0]) *)
  (*                 \/ exists L0 L1, L = L0 ++ [m0;m1] ++ L1 *)
  (*                ). *)

  (* Proof. *)
  (*   intros. *)

  (*   generalize dependent n0 n1. *)
  (*   induction L; intros; hsimpl in *. *)
  (*   1: consider (exists v, na = NComm n0 n1 Q v) by eauto using SRPC_net_new_lock_query; eattac. *)

  (*   rename a into n0'. *)

  (*   destruct (net_sane_lock_dec N0 n0 n0'); eauto 2 with LTS. *)
  (*   - assert (~ lock_chain N0 n0' L n1) by eattac. *)
  (*     specialize (IHL n1 n0' ltac:(auto) ltac:(auto)). *)
  (*     hsimpl in IHL. *)
  (*     destruct `(_ \/ _) as [|[|[|]]]; hsimpl in *; hsimpl in *; eexists _,_,_; split; eauto. *)
  (*     + do 2 right; eattac. *)
  (*     + do 3 right. *)
  (*       exists []; eattac. *)
  (*     + do 2 right; left; eattac. *)
  (*     + do 3 right. *)
  (*       exists (n0'::L0); eattac. *)
  (*   - consider (exists v, na = NComm n0 n0' Q v) by eauto using SRPC_net_new_lock_query. *)
  (*     eexists _,_,_; split; eauto. *)
  (* Qed. *)


  (* Lemma lock_chain_no_immediate_relock_dep' [N0 N1] [na] [n0 n1] [L] : *)
  (*   net_sane '' N0 -> *)
  (*   (N0 =(na)=> N1) -> *)
  (*   dep_on N0 n0 n1 -> *)
  (*   lock_chain N1 n0 L n1 -> *)
  (*   lock_chain N0 n0 L n1 \/ dep_on N1 n1 n1. *)

  (* Proof. *)
  (*   intros. *)

  (*   apply dep_lock_chain in H1. *)
  (*   hsimpl in *. *)
  (*   assert (dep_on N1 n0 n1) by eauto with LTS. *)
  (*   assert (lock_chain N1 n0 L0 n1) by eauto using lock_chain_no_immediate_relock_dep. *)

  (*   assert (lock_chain N1 n0 L n1 \/ ~ dep_on N1 n0 n1) as [|] *)
  (*       by eauto using lock_chain_no_immediate_relock; *)
  (*     attac. *)

  (*   (* assert (lock_chain N0 n0 L n1 \/ ~ lock_chain N0 n0 L n1) as [|] *) *)
  (*   (*     by eauto using net_sane_lock_chain_dec; auto. *) *)

  (*   consider (exists L', L0 = L ++ L' \/ L = L0 ++ L') by eauto using lock_chain_prefix with LTS. *)
  (*   destruct `(_ \/ _); subst. *)
  (*   - destruct L'. 1: attac. *)
  (*     absurd (n = n1); attac. *)
  (*   - destruct L'. 1: attac. *)
  (*     consider (n = n1) by attac. *)
  (*     hsimpl in *. *)

  (*     assert (lock_chain N0 n1 L' n1 \/ ~ lock_chain N0 n1 L' n1) as [|] *)
  (*         by eauto using net_sane_lock_chain_dec with LTS; auto. *)

  (*     1: left; apply lock_chain_seq; auto. *)

  (*     eauto with LTS. *)
  (* Qed. *)


  (* Lemma lock_chain_unlock_in [N0 N1] [na] [n0 n1] [L] : *)
  (*   net_sane '' N0 -> *)
  (*   (N0 =(na)=> N1) -> *)
  (*   lock_chain N0 n0 L n1 -> *)
  (*   ~ dep_on N1 n0 n1 -> *)
  (*   exists m0 m1 v, na = NComm m1 m0 R v *)
  (*              /\ (m0 = n0 \/ List.In m0 L) *)
  (*              /\ (m1 = n1 \/ List.In m1 L). *)

  (* Proof. *)
  (*   intros. *)

  (*   assert (~ lock_chain N1 n0 L n1) by eattac. *)

  (*   consider (exists n1' v, na = NComm n1 n1' R v *)
  (*                    /\ ((n1' = n0 /\ L = []) \/ exists L', L = L' ++ [n1'])) *)
  (*     by eauto using lock_chain_unlock_tip. *)

  (*   eexists _,_,_; split; eauto. *)
  (*   destruct `(_ \/ _); attac. *)
  (* Qed. *)


  (* Lemma SRPC_net_unlock_uniq_dep [N0 N1 : PNet] [na] [n0 n1 m0 m1] : *)
  (*   net_sane '' N0 -> *)
  (*   (N0 =(na)=> N1) -> *)
  (*   net_lock_on N0 n0 n1 -> *)
  (*   ~ net_lock_on N1 n0 n1 -> *)
  (*   dep_on N0 m0 m1 -> *)
  (*   ~ dep_on N1 m0 m1 -> *)
  (*   (m0 = n0 \/ (dep_on N0 m0 n0 /\ dep_on N1 m0 n0)) /\ m1 = n1. *)

  (* Proof. *)
  (*   intros. *)

  (*   smash_eq n0 n1. *)
  (*   { *)
  (*     assert (deadlocked n0 N0) by eauto using dep_self_deadlocked with LTS. *)
  (*     bullshit (net_lock_on N1 n0 n0). *)
  (*   } *)

  (*   apply dep_lock_chain in H3 as [L' [? ?]]. *)
  (*   consider (exists L, *)
  (*       lock_chain N0 m0 L m1 *)
  (*       /\ NoDup L *)
  (*       /\ not (List.In m0 L) *)
  (*       /\ not (List.In m1 L)) by eauto using lock_chain_dedup. *)
  (*   clear L' H3 H5. *)

  (*   assert (~ lock_chain N1 m0 L m1) by attac. *)
  (*   assert (exists m1' v, na = NComm m1 m1' R v *)
  (*                    /\ ((m1' = m0 /\ L = []) \/ exists L', L = L' ++ [m1'])) *)
  (*     by eauto using lock_chain_unlock_tip with LTS. *)
  (*   strip_exists @H5. *)
  (*   destruct H5. *)
  (*   destruct H10; hsimpl in *. *)
  (*   - consider (n0 = m0 /\ n1 = m1) by eauto using SRPC_net_unlock_uniq with LTS. *)
  (*   - consider (net_lock_on N0 m1' m1 /\ ~ net_lock_on N1 m1' m1) by eauto using SRPC_net_reply_unlock with LTS. *)
  (*     apply NoDup_remove_2 in H7. *)
  (*     consider (n0 = m1' /\ n1 = m1) by eauto using SRPC_net_unlock_uniq with LTS. *)
  (*     apply HAVE_ in H0. *)
  (*     hsimpl in *. *)

  (*     repeat (match! goal with *)
  (*             | [_ : ?a0, h1 : ?a1 |- _] => *)
  (*                    if Constr.equal (eval cbv in $a0) (eval cbv in $a1) *)
  (*                    then clear $h1 else fail *)
  (*             | [h : ?t |- _] => *)
  (*                 clear $h; *)
  (*                 assert $t as $h by (repeat (intros Hx; kill Hx); eauto 2 with LTS); *)
  (*                 clear $h *)
  (*             end). *)

  (*     split; eauto. *)
  (*     split; eauto 2 with LTS. *)
  (*     destruct (net_sane_lock_chain_dec N1 m0 L' m1'); (re_have eauto 2 with LTS). *)

  (*     assert (exists m1'' v', NComm m1 m1' R v = NComm m1' m1'' R v' *)
  (*                        /\ ((m1'' = m0 /\ L' = []) \/ exists L'', L' = L'' ++ [m1''])) *)
  (*       by (re_have eauto using lock_chain_unlock_tip with LTS). *)
  (*     strip_exists @H5. *)
  (*     destruct H5; hsimpl in H5. (* TODO performance *) *)
  (*     destruct `(_ \/ _); bullshit. *)
  (* Qed. *)


  Lemma net_dep_close [N0 N1 na n0 n1] :
    net_sane N0 ->
    (N0 =(na)=> N1) ->
    ~ dep_on N0 n0 n1 ->
    dep_on N1 n0 n1 ->
    exists m0 m1 v, na = NComm m0 m1 Q v
                    /\ (m0 = n0 \/ (m0 <> n0 /\ dep_on N0 n0 m0 /\ dep_on N1 n0 m0))
                    /\ (m1 = n1 \/ (m1 <> n1 /\ dep_on N0 m1 n1 /\ dep_on N1 m1 n1)).

  Proof.
    intros.
    consider (
        exists L,
          lock_chain N1 n0 L n1
          /\ NoDup L
          /\ not (List.In n0 L)
          /\ not (List.In n1 L)).
    {
      apply dep_lock_chain in H2 as [? [? ?]].
      eauto using lock_chain_dedup with LTS.
    }
    clear H2.

    consider (exists m0 m1 v, na = NComm m0 m1 Q v
                              /\ ((m0 = n0 /\ m1 = n1 /\ L = [])
                                  \/ (m0 = n0 /\ m1 <> n1 /\ exists L1, L = m1 :: L1 /\ lock_chain N0 m1 L1 n1)
                                  \/ (m0 <> n0 /\ m1 = n1 /\ exists L0, L = L0 ++ [m0] /\ lock_chain N0 n0 L0 m0)
                                  \/ (exists L0 L1, L = L0 ++ [m0;m1] ++ L1 /\ lock_chain N0 n0 L0 m0  /\ lock_chain N0 m1 L1 n1)
             )) by eauto using lock_chain_connect with LTS.

    destruct `(_ \/ _) as [|[|[|]]]; hsimpl in *;
      eexists _,_,_; split; eauto; split; try (solve [left; eauto]); right; eattac.
  Qed.


  Lemma net_M_dep_close [N0 N1 : MNet] [na n0 n1] :
    net_sane '' N0 ->
    (N0 =(na)=> N1) ->
    ~ dep_on '' N0 n0 n1 ->
    dep_on '' N1 n0 n1 ->
    exists m0 m1 v, na = NComm m0 m1 Q (MValP v)
                    /\ (m0 = n0 \/ (m0 <> n0 /\ dep_on '' N0 n0 m0 /\ dep_on '' N1 n0 m0))
                    /\ (m1 = n1 \/ (m1 <> n1 /\ dep_on '' N0 m1 n1 /\ dep_on '' N1 m1 n1)).

  Proof.
    intros.
    destruct (MNAct_to_PNAct na) eqn:?.
    - assert ('' N0 =(p)=> '' N1) by eauto using net_deinstr_act_do.
      consider (exists m0 m1 v, p = @NComm PAct _ m0 m1 Q v
                                /\ (m0 = n0 \/ (m0 <> n0 /\ dep_on '' N0 n0 m0 /\ dep_on '' N1 n0 m0))
                                /\ (m1 = n1 \/ (m1 <> n1 /\ dep_on '' N0 m1 n1 /\ dep_on '' N1 m1 n1))
               )
        by eauto using net_dep_close with LTS.

      exists m0, m1, v.
      destruct na.
      + destruct m.
        destruct p; bullshit.
        destruct p; bullshit.
        destruct a; bullshit.
      + destruct p; doubt.
        attac.
    - assert ('' N0 = '' N1) by eauto using net_deinstr_act_skip.
      rewrite `('' N0 = _) in *.
      bullshit.
  Qed.


  Lemma SRPC_net_new_lock_no_unlock [N0 N1 : PNet] [na] [n0 n1 m0 m1] :
    net_sane N0 ->
    (N0 =(na)=> N1) ->
    ~ net_lock_on N0 n0 n1 ->
    net_lock_on N1 n0 n1 ->
    net_lock_on N0 m0 m1 ->
    net_lock_on N1 m0 m1.

  Proof.
    intros.

    assert (net_lock_on N1 m0 m1 \/ ~ net_lock_on N1 m0 m1) as [|]
        by eauto using net_sane_lock_dec with LTS.
    1: auto.

    assert (exists v', na = NComm n0 n1 Q v') by eauto using net_sane_new_lock_send_Q.
    assert (exists v', na = NComm m1 m0 R v') by (eapply net_unlock_on_reply; eauto with LTS).
    hsimpl in *.
    bullshit.
  Qed.


  Lemma SRPC_net_new_lock_no_unlock_dep [N0 N1 : PNet] [na] [n0 n1 m0 m1] :
    net_sane N0 ->
    (N0 =(na)=> N1) ->
    ~ net_lock_on N0 n0 n1 ->
    net_lock_on N1 n0 n1 ->
    dep_on N0 m0 m1 ->
    dep_on N1 m0 m1.

  Proof.
    intros.
    apply dep_lock_chain in H3.
    hsimpl in *.
    generalize dependent m0.
    induction L; intros; hsimpl in *.
    1: enough (net_lock_on N1 m0 m1); eauto using SRPC_net_new_lock_no_unlock with LTS.

    rename a into m0'.
    specialize (IHL ltac:(auto) m0' ltac:(auto)).
    enough (net_lock_on N1 m0 m0'); eauto 3 using SRPC_net_new_lock_no_unlock with LTS.
  Qed.


  (* Lemma SRPC_net_unlock_no_new_lock [N0 N1 : PNet] [na] [n0 n1 m0 m1] : *)
  (*   net_sane '' N0 -> *)
  (*   (N0 =(na)=> N1) -> *)
  (*   net_lock_on N0 n0 n1 -> *)
  (*   ~ net_lock_on N1 n0 n1 -> *)
  (*   ~ net_lock_on N0 m0 m1 -> *)
  (*   ~ net_lock_on N1 m0 m1. *)

  (* Proof. *)
  (*   intros. intros ?. *)
  (*   assert (exists v', na = NComm n1 n0 R v') by eauto using SRPC_net_unlock_reply. *)
  (*   assert (exists v', na = NComm m0 m1 Q v') by eauto using SRPC_net_new_lock_query. *)
  (*   hsimpl in *. *)
  (*   bullshit. *)
  (* Qed. *)


  (* Lemma SRPC_net_unlock_no_new_dep [N0 N1 : PNet] [na] [n0 n1 m0 m1] : *)
  (*   net_sane '' N0 -> *)
  (*   (N0 =(na)=> N1) -> *)
  (*   net_lock_on N0 n0 n1 -> *)
  (*   ~ net_lock_on N1 n0 n1 -> *)
  (*   ~ dep_on N0 m0 m1 -> *)
  (*   ~ dep_on N1 m0 m1. *)

  (* Proof. *)
  (*   intros; intros ?. *)
  (*   apply dep_lock_chain in H4. *)
  (*   hsimpl in *. *)
  (*   generalize dependent m0. *)
  (*   induction L; intros; hsimpl in *. *)
  (*   - assert (~ net_lock_on N0 m0 m1) by (intros ?; apply `(~ dep_on N0 m0 m1); bullshit). *)
  (*     absurd (net_lock_on N1 m0 m1); eauto using SRPC_net_unlock_no_new_lock with LTS. *)

  (*   - rename a into m0'. *)
  (*     destruct (net_sane_lock_dec N0 m0 m0'); auto; doubt. *)
  (*     absurd (net_lock_on N1 m0 m0'); eauto using SRPC_net_unlock_no_new_lock with LTS. *)
  (* Qed. *)


  (* (* TODO TO LOCKS *) *)
  (* Lemma lock_no_dep_refute [N] [n0 n1 n2] : *)
  (*   (forall n, AnySRPC_pq (NetMod.get n N)) -> *)
  (*   n1 <> n2 -> *)
  (*   net_lock_on N n0 n1 -> *)
  (*   ~ dep_on N n1 n2 -> *)
  (*   ~ dep_on N n0 n2. *)

  (* Proof. *)
  (*   intros. *)
  (*   intros ?; apply `(~ dep_on _ _ _). *)
  (*   clear H2. *)
  (*   consider (dep_on N n0 n2). *)
  (*   - bullshit (n1 = n2). *)
  (*   - assert (n1 = n3) by eauto with LTS. (* TODO consider doesn't subst here *) *)
  (*     (* hsimpl in H3. (* TODO THIS doesn't subst *) *) *)
  (*     compat_hsimpl in H3. *)
  (*     eauto using dep_on_seq with LTS. *)
  (* Qed. *)


  (* Lemma lock_no_dep_refute' [N] [n0 n1 n2] : *)
  (*   (forall n, AnySRPC_pq (NetMod.get n N)) -> *)
  (*   net_lock_on N n0 n1 -> *)
  (*   ~ dep_on N n0 n2 -> *)
  (*   ~ dep_on N n1 n2. *)

  (* Proof. *)
  (*   intros. *)
  (*   intros ?; apply `(~ dep_on _ _ _). *)
  (*   eauto with LTS. *)
  (* Qed. *)


  Lemma invariant_dep_dec1 [N0 N1 : PNet] [a] :
    net_sane N0 ->
    (N0 =(a)=> N1) ->
    (forall n0 n1, dep_on N0 n0 n1 \/ ~ dep_on N0 n0 n1) ->
    (forall n0 n1, dep_on N1 n0 n1 \/ ~ dep_on N1 n0 n1).

  Proof.
    intros.
    assert (net_sane N1) by attac.

    destruct `(dep_on N0 n0 n1 \/ ~ dep_on N0 n0 n1).
    - apply dep_lock_chain in H3. hsimpl in *.
      generalize dependent n0.
      induction L; intros; hsimpl in *.
      + assert (net_lock_on N1 n0 n1 \/ ~ net_lock_on N1 n0 n1)
          as [|] by eauto using net_sane_lock_dec with LTS.
        1: eattac.

        right; intros Hx.
        consider (dep_on N1 n0 n1).
        bullshit (n1 = n2) by (eauto using SRPC_net_no_relock with LTS).
      + rename a0 into n0'.
        specialize (IHL ltac:(auto) n0' ltac:(auto)).

        smash_eq n0 n0'; eauto.
        smash_eq n0 n1.
        {
          left.
          assert (deadlocked n0 N0) by (eapply dep_self_deadlocked; eauto with LTS).
          eauto 3 with LTS.
        }

        destruct IHL as [|].
        * assert (net_lock_on N1 n0 n0' \/ ~ net_lock_on N1 n0 n0')
            as [|] by eauto using net_sane_lock_dec with LTS.
          -- left; eauto 3 with LTS.
          -- right.
             intros Hx.
             consider (dep_on N1 n0 n1).
             ++ assert (n0' = n1) by eauto 4 using SRPC_net_no_relock with LTS.
                bullshit.
             ++ assert (n0' = n2) by eauto 4 using SRPC_net_no_relock with LTS.
                bullshit.
        * right.
          assert (net_lock_on N1 n0 n0' \/ ~ net_lock_on N1 n0 n0')
            as [|] by eauto using net_sane_lock_dec with LTS.
          1: { intros ?.
               consider (dep_on N1 n0 n1).
               1: { bullshit (n1 = n0') by (eapply SRPC_net_lock_uniq; eauto with LTS). }
               consider (n2 = n0') by (eapply SRPC_net_lock_uniq; eauto with LTS).
          }

          intros ?.
          consider (dep_on N1 n0 n1).
          ++ assert (n0' = n1) by eauto 4 using SRPC_net_no_relock with LTS.
             bullshit.
          ++ assert (n0' = n2) by eauto 4 using SRPC_net_no_relock with LTS.
             bullshit.
    -
      assert ((exists m0 m1 v, a = @NComm PAct _ m0 m1 Q v) \/ ~ (exists m0 m1 v, a = @NComm PAct _ m0 m1 Q v)) as [|].
      {
        destruct a.
        - right; attac.
        - destruct &t.
          + left; eattac.
          + right; eattac.
      }
      + hsimpl in *.
        consider (~ net_lock_on N0 m0 m1 /\ net_lock_on N1 m0 m1) by eauto using SRPC_net_query_new_lock with LTS.
        remember (NComm _ _ _ _) as na; clear Heqna.
        destruct `(dep_on N0 n0 m0 \/ ~ dep_on N0 n0 m0).
        * assert (dep_on N1 n0 m0).
          {
            consider (exists v, na = NComm m0 m1 Q v) by eauto using net_sane_new_lock_send_Q with LTS.
            eauto using net_dep_Q_preserve.
          }
          destruct `(dep_on N0 m1 n1 \/ ~ dep_on N0 m1 n1).
          1: eauto 4 using SRPC_net_new_lock_no_unlock_dep with LTS.

          smash_eq m1 n1.
          1: eauto 3 with LTS.

          right; intros ?.

          assert (exists v', na = NComm m0 m1 Q v') by eauto using net_sane_new_lock_send_Q with LTS.
          assert (exists m0' m1' v', na = NComm m0' m1' Q v'
                                     /\ (m0' = n0 \/ (m0' <> n0 /\ dep_on N0 n0 m0' /\ dep_on N1 n0 m0'))
                                     /\ (m1' = n1 \/ (m1' <> n1 /\ dep_on N0 m1' n1 /\ dep_on N1 m1' n1)))
            by eauto using net_dep_close with LTS.

          hsimpl in H10.
          hsimpl in H11.
          remember (NComm _ _ _ _) as na; clear Heqna.
          destruct `(_ \/ _); subst.
          1: bullshit.
          hsimpl in H10.
          bullshit.
        * destruct `(dep_on N0 n0 m1 \/ ~ dep_on N0 n0 m1).
          -- assert (dep_on N1 n0 m1) by eauto 2 using SRPC_net_new_lock_no_unlock_dep with LTS.
             destruct `(dep_on N0 m1 n1 \/ ~ dep_on N0 m1 n1).
             1: eauto 4 using SRPC_net_new_lock_no_unlock_dep with LTS.

             smash_eq m1 n1.
             1: eauto 3 with LTS.

             right; intros ?.

             assert (exists v', na = NComm m0 m1 Q v') by eauto using net_sane_new_lock_send_Q with LTS.
             assert (exists m0' m1' v', na = NComm m0' m1' Q v'
                                        /\ (m0' = n0 \/ (m0' <> n0 /\ dep_on N0 n0 m0' /\ dep_on N1 n0 m0'))
                                        /\ (m1' = n1 \/ (m1' <> n1 /\ dep_on N0 m1' n1 /\ dep_on N1 m1' n1)))
               by eauto using net_dep_close with LTS.

             hsimpl in H11.
             hsimpl in H12.
             remember (NComm _ _ _ _) as na; clear Heqna.
             destruct `(_ \/ _); subst.
             1: bullshit.
             hsimpl in H11.
             bullshit.
          -- destruct (net_sane_lock_dec N0 n0 n1); eauto 4 using SRPC_net_new_lock_no_unlock with LTS.
             destruct (net_sane_lock_dec N1 n0 n1); eauto 2 with LTS.

             destruct `(dep_on N0 m1 n1 \/ ~ dep_on N0 m1 n1).
             ++ assert (dep_on N1 m1 n1) by eauto 2 using SRPC_net_new_lock_no_unlock_dep with LTS.
                smash_eq n0 m1.
                smash_eq n0 m0.
                1: eauto 3 with LTS.

                enough (~ dep_on N1 n0 m0).
                {
                  right; intros ?. apply `(~ dep_on N1 n0 m0).

                  assert (exists v', na = NComm m0 m1 Q v') by eauto using net_sane_new_lock_send_Q with LTS.
                  assert (exists m0' m1' v', na = NComm m0' m1' Q v'
                                             /\ (m0' = n0 \/ (m0' <> n0 /\ dep_on N0 n0 m0' /\ dep_on N1 n0 m0'))
                                             /\ (m1' = n1 \/ (m1' <> n1 /\ dep_on N0 m1' n1 /\ dep_on N1 m1' n1)))
                    by eauto using net_dep_close with LTS.

                  hsimpl in H14.
                  strip_exists @H15.
                  do 2 (destruct `(_ /\ _)). hsimpl in H15.
                  kill H14.
                }

                clear H1.
                clear - HEq HEq0 H H0 H3 H4 H5 H6 H9 H10 H11.
                (*
                    N0, N1 : PNet
                    H : net_sane N0
                    m0, m1 : Name
                    na : NAct (Act:=PAct)
                    H0 : N0 =( na )=> N1
                    n0, n1 : Name
                    H3 : ~ dep_on N0 n0 n1
                    H4 : ~ net_lock_on N0 m0 m1
                    H5 : net_lock_on N1 m0 m1
                    H6 : ~ dep_on N0 n0 m0
                    H9 : ~ net_lock_on N1 n0 n1
                    H10 : dep_on N0 m1 n1
                    H11 : dep_on N1 m1 n1
                    HEq : m1 <> n0
                    HEq0 : m0 <> n0
                 *)
                intros Hx.

                apply dep_lock_chain in Hx as [L' [? ?]].
                consider (exists L,
                             lock_chain N1 n0 L m0
                             /\ NoDup L
                             /\ not (List.In n0 L)
                             /\ not (List.In m0 L)) by eauto using lock_chain_dedup.
                clear L' H2 H1.
                generalize dependent n0.
                induction L; intros; hsimpl in *.
                ** destruct (net_sane_lock_dec N0 n0 m0); eauto 2 with LTS.
                   absurd (n0 = m0 /\ m0 = m1); eauto using SRPC_net_lock_uniq.
                   bullshit.
                   assert (exists v, na = NComm n0 m0 Q v) by eauto using net_sane_new_lock_send_Q with LTS.
                   assert (exists v, na = NComm m0 m1 Q v) by eauto using net_sane_new_lock_send_Q with LTS.
                   attac.
                ** rename a into n0'.
                   consider (NoDup (_ :: _)).
                   specialize (IHL ltac:(auto) ltac:(auto) n0').
                   apply IHL; try (intros ?); eauto 3 with LTS.
                   --- destruct (net_sane_lock_dec N0 n0 n0'); eauto 2 with LTS.
                       assert (exists v, na = NComm m0 m1 Q v) by eauto using net_sane_new_lock_send_Q with LTS.
                       assert (exists v, na = NComm n0 n0' Q v) by eauto using net_sane_new_lock_send_Q with LTS.
                       attac.

                   --- destruct (net_sane_lock_dec N0 n0 n0'); eauto 2 with LTS.
                       assert (exists v, na = NComm m0 m1 Q v) by eauto using net_sane_new_lock_send_Q with LTS.
                       assert (exists v, na = NComm n0 n0' Q v) by eauto using net_sane_new_lock_send_Q with LTS.
                       attac.

                   --- destruct (net_sane_lock_dec N0 n0' n1); eauto 2 with LTS.
                       +++ destruct (net_sane_lock_dec N0 n0 n0'); eauto 2 with LTS.
                           bullshit (dep_on N0 n0 n1).
                           assert (exists v, na = NComm m0 m1 Q v) by eauto using net_sane_new_lock_send_Q with LTS.
                           assert (exists v, na = NComm n0 n0' Q v) by eauto using net_sane_new_lock_send_Q with LTS.
                           attac.
                       +++ assert (exists v, na = NComm m0 m1 Q v) by eauto using net_sane_new_lock_send_Q with LTS.
                           assert (exists v, na = NComm n0' n1 Q v) by eauto using net_sane_new_lock_send_Q with LTS.
                           attac.

                   --- subst.
                       destruct (net_sane_lock_dec N0 n0 n0'); eauto 2 with LTS.
                       assert (exists v, na = NComm m0 n0' Q v) by eauto using net_sane_new_lock_send_Q with LTS.
                       assert (exists v, na = NComm n0 n0' Q v) by eauto using net_sane_new_lock_send_Q with LTS.
                       attac.

             ++ right.
                intros ?.


                assert (exists v', na = NComm m0 m1 Q v') by eauto using net_sane_new_lock_send_Q with LTS.
                assert (exists m0' m1' v', na = NComm m0' m1' Q v'
                                           /\ (m0' = n0 \/ (m0' <> n0 /\ dep_on N0 n0 m0' /\ dep_on N1 n0 m0'))
                                           /\ (m1' = n1 \/ (m1' <> n1 /\ dep_on N0 m1' n1 /\ dep_on N1 m1' n1)))
                  by eauto using net_dep_close with LTS.

                hsimpl in H12.
                strip_exists @H13.
                do 2 (destruct `(_ /\ _)).
                hsimpl in H12.

                remember (NComm _ _ _ _) as na; clear Heqna.
                destruct `(_ \/ _), `(_ \/ _); hsimpl in *; bullshit.

      + right.
        intros Hx.
        assert (exists m0' m1' v',
                   a = NComm m0' m1' Q v' /\
                     (m0' = n0 \/ m0' <> n0 /\ dep_on N0 n0 m0' /\ dep_on N1 n0 m0') /\
                     (m1' = n1 \/ m1' <> n1 /\ dep_on N0 m1' n1 /\ dep_on N1 m1' n1)
               ) by eauto using net_dep_close with LTS.
        apply H4.
        strip_exists @H5.
        destruct `(_ /\ _).
        eauto.
  Qed.


  Lemma deadlocked_M_get_lock [MN0 n] :
    SRPC_net '' MN0 ->
    deadlocked n '' MN0 ->
    exists n', net_lock_on '' MN0 n n'.

  Proof.
    intros.
    unfold deadlocked in *.
    hsimpl in *.
    eapply (deadset_net_lock `(DeadSet DS '' MN0)) in H0.
    hsimpl in *.
    unfold net_lock in *.
    consider (exists n0 : Name, pq_lock [n0] (NetMod.get n '' MN0)) by (eauto using SRPC_pq_get_lock with LTS).
    eattac.
  Qed.


  Lemma locked_M_NoRecvR [MN0 n n'] :
    net_sane '' MN0 ->
    net_lock_on '' MN0 n n' ->
    NoRecvR_MQ (get_MQ MN0 n).
  Proof.
    intros.
    unfold get_MQ.

    eapply Forall_forall.
    intros.
    destruct x; auto.
    destruct n0.
    destruct &t; auto.
    destruct (NetMod.get n MN0) as [MQ M S] eqn:?.

    enough (n0 = n').
    {
      subst.

      unfold net_lock_on, net_lock in *.
      hsimpl in *.
      consider (pq_lock L (NetMod.get n '' MN0)).
      apply (`(~ List.In (n', R, v) &I)).
      unfold net_deinstr, deinstr in *.
      ltac1:(autorewrite with LTS in * ).
      rewrite `(NetMod.get n MN0 = _) in *.
      destruct S.
      enough (deinstr (mq MQ M (pq l p l0)) = pq &I P []) by eauto using deinstr_In_recv with LTS.
      unfold deinstr; auto.
    }

    destruct S as [I P O].
    enough ((exists c0, SRPC (Lock c0 n0) P) /\ (exists c', SRPC (Lock c' n') &P)) as [[c0 ?] [c' ?]]
        by (consider (Lock c0 n0 = Lock c' n') by (eapply SRPC_inv; eattac); auto).
    split.
    - destruct (NetMod.get n '' MN0) as [I0 P0 O0] eqn:?.

      enough (P = P0 /\ List.In (n0, R, v) I0) as [? ?].
      {
        subst.
        unfold net_deinstr in *. simpl in *.
        ltac1:(autorewrite with LTS in * ).
        enough (exists c0, SRPC_pq (Lock c0 n0) (pq I0 P0 O0)) by attac.
        rewrite <- `(_ = pq I0 P0 O0).

        replace (deinstr (NetMod.get n MN0)) with (NetMod.get n '' MN0) by (unfold net_deinstr, deinstr; attac).

        eauto using net_sane_in_net_R_in_lock.
      }

      unfold net_deinstr in *.
      ltac1:(autorewrite with LTS in * ).
      split.
      + unfold deinstr in *.
        rewrite `(NetMod.get n MN0 = _) in *.
        attac.
      + rewrite `(NetMod.get n MN0 = _) in *.
        eauto using deinstr_In_recv.
    - assert (net_lock '' MN0 [n'] n) by eauto using lock_singleton with LTS.
      unfold net_lock in *.
      unfold net_deinstr, deinstr in *.
      ltac1:(autorewrite with LTS in * ).
      rewrite `(NetMod.get n MN0 = _) in *.
      eapply lock_SRPC_Lock.
      2: eattac.

      enough (NetMod.get n '' MN0 = pq (&I ++ MQ_r MQ) P (MQ_s MQ ++ &O))
        by (enough (AnySRPC_pq (pq (&I ++ MQ_r MQ) P (MQ_s MQ ++ &O))); eauto with LTS).

      unfold net_deinstr, deinstr in *.
      ltac1:(autorewrite with LTS in * ).
      rewrite `(NetMod.get n MN0 = _) in *.
      auto.
  Qed.

  Hint Immediate locked_M_NoRecvR : LTS.


  Lemma deadlocked_M_NoRecvR [MN0 n] :
    net_sane '' MN0 ->
    deadlocked n '' MN0 ->
    NoRecvR_MQ (get_MQ MN0 n).
  Proof.
    intros.
    consider (deadlocked _ _).
    hsimpl in *.
    consider (exists L, net_lock '' MN0 L n /\ incl L x)
      by eauto using deadset_net_lock.
    consider (exists n1, net_lock '' MN0 [n1] n) by (eapply net_get_lock; eauto with LTS).
    unfold net_lock in *.
    eapply locked_M_NoRecvR; eauto with LTS.
    eattac.
  Qed.

  Hint Immediate deadlocked_M_NoRecvR : LTS.


  Lemma KIC_invariant_H_lock [MN0 MN1 na] :
    net_sane '' MN0 ->
    Rad_net MN0 ->
    (forall n0 n1, net_lock_on '' MN0 n0 n1 -> _of lock MN0 n0 = Some n1) ->
    (MN0 =(na)=> MN1) ->
    forall n0 n1, net_lock_on '' MN1 n0 n1 -> _of lock MN1 n0 = Some n1.

  Proof.
    intros.
    assert (net_lock_on '' MN0 n0 n1 \/ ~ net_lock_on '' MN0 n0 n1) as [|] by eauto using net_sane_lock_dec.
    - assert (_of lock MN0 n0 = Some n1) by auto.
      destruct (_of lock MN1 n0) as [n|] eqn:?.
      + enough (n = n1) by (subst; auto).
        assert (forall v, na <> NComm n0 n Q (MValP v)).
        {
          destruct na; intros ? ?; doubt.
          hsimpl in *.
          absurd (n0 <> n0); eauto using locked_M_no_send.
        }
        eauto using M_preserve_steady_lock, eq_sym with LTS.
      + consider (exists v, na = NTau n0 (MActP (Recv (n1, R) v))) by eauto using Rad_set_unlock with LTS.
        exfalso.
        assert ('' MN0 = '' MN1) by (eapply net_deinstr_act_skip; eauto; simpl; eauto).
        rewrite `('' MN0 = _) in *.
        assert (net_lock '' MN1 [n1] n0) by eauto using lock_singleton with LTS.

        (* TODO no taus when locked *)
        destruct (NetMod.get n0 MN1) as [MQ0 M0 [I0 P0 O0]] eqn:?.
        destruct (NetMod.get n0 '' MN1) as [I0' P0' O0'] eqn:?.
        unfold net_lock_on, net_lock in *.
        unfold net_deinstr, deinstr in *.
        hsimpl in *.
        hsimpl in *.
        kill H7. (* pq_lock *)
        assert (~ List.In (n1, R, v) &I1) by (intros ?; eapply H12; eattac).
        hsimpl in *.
        eassert (MQ_s _ = [] /\ O0 = []) by eauto using app_eq_nil.
        hsimpl in *.
        absurd (List.In (n1, R, v) ((I1 ++ [(n1, R, v)]) ++ MQ_r MQ0)); attac.
    - consider (exists v, na = NComm n0 n1 Q (MValP v)) by eauto using SRPC_M_net_new_lock_query.
      (* TODO fix this shit *)
      kill H2. hsimpl in *.
      assert (h = Rad_handle) by eauto with LTS.
      smash_eq n0 n1; hsimpl in *; hsimpl in |- *; attac.
  Qed.


  Lemma deadlocked_preserve_M_lock1 [na MN0 MN1 n] :
    net_sane '' MN0 ->
    Rad_net MN0 ->
    (forall n0 n1, net_lock_on '' MN0 n0 n1 -> _of lock MN0 n0 = Some n1) ->
    deadlocked n '' MN0 ->
    (MN0 =(na)=> MN1) ->
    _of lock MN0 n = _of lock MN1 n.

  Proof.
    intros.

    assert (exists path, '' MN0 =[path]=> '' MN1) as [? ?] by eauto using Net_path_corr1.
    assert (deadlocked n '' MN1) by eauto with LTS.

    assert (exists m, net_lock_on '' MN0 n m) by eauto using deadlocked_M_get_lock with LTS.
    strip_exists @H6. (* TODO FIX THIS UNFOLD *)
    enough (net_lock_on '' MN1 n m).
    {
      replace (_of lock MN0 n) with (Some m) by eauto using eq_sym with LTS.
      replace (_of lock MN1 n) with (Some m) by eauto using eq_sym, KIC_invariant_H_lock with LTS.
      auto.
    }

    eauto with LTS.
  Qed.


  Lemma KIC_net_sane [MN] : KIC MN -> net_sane '' MN.
  Proof. intros; kill H. Qed.

  Hint Immediate KIC_net_sane : LTS.


  Lemma KIC_invariant_net_sane1 [MN0 MN1] [a] :
    (MN0 =(a)=> MN1) ->
    KIC MN0 ->
    net_sane '' MN1.

  Proof.
    intros.
    consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr1.
    eauto with LTS.
  Qed.

  Hint Resolve KIC_invariant_net_sane1 : LTS.


  Lemma KIC_Rad_net [MN] : KIC MN -> Rad_net MN.
  Proof.
    intros.
    consider (KIC MN).
    intros n.
    unfold Rad_MQued.
    specialize (H_Rad_C n).
    ltac1:(autounfold with LTS_get in * ).
    destruct (NetMod.get n MN).
    destruct m.
    auto.
  Qed.

  Hint Immediate KIC_Rad_net : LTS.


  Lemma KIC_lock_C [MN n0 n1] : KIC MN -> net_lock_on '' MN n0 n1 -> _of lock MN n0 = Some n1.
  Proof.
    intros.
    consider (KIC MN).
  Qed.

  Hint Immediate KIC_lock_C : LTS.


  Lemma deadlocked_preserve_M_lock [mpath MN0 MN1 n] :
    KIC MN0 ->
    deadlocked n '' MN0 ->
    (MN0 =[mpath]=> MN1) ->
    _of lock MN0 n = _of lock MN1 n.
  Proof.
    intros.
    assert (Rad_net MN0) by eauto with LTS. (* TODO why eattac not work? *)
    assert (forall n0 n1, net_lock_on '' MN0 n0 n1 -> _of lock MN0 n0 = Some n1) by (consider (KIC MN0); attac).
    assert (net_sane '' MN0) by eauto with LTS.
    clear H.

    generalize dependent MN0.
    induction mpath; intros.
    1: attac.

    hsimpl in *.
    transitivity '(_of lock N1 n).
    - eauto using deadlocked_preserve_M_lock1 with LTS.
    - consider (exists ppath, '' MN0 =[ppath]=> '' N1) by eauto using Net_path_corr1.
      assert (net_sane '' N1) by eauto with LTS.
      assert (deadlocked n '' N1) by eauto 2 with LTS.
      eauto using KIC_invariant_H_lock with LTS.
  Qed.


  Lemma pq_lock_preserve_lock_id [a MQ0 s0 S0 MQ1 s1 S1 L] :
    pq_lock L (mq MQ0 {|handle:=Rad_handle;state:=s0|} S0) ->
    pq_lock L (mq MQ1 {|handle:=Rad_handle;state:=s1|} S1) ->
    (mq MQ0 {|handle:=Rad_handle;state:=s0|} S0 =(a)=> mq MQ1 {|handle:=Rad_handle;state:=s1|} S1) ->
    lock_id (next_state s0) = lock_id (next_state s1).

  Proof.
    intros.
    destruct_ma &a; kill H1; simpl; auto.
    - destruct t; simpl; hsimpl in *; destruct s; destruct lock0 as [n0|]; simpl; auto.
      smash_eq n n0; attac.
    - kill H.
      destruct S1.
      hsimpl in *.
      bullshit.
    - attac.
    - hsimpl in *.
      blast_cases; eattac.
    - attac.
  Qed.


  Lemma deadlocked_vis_preserve_M_net_lock [na] [MN0 MN1 : MNet] [n L] :
    (forall m (v : Val), na <> recv (m, R) # v) ->
    (MN0 ~(n @ na)~> MN1) ->
    net_lock '' MN0 L n ->
    net_lock '' MN1 L n.

  Proof.
    intros.

    unfold net_lock, net_deinstr in *.
    ltac1:(autorewrite with LTS in * ).

    destruct (NetMod.get n MN0) as [MQ0 M0 [I0 P0 O0]] eqn:?.
    destruct (NetMod.get n MN1) as [MQ1 M1 [I1 P1 O1]] eqn:?.

    compat_hsimpl in *. compat_hsimpl in *.

    kill H1.
    consider (MQ_s MQ0 = [] /\ O0 = []) by auto using app_eq_nil.
    hsimpl in *.

    consider (mq MQ0 _ _ =(_)=> _); compat_hsimpl in *; attac 4; hsimpl in |- *;
      rewrite `(MQ_s _ = _) in *; attac.
    - destruct n0 as [? [|]].
      2: bullshit.
      assert (~ List.In (n1, R, v0) [(n0, Q, v)]) by (intros ?; attac).
      assert (~ List.In (n1, R, v) (I1 ++ MQ_r MQ0)) by attac.
      apply in_app_or in H5 as [|]. bullshit.
      apply in_app_or in H5 as [|]. bullshit.
      bullshit.
    - rewrite <- app_assoc in *.
      bullshit.
    - kill TP; attac.
  Qed.


  Lemma deadlocked_vis_preserve_M_lock_id [na MN0 MN1 n] :
    SRPC_net '' MN0 ->
    Rad_net MN0 ->
    deadlocked n '' MN0 ->
    (forall m (v : Val), na <> recv (m, R) # v) ->
    (MN0 ~(n @ na)~> MN1) ->
    _of lock_id MN0 n = _of lock_id MN1 n.

  Proof.
    intros.

    consider (exists m, net_lock_on '' MN0 n m) by eauto using deadlocked_M_get_lock with LTS.
    apply lock_singleton in H4. 2: attac.

    assert (net_lock '' MN1 [m] n)
      by eauto using deadlocked_vis_preserve_M_net_lock.

    unfold net_lock in *.

    ltac1:(autounfold with LTS_get).

    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.
    destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.

    assert (pq_lock [m] (mq MQ0 M0 S0)).
    {
      unfold net_deinstr in *.
      ltac1:(autorewrite with LTS in * ).
      rewrite `(NetMod.get n MN0 = _) in H4.
      auto.
    }

    assert (pq_lock [m] (mq MQ1 M1 S1)).
    {
      unfold net_deinstr in *.
      ltac1:(autorewrite with LTS in * ).
      rewrite `(NetMod.get n MN1 = _) in H5.
      auto.
    }

    eapply (pq_lock_preserve_lock_id
              `(pq_lock _ (mq MQ0 M0 S0))
              `(pq_lock _ (mq MQ1 M1 S1))).
    destruct M0, M1.

    assert (handle0 = Rad_handle).
    {
      specialize (H0 n).
      ltac1:(autounfold with LTS_get in * ).
      rewrite `(NetMod.get n MN0 = _) in *.
      auto.
    } subst.

    hsimpl in *. hsimpl in *.
    rewrite `(NetMod.get n MN0 = _) in *.

    assert (handle1 = Rad_handle).
    {
      kill H3; attac.
    } subst.

    eauto.
    eapply SRPC_net_lock_uniq; eauto with LTS.
    eauto with LTS.
  Qed.


  Lemma deadlocked_preserve_M_lock_id1 [na MN0 MN1 n] :
    SRPC_net '' MN0 ->
    Rad_net MN0 ->
    deadlocked n '' MN0 ->
    (MN0 =(na)=> MN1) ->
    _of lock_id MN0 n = _of lock_id MN1 n.

  Proof.
    intros.

    consider (exists m, net_lock_on '' MN0 n m) by eauto using deadlocked_M_get_lock with LTS.

    kill H2.
    - smash_eq n n0.
      + destruct a; doubt.
        eapply deadlocked_vis_preserve_M_lock_id; eauto; bullshit.
        eapply deadlocked_vis_preserve_M_lock_id; eauto; bullshit.
        eapply deadlocked_vis_preserve_M_lock_id; eauto; bullshit.
      + ltac1:(autounfold with LTS_get).
        replace (NetMod.get n MN1) with (NetMod.get n MN0); attac.
    - transitivity '(_of lock_id N0' n).
      + smash_eq n n0.
        * eapply deadlocked_vis_preserve_M_lock_id; eauto. intros.
          destruct v; bullshit.
        * ltac1:(autounfold with LTS_get).
          replace (NetMod.get n N0') with (NetMod.get n MN0); attac.
      + smash_eq n n0.
        * hsimpl in *.
          smash_eq n n'; destruct v; ltac1:(autounfold with LTS_get in * ); attac.
        * ltac1:(autounfold with LTS_get).
          smash_eq n n'; destruct v; attac.
  Qed.


  Lemma deadlocked_preserve_M_lock_id [mpath MN0 MN1 n] :
    net_sane '' MN0 ->
    Rad_net MN0 ->
    deadlocked n '' MN0 ->
    (MN0 =[mpath]=> MN1) ->
    _of lock_id MN0 n = _of lock_id MN1 n.
  Proof.
    intros.

    generalize dependent MN0.
    induction mpath; intros.
    1: attac.

    hsimpl in *.
    transitivity '(_of lock_id N1 n).
    - eapply deadlocked_preserve_M_lock_id1; eauto with LTS.
    - consider (exists ppath, '' MN0 =[ppath]=> '' N1) by eauto using Net_path_corr1.
      assert (net_sane '' N1) by eauto with LTS.
      assert (deadlocked n '' N1) by eauto 2 with LTS.
      eauto with LTS.
  Qed.


  Lemma deadlocked_preserve_hot_probe1 [na MN0 MN1 p n] :
    SRPC_net '' MN0 ->
    Rad_net MN0 ->
    deadlocked n '' MN0 ->
    (MN0 =(na)=> MN1) ->
    hot MN0 p n ->
    hot MN1 p n.

  Proof.
    intros.
    consider (hot MN0 p n).
    constructor; auto.
    now replace (_of lock_id MN1 (init p)) with (_of lock_id MN0 (init p)) by
      eauto using deadlocked_preserve_M_lock_id1 with LTS.
  Qed.


  Lemma deadlocked_preserve_hot_probe [mpath MN0 MN1 p n] :
    net_sane '' MN0 ->
    Rad_net MN0 ->
    deadlocked n '' MN0 ->
    (MN0 =[mpath]=> MN1) ->
    hot MN0 p n ->
    hot MN1 p n.

  Proof.
    intros.

    generalize dependent MN0.
    induction mpath; intros.
    1: hsimpl in *; auto.

    hsimpl in *.
    assert (hot N1 p n).
    - eapply deadlocked_preserve_hot_probe1; eauto with LTS.
    - consider (exists ppath, '' MN0 =[ppath]=> '' N1) by eauto using Net_path_corr1.
      assert (net_sane '' N1) by eauto with LTS.
      assert (deadlocked n '' N1) by eauto 2 with LTS.
      eauto with LTS.
  Qed.


  Lemma pq_lock_preserve_in_waitees [a MQ0 s0 S0 MQ1 s1 S1 L m] :
    pq_lock L (mq MQ0 {|handle:=Rad_handle;state:=s0|} S0) ->
    pq_lock L (mq MQ1 {|handle:=Rad_handle;state:=s1|} S1) ->
    (mq MQ0 {|handle:=Rad_handle;state:=s0|} S0 =(a)=> mq MQ1 {|handle:=Rad_handle;state:=s1|} S1) ->
    List.In m (waitees (next_state s0)) ->
    List.In m (waitees (next_state s1)).

  Proof.
    intros.
    destruct_ma &a; kill H1; simpl; auto.
    - destruct t; simpl; hsimpl in *; destruct s; destruct lock0 as [n0|]; simpl; auto.
      smash_eq n n0; attac.
    - kill H.
      blast_cases; attac.
    - attac.
    - hsimpl in *.
      blast_cases; attac.
    - attac.
  Qed.


  Lemma deadlocked_vis_preserve_in_waitees [na MN0 MN1 n n'] :
    SRPC_net '' MN0 ->
    Rad_net MN0 ->
    deadlocked n '' MN0 ->
    (forall m (v : Val), na <> recv (m, R) # v) ->
    (MN0 ~(n @ na)~> MN1) ->
    List.In n' (_of waitees MN0 n) ->
    List.In n' (_of waitees MN1 n).
  Proof.
    intros.
    consider (exists m, net_lock_on '' MN0 n m) by eauto using deadlocked_M_get_lock with LTS.
    apply lock_singleton in H5. 2: attac.

    assert (net_lock '' MN1 [m] n)
      by eauto using deadlocked_vis_preserve_M_net_lock.

    unfold net_lock in *.

    ltac1:(autounfold with LTS_get).

    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.
    destruct (NetMod.get n MN1) as [MQ1 M1 S1] eqn:?.

    assert (pq_lock [m] (mq MQ0 M0 S0)).
    {
      unfold net_deinstr in *.
      ltac1:(autorewrite with LTS in * ).
      rewrite `(NetMod.get n MN0 = _) in H5.
      auto.
    }

    assert (pq_lock [m] (mq MQ1 M1 S1)).
    {
      unfold net_deinstr in *.
      ltac1:(autorewrite with LTS in * ).
      rewrite `(NetMod.get n MN1 = _) in H6.
      auto.
    }

    assert (mq MQ0 M0 S0 =(na)=> mq MQ1 M1 S1).
    {
      hsimpl in *. hsimpl in *.
      now rewrite <- `(NetMod.get n MN0 = _).
    }

    destruct M0, M1.

    assert (handle0 = Rad_handle).
    {
      specialize (H0 n).
      ltac1:(autounfold with LTS_get in * ).
      rewrite `(NetMod.get n MN0 = _) in *.
      auto.
    } subst.

    assert (handle1 = Rad_handle).
    {
      hsimpl in *. hsimpl in *.
      rewrite `(NetMod.get n MN0 = _) in *.
      kill H3; attac.
    } subst.

    eapply pq_lock_preserve_in_waitees.
    3: eauto.
    all: eauto.
    ltac1:(autounfold with LTS_get in * ).
    rewrite `(NetMod.get n MN0 = _) in *.
    attac.
    eapply SRPC_net_lock_uniq; eauto with LTS.
    eauto with LTS.
  Qed.


  Lemma deadlocked_preserve_M_in_waitees1 [na MN0 MN1 n m] :
    SRPC_net '' MN0 ->
    Rad_net MN0 ->
    deadlocked n '' MN0 ->
    (MN0 =(na)=> MN1) ->
    List.In m (_of waitees MN0 n) ->
    List.In m (_of waitees MN1 n).

  Proof.
    intros.

    consider (exists m, net_lock_on '' MN0 n m) by eauto using deadlocked_M_get_lock with LTS.

    kill H2.
    - smash_eq n n0.
      + destruct a; doubt.
        eapply deadlocked_vis_preserve_in_waitees; eauto; bullshit.
        eapply deadlocked_vis_preserve_in_waitees; eauto; bullshit.
        eapply deadlocked_vis_preserve_in_waitees; eauto; bullshit.
      + ltac1:(autounfold with LTS_get).
        replace (NetMod.get n MN1) with (NetMod.get n MN0); attac.
    - assert (List.In m (_of waitees N0' n)).
      + smash_eq n n0.
        * eapply deadlocked_vis_preserve_in_waitees; eauto. intros.
          destruct v; bullshit.
        * ltac1:(autounfold with LTS_get).
          replace (NetMod.get n N0') with (NetMod.get n MN0); attac.
      + smash_eq n n0.
        * hsimpl in *.
          smash_eq n n'; destruct v; ltac1:(autounfold with LTS_get in * ); attac.
        * ltac1:(autounfold with LTS_get in * ).
          hsimpl in *.
          hsimpl in |- *.
          smash_eq n n'; destruct v; hsimpl in *; hsimpl in |- *; auto.
  Qed.


  Lemma deadlocked_preserve_M_in_waitees [mpath MN0 MN1 n m] :
    net_sane '' MN0 ->
    Rad_net MN0 ->
    deadlocked n '' MN0 ->
    (MN0 =[mpath]=> MN1) ->
    List.In m (_of waitees MN0 n) ->
    List.In m (_of waitees MN1 n).

  Proof.
    intros.

    generalize dependent MN0.
    induction mpath; intros.
    1: attac.

    hsimpl in *.
    assert (List.In m (_of waitees N1 n)).
    - eapply deadlocked_preserve_M_in_waitees1; eauto with LTS.
    - consider (exists ppath, '' MN0 =[ppath]=> '' N1) by eauto using Net_path_corr1.
      assert (net_sane '' N1) by eauto with LTS.
      assert (deadlocked n '' N1) by eauto 2 with LTS.
      eauto with LTS.
  Qed.


  Lemma net_deinstr_act_or [MN0 MN1] [ma] :
    (MN0 =(ma)=> MN1) ->
    '' MN0 = '' MN1 \/ exists a, '' MN0 =(a)=> '' MN1.

  Proof.
    clear.
    intros.
    destruct (MNAct_to_PNAct ma) eqn:?.
    - right. exists p. eauto using net_deinstr_act_do.
    - left. eauto using net_deinstr_act_skip.
  Qed.


  Lemma deadlocked_M_dep_invariant1 [MN0 MN1 n0 n1 a] :
    (MN0 =(a)=> MN1) ->
    deadlocked n0 '' MN0 ->
    dep_on '' MN0 n0 n1 ->
    dep_on '' MN1 n0 n1.

  Proof.
    intros.
    destruct (@net_deinstr_act_or MN0 MN1 a); auto.
    - rewrite <- `('' MN0 = _). auto.
    - hsimpl in *. eauto using deadlocked_dep_invariant1.
  Qed.


  Lemma hot_of_hot [MN p n] : hot MN p n -> p = hot_of MN n.

  Proof.
    clear.
    intros.
    consider (hot _ p _).
    destruct p.
    attac.
  Qed.


  Lemma deadlocked_preserve_hot_of1 [MN0 MN1 a m] :
    net_sane '' MN0 ->
    Rad_net MN0 ->
    deadlocked m '' MN0 ->
    (MN0 =(a)=> MN1) ->
    hot_of MN0 m = hot_of MN1 m.

  Proof.
    intros.
    enough (hot MN1 (hot_of MN0 m) m) by auto using hot_of_hot.
    assert (hot MN0 (hot_of MN0 m) m) by auto using hot_hot_of.
    eauto using deadlocked_preserve_hot_probe1 with LTS.
  Qed.


  Lemma KIC_invariant_H_wait [MN0 MN1 : MNet] [a] [n0 n1] :
    KIC MN0 ->
    (MN0 =(a)=> MN1) ->
    net_lock_on '' MN1 n0 n1 ->
    NoRecvQ_from n0 (get_MQ MN1 n1) ->
    List.In n0 (_of waitees MN1 n1).

  Proof.
    intros.
    assert (net_lock_on '' MN0 n0 n1 \/ ~ net_lock_on '' MN0 n0 n1) as [|] by eauto using net_sane_lock_dec with LTS.
    - assert (NoRecvQ_from n0 (get_MQ MN0 n1) \/ ~ NoRecvQ_from n0 (get_MQ MN0 n1)) as [|] by eauto using NoRecvQ_from_dec.
      + assert (List.In n0 (_of waitees MN0 n1)) by (consider (KIC MN0); auto).
        assert (_of lock MN0 n0 = Some n1) by (consider (KIC MN0); auto).
        (* clear - H1 H H5 H3 H2 H6 H4 H7 H0. *)
        consider (MN0 =(a)=> _).
        * hsimpl in *.
          ltac1:(autounfold with LTS_get in * ).
          destruct_ma &a0; doubt; hsimpl in *; eauto.
          -- smash_eq n n1; hsimpl in *; attac.
          -- smash_eq n n1; hsimpl in *; attac.
             assert (h = Rad_handle).
             {
               consider (KIC MN0). specialize (H_Rad_C n). ltac1:(autounfold with LTS_get in * ).
               rewrite `(NetMod.get n MN0 = _) in *. auto.
             } subst.
             simpl in *.
             blast_cases; attac.
          -- smash_eq n n1; hsimpl in *; attac.
          -- smash_eq n n1; hsimpl in *; attac.
             assert (h = Rad_handle) by eauto with LTS.
             subst; simpl in *.
             blast_cases; attac.
        * destruct v; hsimpl in *.
          -- ltac1:(autounfold with LTS_get in * ).
             smash_eq n' n n1; hsimpl in |- *; auto; hsimpl in *.
             all: try (rewrite `(NetMod.get n' MN0 = _) in * ).
             all: try (rewrite `(NetMod.get n MN0 = _) in * ).
             all: auto.
          -- smash_eq n n0.
             {
               exfalso.
               apply lock_singleton in H3. 2: attac.
               unfold net_lock in *.
               clear - H3 H7.
               unfold net_deinstr in *.
               ltac1:(autorewrite with LTS in * ).
               rewrite `(NetMod.get n MN0 = _ ) in *.
               kill H3.
               destruct P0.
               bullshit.
               eapply SRPC_net_lock_uniq; eauto with LTS.
               eauto with LTS.
             }
             ltac1:(autounfold with LTS_get in * ).
             hsimpl.
             smash_eq n n' n1; hsimpl in |- *; auto; doubt; hsimpl in *; destruct &t; doubt.
             all: try (rewrite `(NetMod.get n MN0 = _) in * ).
             all: try (rewrite `(NetMod.get n' MN0 = _) in * ).
             all: auto.
             all: assert (h = Rad_handle)
               by (do 2 (consider (KIC MN0)); specialize (H_Rad_C n); ltac1:(autounfold with LTS_get in * ); rewrite `(NetMod.get n MN0 = _) in *; auto).
             all: subst; hsimpl in *; hsimpl in |- *; hsimpl in |- *; auto.
             1: auto using in_in_remove.
             smash_eq n0 n'. 2: apply in_in_remove; auto.
             clear - H1.
             exfalso.
             kill H1.
             hsimpl in *.
             unfold net_lock, net_deinstr in *.
             ltac1:(autorewrite with LTS in * ).
             kill H0.
             destruct P.
             hsimpl in *.
             eapply H3 with (v:=v); eattac.
      + assert (_of lock MN0 n0 = Some n1) by (consider (KIC MN0); auto).
        assert (exists v, a = NTau n1 (MActP (Recv (n0, Q) v))) by eauto using net_TrRecvQ_pop.
        hsimpl in *.
        consider (_ =(_)=> _).
        hsimpl in *.
        consider (h = Rad_handle) by eauto with LTS.
        hsimpl in *; hsimpl in |- *; hsimpl in |- *; auto.
        ltac1:(autounfold with LTS_get in * ).
        destruct s; simpl in *; destruct lock0 eqn:?; subst; attac.
    - consider (exists v, a = NComm n0 n1 Q (MValP v)) by eauto using SRPC_M_net_new_lock_query with LTS.
      absurd (List.In (TrRecv (n0, Q) v) (get_MQ MN1 n1)). 1: attac.
      kill H0. hsimpl in *.
      attac.
  Qed.


  (* TODO to Locks *)
  Lemma deadlocked_dep_on_loop [N n0] :
    net_sane N ->
    deadlocked n0 N ->
    exists n1, dep_on N n0 n1 /\ dep_on N n1 n1.

  Proof with eattac.
    intros HSRPC Hd.

    assert (forall n, AnySRPC_pq (NetMod.get n N)) as Hsrpc by eauto with LTS.

    consider (exists DS, List.In n0 DS /\ DeadSet DS N).
    hsimpl in *. (* TODO why? *)
    rename H0 into HDS.
    rename H into HIn.

    destruct (deadset_dep_set HDS HIn) as [L HL].

    assert (L <> []) as HLnil.
    {
      destruct L; doubt.
      destruct (deadset_net_lock HDS HIn) as [L' [HL' _]].
      consider (exists n1, net_lock N [n1] n0) by (eapply net_get_lock; eauto with LTS).
      unfold dep_set in HL.
      assert (net_lock_on N n0 n1) by eattac.
      assert (dep_on N n0 n1) as HD' by attac.
      apply HL in HD'.
      bullshit.
    }

    specialize (deadset_dep_set_deadset HDS HL HLnil HIn) as HDSL.

    consider (exists (n1 : Name) (L' : Names), lock_chain N n0 L' n1 /\ incl L (n1 :: L')).
    {
      eapply longest_lock_chain; eauto with LTS.
      unfold locks_dec_in. intros; eauto using net_sane_lock_dec.
    }

    enough (dep_on N n1 n1) by eauto with LTS.

    enough (exists n2, List.In n2 (n1::L) /\ dep_on N n1 n2) as [n2 [HIn1 HD1]].
    {
      kill HIn1.
      smash_eq n1 n2.
      eapply (lock_chain_split_in) with (n1:=n2) in H
          as (L0 & L1 & HEq' & HLc0 & HLc1).
      apply lock_chain_dep in HLc1.
      eauto with LTS.
      apply `(incl _ _) in H1.
      attac.
    }

    assert (List.In n1 L) as HIn2 by (apply HL; eapply lock_chain_dep; eauto).

    assert (exists n2, net_lock_on N n1 n2) as [n2 HL1].
    {
      apply (deadset_net_lock HDSL) in HIn2 as [L2 [HL2 _]].
      apply net_get_lock in HL2 as [n2 HL2]; eauto with LTS.
      exists n2.
      eattac.
    }

    exists n2; split; auto with LTS.

    enough (List.In n2 L) by attac.

    eapply deadset_in; eauto.
  Qed.


  Lemma sends_probe_extend_r [MQ0 MQ' M0 S0] [nc p] :
    sends_probe nc p (mq MQ0 M0 S0) ->
    sends_probe nc p (mq (MQ0 ++ MQ') M0 S0).

  Proof.
    intros.
    generalize dependent MQ0 S0 nc p.
    induction MQ'; intros; hsimpl in *; hsimpl in |- *.
    - attac.
    - replace (MQ0 ++ a :: MQ') with ((MQ0 ++ [a]) ++ MQ') by attac.
      apply IHMQ'.
      destruct M0.
      clear IHMQ'.
      generalize dependent a MQ0.
      induction state0; intros; attac.
      + kill H; rewrite <- app_assoc; eauto with LTS.
      + kill H; eauto with LTS.
  Qed.


  Lemma sends_probe_proc [MQ0 M0 S0 S0'] [nc p] :
    sends_probe nc p (mq MQ0 M0 S0) ->
    sends_probe nc p (mq MQ0 M0 S0').

  Proof.
    intros.
    ltac1:(dependent induction H); eauto with LTS.
  Qed.

  Lemma sends_probe_waitees_s_l1 [MQ0 S0] [ss sl si sw n sd] [nc l t p] :
    sends_probe nc p (mq MQ0 {|handle:=Rad_handle;state:=MSend_all l t p (MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;waitees:=sw|})|} S0) ->
    sends_probe nc p (mq MQ0 {|handle:=Rad_handle;state:=MSend_all l t p (MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;waitees:=n :: sw|})|} S0).

  Proof.
    intros.
    induction l.
    - kill H; hsimpl in *; hsimpl in |- *.
      + econstructor 1; eattac.
      + econstructor 2; subst; kill H4; eattac.
    - destruct (NChan_eq_dec nc (a, &t)).
      + subst. econstructor 3.
      + kill H.
        apply IHl in H1.
        econstructor 4; eattac.
  Qed.


  Lemma sends_probe_waitees_l1 [MQ0 S0] [ss sl si sw n sd] [nc p] :
    sends_probe nc p (mq MQ0 {|handle:=Rad_handle;state:=MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;waitees:=sw|}|} S0) ->
    sends_probe nc p (mq MQ0 {|handle:=Rad_handle;state:=MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;waitees:=n :: sw|}|} S0).

  Proof.
    intros.
    kill H; hsimpl in *; hsimpl in |- *.
    - econstructor 1; eattac.
    - econstructor 2; subst; kill H4; eattac.
  Qed.


  Lemma sends_probe_waitees_l [MQ0 S0] [ss sl si sw sw' sd] [nc p] :
    sends_probe nc p (mq MQ0 {|handle:=Rad_handle;state:=MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;waitees:=sw|}|} S0) ->
    sends_probe nc p (mq MQ0 {|handle:=Rad_handle;state:=MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;waitees:=sw' ++ sw|}|} S0).

  Proof.
    intros.
    induction sw'; eauto using sends_probe_waitees_l1.
  Qed.


  Lemma sends_probe_skip1 [MQ0 h n s S0] [nc t p] :
    sends_probe nc p (mq MQ0 {|handle:=h;state:=s|} S0) ->
    sends_probe nc p (mq MQ0 {|handle:=h;state:=MSend (n, t) p s|} S0).

  Proof.
    intros.
    destruct (NChan_eq_dec nc (n, &t)); eattac.
  Qed.


  Lemma sends_probe_skip [MQ0 h l s S0] [nc t p] :
    sends_probe nc p (mq MQ0 {|handle:=h;state:=s|} S0) ->
    sends_probe nc p (mq MQ0 {|handle:=h;state:=MSend_all l t p s|} S0).

  Proof.
    intros.
    induction l; eauto using sends_probe_skip1.
  Qed.


  Lemma sends_probe_skip_inv1 [MQ0 h n s s' S0] [nc t p] :
    sends_probe nc p (mq MQ0 {|handle:=h;state:=s|} S0) ->
    sends_probe nc p (mq MQ0 {|handle:=h;state:=MSend (n, t) p s'|} S0) ->
    sends_probe nc p (mq MQ0 {|handle:=h;state:=MSend (n, t) p s|} S0).

  Proof.
    intros.
    destruct (NChan_eq_dec nc (n, &t)); eattac.
  Qed.


  Lemma sends_probe_skip_inv [MQ0 h l s s' S0] [nc t p] :
    sends_probe nc p (mq MQ0 {|handle:=h;state:=s|} S0) ->
    sends_probe nc p (mq MQ0 {|handle:=h;state:=MSend_all l t p s'|} S0) ->
    sends_probe nc p (mq MQ0 {|handle:=h;state:=MSend_all l t p s|} S0).

  Proof.
    intros.
    induction l; eauto.
    kill H0; eattac.
  Qed.


  Lemma sends_probe_skip_neq1 [MQ0 h n s S0] [nc t p p'] :
    p <> p' ->
    sends_probe nc p (mq MQ0 {|handle:=h;state:=s|} S0) <->
      sends_probe nc p (mq MQ0 {|handle:=h;state:=MSend (n, t) p' s|} S0).

  Proof.
    eattac.
  Qed.


  Lemma sends_probe_skip_neq [MQ0 h l s S0] [nc t p p'] :
    p <> p' ->
    sends_probe nc p (mq MQ0 {|handle:=h;state:=s|} S0) <->
      sends_probe nc p (mq MQ0 {|handle:=h;state:=MSend_all l t p' s|} S0).

  Proof.
    split; intros.
    - induction l; eattac.
    - induction l; eattac.
      kill H0;eattac.
  Qed.


  Hint Rewrite <- sends_probe_skip_neq1 sends_probe_skip_neq using spank : LTS_concl.
  Hint Resolve -> sends_probe_skip_neq1 sends_probe_skip_neq : LTS.


  Lemma sends_probe_waitees_skip_l1 [MQ0 S0] [ss sl si sw n n' t sd] [p] :
    n <> n' ->
    sends_probe (n, t) p (mq MQ0 {|handle:=Rad_handle;state:=MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;waitees:=n'::sw|}|} S0) ->
    sends_probe (n, t) p (mq MQ0 {|handle:=Rad_handle;state:=MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;waitees:=sw|}|} S0).

  Proof.
    intros.

    kill H0.
    - simpl in *. subst.
      econstructor 1; eattac.
    - simpl in *; subst. kill H5; econstructor 2; eattac.
  Qed.


  Lemma sends_probe_waitees_skip_l [MQ0 S0] [ss sl si sw sw' sd n t] [p] :
    ~ List.In n sw' ->
    sends_probe (n, t) p (mq MQ0 {|handle:=Rad_handle;state:=MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;waitees:=sw' ++ sw|}|} S0) ->
    sends_probe (n, t) p (mq MQ0 {|handle:=Rad_handle;state:=MRecv {|self:=ss;lock:=sl;lock_id:=si;alarm:=sd;waitees:=sw|}|} S0).

  Proof.
    intros.
    generalize dependent sw n.
    induction sw'; intros; hsimpl in *; eauto using sends_probe_waitees_skip_l1.
  Qed.


  Lemma sends_probe_skip_s1 [MQ0 S0] [nc nc'] [p p'] [s] :
    nc <> nc' ->
    sends_probe nc p (mq MQ0 {|handle:=Rad_handle;state:=MSend nc' p' s|} S0) <->
      sends_probe nc p (mq MQ0 {|handle:=Rad_handle;state:=s|} S0).

  Proof.
    split; intros.
    - kill H0.
    - eattac.
  Qed.


  Lemma sends_probe_skip_s_in [MQ0 S0] [n t t'] [l p p'] [s] :
    ~ List.In n l ->
    sends_probe (n, t) p (mq MQ0 {|handle:=Rad_handle;state:=MSend_all l t' p' s|} S0) <->
      sends_probe (n, t) p (mq MQ0 {|handle:=Rad_handle;state:=s|} S0).

  Proof.
    split; intros.
    - induction l; attac.
      apply sends_probe_skip_s1 in H0; attac.
    - induction l; attac.
  Qed.

  Hint Rewrite -> sends_probe_skip_s1 sends_probe_skip_s_in using spank : LTS_concl.
  Hint Resolve <- sends_probe_skip_s1 sends_probe_skip_s_in : LTS.


  Lemma mq_sends_probe_sent [MS0 MS1 : MQued] [ma : MAct] [nc p] :
    Rad_MQued MS0 ->
    (MS0 =(ma)=> MS1) ->
    sends_probe nc p MS0 ->
    ~ sends_probe nc p MS1 ->
    ma = send nc (MValM p).

  Proof.
    intros.
    destruct_ma &ma; compat_hsimpl in *; doubt.
    6: destruct (NChan_eq_dec nc (n, &t)); subst; auto.
    6: destruct (MProbe_eq_dec p v) as [?|HEqv]; subst; auto.
    all: exfalso; apply H2; clear H2; subst.
    all: eauto using sends_probe_extend_r, sends_probe_proc.
    - kill H1.
      + destruct MQ0; kill H7.
        * destruct s; simpl in *; subst.
          destruct p.
          eauto with LTS.
        * hsimpl in *.
          destruct s eqn:?; simpl in *; subst lock0.
          remember {| self := self0;
                     lock_id := lock_id0;
                     lock := Some n';
                     waitees := n :: waitees0;
                     alarm := alarm0
                   |} as s1.
          replace {| init := self0; index := lock_id0 |} with
            {| init := self s1; index := lock_id s1 |} by (subst; auto).

          assert (NoRecvR_from n' MQ0) by (intros ? ?; apply (H v1); eattac).
          destruct &t; smash_eq n0 n; destruct p; attac.
          smash_eq n0 n'; eattac.
          1: specialize (H v); bullshit.
          smash_eq n n'; attac.
          1: econstructor 1; eattac.
          specialize (H v); bullshit.
      + destruct MQ0; kill H7.

        smash_eq n n0.
        * destruct s eqn:?; simpl in *; subst lock0.
          remember {| self := self0;
                     lock_id := lock_id0;
                     lock := Some n';
                     waitees := n :: waitees0;
                     alarm := alarm0
                   |} as s1.
          replace {| init := self0; index := lock_id0 |} with
            {| init := self s1; index := lock_id s1 |} by (subst; auto).

          assert (NoRecvR_from n' MQ0) by (intros ? ?; apply (H v0); eattac).
          destruct &t; smash_eq n n'.
          3: specialize (H v); bullshit.
          econstructor 4; eattac.
          econstructor 2; eattac.
          econstructor 4; eattac.
          econstructor 2; eattac.
          hsimpl.
          econstructor 2; kill H4; eattac.

        * assert (List.In n0 (waitees s) \/ (exists v0, List.In (TrRecv (n0, Q) v0) MQ0)) by (kill H4; eattac). clear H4.
          destruct s eqn:?; simpl in *; subst lock0.
          remember {| self := self0;
                     lock_id := lock_id0;
                     lock := Some n';
                     waitees := n :: waitees0;
                     alarm := alarm0
                   |} as s1.
          replace {| init := self0; index := lock_id0 |} with
            {| init := self s1; index := lock_id s1 |} by (subst; auto).

          assert (NoRecvR_from n' MQ0) by (intros ? ?; apply (H v0); eattac).
          destruct &t; smash_eq n n'.
          3: specialize (H v); bullshit.
          econstructor 4; eattac.
          econstructor 2; eattac. destruct `(_ \/ _); attac.
          econstructor 2; eattac.
          hsimpl.
          econstructor 2; eattac.
    - kill H1.
      all: destruct MQ0; hsimpl in *; bullshit.
    - destruct M1; attac.
    - kill H.
      destruct M1; hsimpl in *; eattac.

    - destruct n.
      destruct s; destruct &t; simpl in *.
      + kill H1; hsimpl in *.
        * destruct MQ0; kill H7.
          hsimpl in *.
          econstructor 1; eattac.
          specialize (H v0). bullshit.
        * destruct MQ0; kill H7.
          hsimpl in *.
          econstructor 2; destruct H4; eattac.
          specialize (H v); bullshit.
          specialize (H v); bullshit.
      + destruct lock0 as [n0|].
        2: kill H1; bullshit.
        smash_eq n n0; hsimpl in |- *.
        * destruct p, msg; hsimpl in *.
          smash_eq init1 self0; hsimpl in *.
          -- destruct (PeanoNat.Nat.eqb lock_id0 index1); hsimpl in *.
             ++ {
                 kill H1; hsimpl in *.
                 -- destruct MQ0; kill H7; hsimpl in *; econstructor 1; eattac.
                    specialize (H v0); bullshit.
                 -- destruct MQ0; kill H7; hsimpl in *; econstructor 2; kill H4; eattac.
                    specialize (H v); bullshit.
                    specialize (H v); bullshit.
               }
             ++ {
                 kill H1; hsimpl in *.
                 -- destruct MQ0; kill H7; hsimpl in *; econstructor 1; eattac.
                    specialize (H v0); bullshit.
                 -- destruct MQ0; kill H7; hsimpl in *; econstructor 2; kill H4; eattac.
                    specialize (H v); bullshit.
                    specialize (H v); bullshit.
               }
          -- destruct nc.
             remember {|
                 self := self0;
                 lock_id := lock_id0;
                 lock := Some n;
                 waitees := waitees0;
                 alarm := alarm0
               |} as s0.

             destruct (MProbe_eq_dec {| init := init0; index := index0 |} {| init := init1; index := index1 |}).

             2: subst; apply sends_probe_skip_neq; attac.
             2: kill H1.
             2: destruct MQ0; kill H8; econstructor 1; eattac.
             2: specialize (H v0); bullshit.
             2: destruct MQ0; kill H8; doubt; econstructor 2; kill H4; eattac.
             2: specialize (H v); bullshit.
             2: specialize (H v); bullshit.

             hsimpl in e.

             generalize dependent s0.
             induction waitees0; intros.
             {
               simpl in *.
               kill H1.
               ** destruct MQ0; kill H8; hsimpl in *.
                  econstructor 1; eattac.
               ** destruct MQ0; kill H8; hsimpl in *. 1: bullshit.
                  econstructor 2; eattac.
                  specialize (H v0); bullshit.
             }
             destruct &t. 1: bullshit.

             smash_eq n0 a.
             1: econstructor 3.
             hsimpl in *.

             specialize IHwaitees0 with (s0:=
                           {|
                             self := self0;
                             lock_id := lock_id0;
                             lock := Some n;
                             waitees := waitees0;
                             alarm := alarm0|}).

             eapply sends_probe_waitees_skip_l1 in H1. 2: attac.

             specialize IHwaitees0 with (2:=eq_refl).

             eauto using sends_probe_waitees_s_l1.

        * destruct nc.
          destruct &t. 1: kill H1.
          subst.
          destruct p; simpl in *; subst.
          kill H1; hsimpl in *.
          ++ destruct MQ0; kill H7; econstructor 1; eattac.
             specialize (H v0); bullshit.
          ++ destruct MQ0; kill H7; econstructor 2; kill H4; eattac.
             specialize (H v); bullshit.
             specialize (H v); bullshit.
  Qed.


  Lemma vis_sends_probe_sent [MN0 MN1 : MNet] [a] [n0 n1 n'] [t p] :
    Rad_net MN0 ->
    (MN0 ~(n' @ a)~> MN1) ->
    sends_probe (n1, t) p (NetMod.get n0 MN0) ->
    ~ sends_probe (n1, t) p (NetMod.get n0 MN1) ->
    n' = n0 /\ a = send (n1, t) ^ p.

  Proof.
    intros.
    smash_eq n0 n'.
    - kill H0.
      consider (a = send (n1, &t) ^ p) by (eapply mq_sends_probe_sent; eattac).
    - replace (NetMod.get n0 MN1) with (NetMod.get n0 MN0) by eauto using NV_stay.
      bullshit.
  Qed.


  Lemma sends_probe_sent [MN0 MN1 : MNet] [a] [n0 n1] [t p] :
    Rad_net MN0 ->
    (MN0 =(a)=> MN1) ->
    sends_probe (n1, t) p (NetMod.get n0 MN0) ->
    ~ sends_probe (n1, t) p (NetMod.get n0 MN1) ->
    a = NComm n0 n1 t ^ p.

  Proof.
    intros.
    kill H0.
    - consider (_ /\ a0 = send (n1, &t) ^ p) by (eauto using vis_sends_probe_sent).
      bullshit.
    - assert (Rad_net N0').
      {
        unfold Rad_net. intros.
        smash_eq n n2.
        - kill H3; hsimpl in |- *; eauto with LTS.
          specialize (H n).
          unfold Rad_MQued in *.
          destruct (NetMod.get n MN0) as [MQ [h s] S'].
          subst.
          destruct S as [Q [hh ss] W].
          kill H0; eattac.
        (* TODO cleanup  *)
        - replace (NetMod.get n2 N0') with (NetMod.get n2 MN0)
            by eauto using NV_stay, eq_sym.
          apply H.
      }
      destruct (sends_probe_dec (n1, &t) p (NetMod.get n0 N0')); eauto with LTS.
      + consider (_ /\ recv (n, t0) v = send (n1, &t) ^ p) by eauto using vis_sends_probe_sent.
        destruct v; bullshit.
      + clear H2.
        consider (n = n0 /\ send (n', t0) v = send (n1, &t) ^ p) by eauto using vis_sends_probe_sent.
        destruct v; kill H6.
        auto.
  Qed.


  Lemma sends_probe_init_skip [MQ MQ' s S n n' v p] :
    NoRecvR_from n' MQ -> (* We won't unlock *)
    NoSends_MQ MQ -> (* We won't change the lock_id *)
    lock (next_state s) = Some n' -> (* We are locked *)
    init p = self (next_state s) -> index p = lock_id (next_state s) -> (* Our hot probe *)
    sends_probe (n, R)
      p
      (mq
         (MQ ++ TrRecv (n, Q) v :: MQ') (* There is a query incoming... *)
         {|handle:=Rad.Rad_handle; state:=s|} (* We are ready to take it *)
         S
      ).

  Proof.
    intros.
    induction s.
    - econstructor 1; eattac.
    - assert (sends_probe (n, R) p
                (mq (MQ ++ TrRecv (n, Q) v :: MQ') {| handle := Rad_handle; state := s |} &S)) by eattac.
      destruct to.
      destruct (MProbe_eq_dec p msg); subst.
      + eauto using sends_probe_skip1.
      + econstructor 4; eattac.
  Qed.


  Lemma sends_probe_prop_skip [MQ MQ' s S n n' p] :
    NoRecvR_from n' MQ -> (* We won't unlock *)
    NoSends_MQ MQ -> (* We won't change the lock_id *)
    lock (next_state s) = Some n' -> (* We are locked *)
    init p <> self (next_state s) -> (* The probe is not ours *)
    List.In n (waitees (next_state s)) \/ (exists v, List.In (TrRecv (n, Q) v) MQ) -> (* The receiver will be in waitees *)
    sends_probe (n, R) p (mq (MQ ++ EvRecv (n', R) p :: MQ') {|handle:=Rad.Rad_handle; state:=s|} S).

  Proof.
    intros.
    induction s.
    - econstructor 2; eattac.
    - assert (sends_probe (n, R) p
                (mq (MQ ++ EvRecv (n', R) p :: MQ') {| handle := Rad_handle; state := s |} &S)) by eattac.
      destruct to.
      destruct (MProbe_eq_dec p msg); subst.
      + eauto using sends_probe_skip1.
      + econstructor 4; eattac.
  Qed.


  Lemma sends_probe_prop_foreign [MN0 n0 n1 n2 p MQ] :
    KIC MN0 ->
    net_lock_on '' MN0 n0 n1 ->
    net_lock_on '' MN0 n1 n2 ->
    init p <> n1 ->
    (* List.In (EvRecv (n2, R) p) (get_MQ MN0 n1) -> *) (* TODO requires tighter KIC-wait *)
    get_MQ MN0 n1 = MQ ++ [EvRecv (n2, R) p] ->
    sends_probe (n0, R) p (NetMod.get n1 MN0).

  Proof.
    intros.

    destruct (NetMod.get n1 MN0) as [MQ1 [h1 s1] S1] eqn:?.

    consider (h1 = Rad_handle) by eauto with LTS.

    (* assert (get_MQ MN0 n1 = MQ1) by (ltac1:(autounfold with LTS_get in * ); attac). *)
    (* rewrite `(get_MQ MN0 n1 = _) in *.  clear H4. *)
    consider (MQ1 = get_MQ MN0 n1) by (ltac1:(autounfold with LTS_get in * ); attac).
    rewrite `(get_MQ MN0 n1 = _) in *. clear H3.


    (* consider (exists MQ10 MQ11 : list Event, MQ1 = MQ10 ++ EvRecv (n2, R) p :: MQ11) by eauto using in_split. *)

    eapply sends_probe_prop_skip; eauto with LTS; subst.
    - enough (NoRecvR_MQ MQ) by eauto with LTS.
      enough (NoRecvR_MQ (get_MQ MN0 n1)) by (ltac1:(autounfold with LTS_get in * ); attac).
      now eauto using locked_M_NoRecvR with LTS.

    - enough (no_sends_in n1 MN0) by (unfold no_sends_in, NoTrSend in *; attac).
      eauto using net_lock_on_M_no_sends_in.
    - assert (_of lock MN0 n1 = Some n2) by eauto with LTS.
      ltac1:(autounfold with LTS_get in * ); attac.
    - enough (self (next_state s1) = n1) by (subst; eauto with LTS).
      enough (_of self MN0 n1 = n1) by (ltac1:(autounfold with LTS_get in * ); attac 2).
      consider (KIC MN0). (* TODO to lemma... *)

    - consider (pq_client n0 (NetMod.get n1 '' MN0)) by eauto with LTS.
      + unfold net_deinstr in *.
        compat_hsimpl in *.

        assert ((exists v0, List.In (TrRecv (n0, Q) v0) MQ) \/ ~ (exists v0, List.In (TrRecv (n0, Q) v0) MQ)) as [|].
        {
          clear.
          induction MQ.
          right; eattac.
          kill IHMQ; eattac.
          destruct a.
          - right; eattac.
          - destruct (NChan_eq_dec (n0, Q) n); subst.
            + left; eattac.
            + right; eattac.
          - right; eattac.
        }
        1: eattac.

        left.
        simpl in *.
        enough (NoRecvQ_from n0 (MQ ++ [EvRecv (n2, R) p])).
        {
          consider (KIC MN0).
          specialize (H_wait_C n0 n1 ltac:(auto)).
          ltac1:(autounfold with LTS_get in * ).
          attac.
        }

        intros ? ?.
        consider (List.In (TrRecv (n0, Q) v0) MQ \/ List.In _ [EvRecv (n2, R) p])
          by (eauto using in_app_or).

        eattac.
      + enough (NoRecvQ_from n0 (MQ ++ [EvRecv (n2, R) p])).
        {
          consider (KIC MN0).
          specialize (H_wait_C n0 n1 ltac:(auto)).
          ltac1:(autounfold with LTS_get in * ).
          attac.
        }
        enough (NoRecvQ_from n0 MQ).
        {
          intros ? ?.
          consider (List.In (TrRecv (n0, Q) v) MQ \/ List.In _ [EvRecv (n2, R) p])
            by eauto using in_app_or.
          bullshit.
        }
        hsimpl in *.
        intros ? ?.

        unfold net_deinstr in *.
        compat_hsimpl in *.
        destruct S1 as [I1 P1 O1].

        enough (~ List.In (n0, Q, v) &I).
        {
          eattac. eapply H6.
          unfold deinstr in *.
          eattac.
        }

        assert (proc_client n0 P).
        {
          unfold deinstr in *.
          eattac.
        }
        assert (NetMod.get n1 '' MN0 = pq &I P &O).
        {
          rewrite <- `(_ = pq &I P &O).
          unfold net_deinstr, deinstr; hsimpl in *; hsimpl in *; attac.
        }
        eauto with LTS.

      + enough (NoRecvQ_from n0 (MQ ++ [EvRecv (n2, R) p])).
        {
          consider (KIC MN0).
          specialize (H_wait_C n0 n1 ltac:(auto)).
          ltac1:(autounfold with LTS_get in * ).
          attac.
        }
        enough (NoRecvQ_from n0 MQ).
        {
          intros ? ?.
          consider (List.In (TrRecv (n0, Q) v0) MQ \/ List.In _ [EvRecv (n2, R) p])
            by eauto using in_app_or.
          bullshit.
        }
        hsimpl in *.
        intros ? ?.

        unfold net_deinstr in *.
        compat_hsimpl in *.
        destruct S1 as [I1 P1 O1].

        enough (~ List.In (n0, Q, v0) &I).
        {
          eattac. eapply H6.
          unfold deinstr in *.
          eattac.
        }

        assert (List.In (n0, R, v) &O).
        {
          unfold deinstr in *.
          eattac.
        }
        assert (NetMod.get n1 '' MN0 = pq &I P &O).
        {
          rewrite <- `(_ = pq &I P &O).
          unfold net_deinstr, deinstr; hsimpl in *; hsimpl in *; attac.
        }
        eauto with LTS.
  Qed.


  Lemma probe_pass_on [MN0 MN1 : MNet] [n0 n1 n2] [p] :
    KIC MN0 ->
    net_lock_on '' MN0 n0 n1 ->
    net_lock_on '' MN0 n1 n2 ->
    init p <> n1 ->
    (MN0 =(NComm n2 n1 R ^ p)=> MN1) ->
    sends_probe (n0, R) p (NetMod.get n1 MN1).

  Proof.
    intros.

    (* TODO Merge with sends_probe_prop_foreign;
         instead of entire KIC, bring whatever you can and should click
     *)

    (* destruct (NetMod.get n1 MN0) as [MQ0 [h0 s0] S0] eqn:?. *)
    (* assert (exists MQ1 M1 S1, NetMod.get n1 MN1 = mq (MQ1 ++ [EvRecv (n2, R) p]) M1 S1). *)
    (* { *)
    (*   consider (MN0 =(_)=> _). compat_hsimpl in *. *)
    (*   eattac. *)
    (* } *)

    (* eapply sends_probe_prop_foreign. *)

    destruct (NetMod.get n1 MN1) as [MQ0 [h0 s0] S0] eqn:?.
    assert (Rad_net MN0) by eauto with LTS.
    consider (h0 = Rad_handle)
      by (assert (Rad_net MN0) by eauto with LTS; eauto with LTS).

    assert (net_sane '' MN1)
      by ((consider (exists ppath, '' MN0 =[ppath]=> '' MN1)
            by eauto using Net_path_corr with LTS); eauto with LTS).

    assert (net_lock_on '' MN1 n0 n1).
    {
      destruct (net_sane_lock_dec '' MN1 n0 n1); auto.
      assert (exists v, NComm n2 n1 R ^ p = NComm n1 n0 R (MValP v)) by eauto using SRPC_M_net_unlock_reply with LTS.
      hsimpl in *; bullshit.
    }
    assert (net_lock_on '' MN1 n1 n2).
    {
      destruct (net_sane_lock_dec '' MN1 n1 n2); auto.
      assert (exists v, NComm n2 n1 R ^ p = NComm n2 n1 R (MValP v)) by eauto using SRPC_M_net_unlock_reply with LTS.
      hsimpl in *; bullshit.
    }

    assert (NoRecvR_MQ (get_MQ MN1 n1)) by eauto using locked_M_NoRecvR with LTS.

    assert (NoSends_MQ (get_MQ MN1 n1)).
    {
      assert (no_sends_in n1 MN1) by eauto using net_lock_on_M_no_sends_in.  (* TODO hint resolve *)
      unfold no_sends_in, NoTrSend in *.
      unfold get_MQ. destruct (NetMod.get n1 MN1) eqn:?; auto.
    }
    assert (_of lock MN1 n1 = Some n2) by eauto using KIC_invariant_H_lock with LTS.
    assert (_of lock MN1 n1 = Some n2) by eauto using KIC_invariant_H_lock with LTS.
    assert (pq_client n0 (NetMod.get n1 '' MN1)) by eauto with LTS.
    assert (_of waitees MN1 n1 = _of waitees MN0 n1).
    {
      clear - H3. kill H3; hsimpl in *.
      destruct M; simpl in *.
      ltac1:(autounfold with LTS_get in * ).
      smash_eq n1 n2; attac.
    }
    assert (Rad_net MN1) by eauto with LTS.
    assert (NoRecvQ_from n0 (get_MQ MN1 n1) -> List.In n0 (_of waitees MN1 n1))
      by eauto using KIC_invariant_H_wait with LTS.

    kill H3.
    assert (Rad_net N0') by eauto with LTS.
    hsimpl in *.
    hsimpl in |- *.
    assert (handle M1 = Rad_handle) by eauto with LTS.
    destruct M1.
    simpl in *; hsimpl in *.

    assert (n1 = self (next_state s0)).
    {
      consider (KIC MN0).
      ltac1:(autounfold with LTS_get in * ).
      clear - H16 H17 H_self_C.
      specialize (H_self_C n1).
      smash_eq n1 n2; hsimpl in * |- ; eattac.
    }

    eapply sends_probe_prop_skip; eauto with LTS; subst.

    consider (pq_client n0 _).
    * unfold net_deinstr in *.
      compat_hsimpl in H20.
      destruct S0.
      hsimpl in H20.

      assert ((exists v0, List.In (TrRecv (n0, Q) v0) MQ) \/ ~ (exists v0, List.In (TrRecv (n0, Q) v0) MQ)) as [|].
      {
        clear.
        induction MQ.
        right; eattac.
        kill IHMQ; eattac.
        destruct a.
        - right; eattac.
        - destruct (NChan_eq_dec (n0, Q) n); subst.
          + left; eattac.
          + right; eattac.
        - right; eattac.
      }
      1: eattac.

      left.
      simpl in *.
      enough (NoRecvQ_from n0 (MQ ++ [EvRecv (n2, R) p])) by eauto.
      intros ? ?.
      apply in_app_or in H20 as [|].
      2: bullshit.

      eattac.

    (* * enough (NoRecvQ_from n0 (MQ ++ [EvRecv (n2, R) p])) by eauto. *)
    (*   enough (NoRecvQ_from n0 MQ) *)
    (*     by (intros ? ?; apply in_app_or in H21 as [|]; bullshit). *)
    (*   (* clear - H16 H17 H H10 H20. *) *)
    (*   hsimpl in *. *)
    (*   intros ?. *)

    (*   unfold net_deinstr in *. *)
    (*   compat_hsimpl in *. *)
    (*   destruct S0, P0. *)
    (*   hsimpl in *. *)

    (*   destruct (NetMod.get (self (next_state s0)) '' MN0) as [I0 P0 O0] eqn:?. *)
    (*   enough (~ List.In (n0, Q, v) I0). *)
    (*   { *)
    (*     eattac. *)
    (*     absurd (List.In (n0, Q, v) I0); auto. *)
    (*     unfold net_deinstr in *. *)
    (*     compat_hsimpl in *. *)
    (*     unfold deinstr in *. *)

    (*     remember (self (next_state s0)) as n1. *)
    (*     smash_eq n1 n2; hsimpl in *. *)
    (*     - apply in_or_app. eattac. *)
    (*     - rewrite `(NetMod.get (self (next_state s0)) MN0 = _) in *. *)
    (*       hsimpl in *. *)
    (*       apply in_or_app. eattac. *)
    (*   } *)
    (*   enough (proc_client n0 P0) by eauto with LTS. *)

    (*   unfold net_deinstr, deinstr in *. *)
    (*   hsimpl in *. *)

    (*   remember (self (next_state s0)) as n1. *)
    (*   smash_eq n1 n2; hsimpl in *; eattac. *)

    (* * enough (NoRecvQ_from n0 (MQ ++ [EvRecv (n2, R) p])) by eauto. *)
    (*   enough (NoRecvQ_from n0 MQ) *)
    (*     by (intros ? ?; apply in_app_or in H21 as [|]; bullshit). *)
    (*   hsimpl in *. *)
    (*   intros ?. *)

    (*   unfold net_deinstr in *. *)
    (*   compat_hsimpl in *. *)
    (*   destruct S0, P0. *)
    (*   hsimpl in *. *)

    (*   destruct (NetMod.get (self (next_state s0)) '' MN0) as [I0 P0 O0] eqn:?. *)
    (*   enough (~ List.In (n0, Q, v0) I0). *)
    (*   { *)
    (*     eattac. *)
    (*     absurd (List.In (n0, Q, v0) (MQ_r MQ)); auto using MQ_r_In. *)

    (*     unfold net_deinstr in *. *)
    (*     compat_hsimpl in *. *)
    (*     unfold deinstr in *. *)

    (*     remember (self (next_state s0)) as n1. *)
    (*     smash_eq n1 n2; hsimpl in *; attac. *)
    (*   } *)
    (*   enough (List.In (n0, R, v) O0) by attac. *)

    (*   unfold net_deinstr, deinstr in *. *)
    (*   compat_hsimpl in *. *)

    (*   remember (self (next_state s0)) as n1. *)
    (*   smash_eq n1 n2; destruct `(_ \/ _); hsimpl in *; eattac. *)
  Qed.


  Lemma KIC_invariant_H_alarm [MN0 MN1 : MNet] [a] [n0] :
    KIC MN0 ->
    (MN0 =(a)=> MN1) ->
    deadlocked n0 '' MN1 ->
    exists n1, dep_on '' MN1 n0 n1 /\ ac n1 MN1.

  Proof.
    intros.
    have (net_sane '' MN0) by eauto with LTS.
    have (net_sane '' MN1) by eauto with LTS.
    consider (exists n0', dep_on '' MN1 n0 n0' /\ dep_on '' MN1 n0' n0')
      by re_have (eauto using deadlocked_dep_on_loop with LTS).

    assert (Rad_net MN1) by (consider (KIC MN0); eauto with LTS).

    enough (exists n1, dep_on '' MN1 n0' n1 /\ ac n1 MN1) by (hsimpl in *; exists n1; eattac).
    clear H1 n0 H4.
    rename n0' into n0.

    assert (dep_on '' MN0 n0 n0 \/ ~ dep_on '' MN0 n0 n0) as [|] by consider (KIC MN0).
    - consider (exists m, dep_on '' MN0 n0 m /\ ac m MN0) by (consider (KIC MN0); auto).
      assert (deadlocked n0 '' MN0) by eauto using dep_self_deadlocked with LTS.
      assert (dep_on '' MN1 n0 m) by eauto using deadlocked_M_dep_invariant1 with LTS.

      consider (ac m MN0).
      + exists m.
        split; eauto 2 with LTS.
        constructor 1.
        consider (KIC MN0).
        eauto using net_preserve_alarm.
      + assert (Rad_MQued (NetMod.get m' MN1)) by eauto with LTS.
        assert (sends_probe (m0, R) (hot_of MN0 m) (NetMod.get m' MN1) \/ ~ sends_probe (m0, R) (hot_of MN0 m) (NetMod.get m' MN1))
          as [|] by eauto using sends_probe_dec.
        * exists m.
          split; auto.

          assert (hot_of MN0 m = hot_of MN1 m) by eauto 3 using deadlocked_preserve_hot_of1 with LTS.
          rewrite `(hot_of _ _ = _) in *.

          assert (deadlocked m '' MN0) by eauto 3 with LTS.
          assert (deadlocked m0 '' MN0) by (consider (m = m0 \/ _); eauto 3 with LTS).
          econstructor 2. 3: eauto.
          consider (m = m0 \/ dep_on '' MN0 m m0) by attac > [left|right]; auto.
          -- eauto 3 using deadlocked_M_dep_invariant1 with LTS.
          -- consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr1; eauto 2 with LTS.
        * exists m.
          split; auto.

          consider (a = NComm m' m0 R ^ (hot_of MN0 m)) by eauto using sends_probe_sent with LTS.
          smash_eq m0 m.
          -- constructor 3 with (n':=m'); eauto.
             1: consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr with LTS; eauto 4 with LTS.

             clear - H0.
             kill H0. hsimpl in *.
             unfold hot_ev_of, hot_of in *.
             ltac1:(autounfold with LTS_get in * ).
             hsimpl in |- *.
             smash_eq m0 m'; attac.
             rewrite H. attac.
          -- destruct `(m = m0 \/ dep_on '' MN0 m m0).
             1: bullshit.

             assert (deadlocked m0 '' MN0) by eauto 3 with LTS.
             assert (deadlocked m '' MN0) by eauto 3 with LTS.
             assert (exists m'', dep_on '' MN0 m m'' /\ net_lock_on '' MN0 m'' m0).
             {
               apply dep_lock_chain in H10. hsimpl in H10.
               ltac1:(rev_induction L); intros; hsimpl in *.
               - exists m.
                 split; auto.
                 eapply dep_reloop; re_have (eauto with LTS).
               - exists a; split; eauto.
                 eauto using lock_chain_dep.
             } (* TODO TO LEMMA *)
             (* TODO deadlocked_M_lock_on_invariant *)
             hsimpl in H16.

             assert (~ hot MN0 (hot_of MN0 m) m0) by (intros Hx; kill Hx).
             assert (sends_probe (m'', R) (hot_of MN0 m) (NetMod.get m0 MN1)) by eauto using probe_pass_on.

             assert (dep_on '' MN1 m m'') by eauto 4 using deadlocked_M_dep_invariant1 with LTS.

             assert (net_lock_on '' MN1 m'' m0) by
               (consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr1;
                eauto 4 using deadlocked_lock_on_invariant with LTS
               ).
             assert (dep_on '' MN1 m m0) by eauto 4 using deadlocked_M_dep_invariant1 with LTS.

             econstructor 2.
             3: replace (hot_of MN1 m) with (hot_of MN0 m) by eauto 3 using deadlocked_preserve_hot_of1 with LTS.
             3: eauto 4 with LTS.
             all: auto.
      + exists m.
        split; auto.

        assert (_of lock MN0 m = Some n') by eauto with LTS.
        assert (deadlocked m '' MN0) by eauto 3 with LTS.
        assert (net_lock_on '' MN1 m n')
          by (consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr with LTS; eauto 4 with LTS).
        assert (net_sane '' MN1)
          by (consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr with LTS; eauto 4 with LTS).

        assert (hot_ev_of MN1 n' m = hot_ev_of MN0 n' m).
        {
          unfold hot_ev_of.
          consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr with LTS.
          replace (hot_of MN1 m) with (hot_of MN0 m) by eauto using deadlocked_preserve_hot_of1, eq_sym with LTS.
          auto.
        }

        kill H0.
        * smash_eq m n.
          2: econstructor 3; eauto; unfold get_MQ in *; replace (NetMod.get m MN1) with (NetMod.get m MN0) by eauto using NV_stay, eq_sym; rewrite `(hot_ev_of _ _ _ = _); eauto.

          apply in_split in H11. hsimpl in H11.

          unfold hot_ev_of, hot_of in *.
          ltac1:(autounfold with LTS_get in * ).

          destruct_ma &a0; doubt; compat_hsimpl in *.
          -- exfalso.
             absurd (no_sends_in m (NetMod.put m
                                      (mq
                                         ((l1 ++
                                             EvRecv (n', R) {| init := m; index := lock_id (next_state (state M)) |}
                                             :: l2) ++ [TrSend (n, &t) v]) M (pq I0 P2 O1)) MN0)).
             2: eauto using net_lock_on_M_no_sends_in.

             intros Hx. clear - Hx.
             unfold no_sends_in, NoTrSend in *.
             compat_hsimpl in *. bullshit.

          -- simpl in *.
             assert (self s = m).
             {
               clear - H H17.
               consider (KIC MN0).
               specialize (H_self_C m).
               ltac1:(autounfold with LTS_get in * ).
               rewrite `(NetMod.get m MN0 = _) in *.
               eattac.
             }
             (* clear - H6 H9 H11 H13 H15. *)
             destruct l1.
             1: bullshit.

             consider ((e :: _) ++ _ = TrRecv _ _ :: _).
             econstructor 3; eauto.
             unfold hot_ev_of, hot_of.
             ltac1:(autounfold with LTS_get in * ).
             ltac1:(autorewrite with LTS in * ).

             rewrite <- H15; clear H15.
             hsimpl in *.

             unfold next_state.
             right; left.
             f_equal. f_equal.
             cbv; now rewrite Heqm.

          -- exfalso.
             clear - H H10 H17 H19 H20.
             destruct P0 as [I0 P0 O0].
             apply lock_singleton in H10. 2: attac.
             unfold net_lock in *.
             destruct (NetMod.get m '' MN0) as [I0' P0' O0'] eqn:?.
             unfold net_deinstr in *.
             ltac1:(autorewrite with LTS in * ).
             rewrite `(NetMod.get m MN0 = _) in *.
             kill H10.
             unfold deinstr in *.
             hsimpl in *.
             clear - H1 H19 H2 Heqp.
             kill H19; hsimpl in *; attac.

             eapply SRPC_net_lock_uniq; eauto with LTS.
             eauto with LTS.
          -- bullshit.
          -- simpl in *.
             assert (self s = m).
             {
               clear - H H17.
               consider (KIC MN0).
               specialize (H_self_C m).
               ltac1:(autounfold with LTS_get in * ).
               rewrite `(NetMod.get m MN0 = _) in *.
               eattac.
             }
             clear - H6 H7 H10 H11 H13 H15 H0.
             destruct l1.
             ++ assert (h = Rad_handle) by (specialize (H6 m); eattac). subst.
                econstructor 1.
                ltac1:(autorewrite with LTS in * ).
                hsimpl in *.
                destruct s; simpl in *; subst. hsimpl in *.
                hsimpl in |- *. rewrite PeanoNat.Nat.eqb_refl in *. attac.
             ++ kill H11.
                destruct n.
                econstructor 3; eauto.
                unfold hot_ev_of, hot_of.
                ltac1:(autounfold with LTS_get in * ).
                ltac1:(autorewrite with LTS in * ).
                simpl.
                right; left.
                f_equal; f_equal.
                cbv; rewrite <- H15.
                attac.
        * constructor 3 with (n':=n').
          1: auto.
          rewrite `(hot_ev_of _ _ _ = _).
          clear - H11 H16 H17.
          hsimpl in *. hsimpl in *.
          unfold hot_ev_of, hot_of in *.
          ltac1:(autounfold with LTS_get in * ).
          all: smash_eq m n n'0; destruct v; hsimpl in *; hsimpl in |- *;
            try (rewrite `(NetMod.get m _ = _) in * );
            try (rewrite `(NetMod.get n _ = _) in * );
            try (rewrite `(NetMod.get n'0 _ = _) in * ); hsimpl in *; doubt.
          all: eattac.

    - assert (deadlocked n0 '' MN1) by re_have (eauto using dep_self_deadlocked).
      consider (exists m0 m1 v, (n0 = m0 \/ dep_on '' MN1 n0 m0) /\ a = NComm m0 m1 Q (MValP v)).
      {
        consider (exists (m0 m1 : Name) (v : Val),
                     a = NComm m0 m1 Q # v /\
                       (m0 = n0 \/ m0 <> n0 /\ dep_on '' MN0 n0 m0 /\ dep_on '' MN1 n0 m0) /\
                       (m1 = n0 \/ m1 <> n0 /\ dep_on '' MN0 m1 n0 /\ dep_on '' MN1 m1 n0))
          by re_have (eauto 2 using net_M_dep_close).
        do 2 (destruct `(_ \/ _)); eattac.
      }

      assert (net_lock_on '' MN1 m0 m1)
        by (consider (~ net_lock_on '' MN0 m0 m1 /\ net_lock_on '' MN1 m0 m1);
            eauto using SRPC_M_net_query_new_lock with LTS).

      exists m1.
      split.
      1: kill H7; eauto with LTS.

      assert (dep_on '' MN1 n0 m0) by
        (destruct `(n0 = m0 \/ dep_on '' MN1 n0 m0); subst; eauto 4 using dep_reloop, dep_loop, dep_on_seq1 with LTS).
      assert (forall n : Name, AnySRPC_pq (NetMod.get n '' MN1)) by re_have (eauto with LTS).
      assert (sends_probe (m0, R) (hot_of MN1 m1) (NetMod.get m1 MN1)).
      {
        assert (deadlocked m1 '' MN1) by eauto 4 using dep_self_deadlocked with LTS.
        destruct (NetMod.get m1 MN1) as [MQ1 [h1 s1] S1] eqn:?.
        consider (exists m2, net_lock_on '' MN1 m1 m2) by re_have (eauto 3 using deadlocked_M_get_lock with LTS).

        assert (NoRecvR_MQ (get_MQ MN1 m1)) by re_have (eauto using deadlocked_M_NoRecvR with LTS).
        assert (NoSends_MQ (get_MQ MN1 m1)).
        {
          assert (no_sends_in m1 MN1) by eauto using net_lock_on_M_no_sends_in.
          ltac1:(autounfold with LTS_get).
          unfold no_sends_in, NoTrSend in *.
          destruct (NetMod.get m1 MN1).
          auto.
        }
        assert (lock (next_state s1) = Some m2).
        {
          assert (_of lock MN1 m1 = Some m2) by eauto using KIC_invariant_H_lock with LTS.
          ltac1:(autounfold with LTS_get in * ).
          rewrite `(NetMod.get m1 MN1 = _) in *.
          auto.
        }
        assert (h1 = Rad_handle) by (specialize (H6 m1); unfold Rad_MQued; rewrite `(NetMod.get m1 MN1 = _) in *; auto).
        assert (m1 = self (next_state s1)); subst.
        {
          consider (m1 = _of self MN0 m1) by consider (KIC MN0).
          replace (_of self MN0 m1) with (_of self MN1 m1) by (consider (KIC MN0); eauto using net_preserve_self, eq_sym with LTS); auto.
          ltac1:(autounfold with LTS_get in * ).
          rewrite `(NetMod.get m1 MN1 = _).
          auto.
        }

        consider (exists MQ1', MQ1 = MQ1' ++ [TrRecv (m0, Q) v]) by (clear - H0 Heqm; kill H0; eattac).
        clear - H12 H13 H14 H15 Heqm.

        unfold hot_of in *.
        ltac1:(autounfold with LTS_get in * ).
        rewrite `(NetMod.get (self (next_state s1)) MN1 = _) in *.
        clear Heqm.

        induction s1; simpl in *.
        1: eattac.

        destruct
          (NChan_eq_dec to (m0, R)),
          (MProbe_eq_dec msg {| init := self (next_state s1); index := lock_id (next_state s1) |}); subst;
          eauto with LTS.
      }

      econstructor 2. 3: eauto. all: eauto.
      right.
      destruct `(n0 = m0 \/ dep_on '' MN1 n0 m0); subst; eauto 4 using dep_reloop, dep_loop, dep_on_seq1 with LTS.
  Qed.


  Theorem KIC_invariant : trans_invariant KIC always.

  Proof.
    unfold trans_invariant; intros. hsimpl in *.
    rename N0 into MN0.
    rename N1 into MN1.

    assert (net_sane '' MN0) by eauto with LTS.
    assert (net_sane '' MN1) by eauto with LTS.

    assert (forall n, _of self MN1 n = n) as H_self_C1.
    {
      intros.
      consider (KIC MN0).
      replace (_of self MN1 n) with (_of self MN0 n) by eauto using net_preserve_self with LTS.
      auto.
    }

    assert (forall n : Name, handle (get_M MN1 n) = Rad_handle) as H_Rad_C1.
    {
      intros.
      consider (KIC MN0).
      replace (handle (get_M MN1 n)) with (handle (get_M MN0 n)) by eauto using net_preserve_handle.
      auto.
    }

    constructor; auto with LTS; intros.
    - eauto using KIC_invariant_H_lock with LTS.
    - eauto using KIC_invariant_H_wait with LTS.
    - eauto using KIC_invariant_H_alarm, dep_self_deadlocked with LTS.
    - (* TODO to lemma *)
      destruct (MNAct_to_PNAct a) eqn:?.
      + assert ('' MN0 =(p)=> '' MN1) by eauto using net_deinstr_act_do.
        consider (KIC MN0).
        eauto using invariant_dep_dec1 with LTS.
      + replace ('' MN1) with ('' MN0) by eauto using net_deinstr_act_skip.
        consider (KIC MN0).
  Qed.

  Hint Resolve KIC_invariant : LTS inv.
  Hint Extern 0 (KIC _) => solve_invariant : LTS.


  Lemma make_ready MN0 n :
    exists mpath MN1,
      (MN0 =[mpath]=> MN1)
      /\ ready_in n MN1
      /\ forall m MQ M S, NetMod.get m MN0 = mq MQ M S ->
                    exists MQ' M', NetMod.get m MN1 = mq (MQ ++ MQ') M' S
                              /\ (n <> m -> M' = M)
                              /\ MQ_Clear MQ'.

  Proof.
    intros.
    unfold ready_in, ready_q, ready in *.
    destruct (NetMod.get n MN0) as [MQ0 [h s] S0] eqn:?.

    remember ([] : list Event) as MQ0'.
    replace MQ0 with (MQ0 ++ MQ0') by attac.
    assert (MQ_Clear MQ0') by attac.
    clear HeqMQ0'.

    generalize dependent MN0 MQ0 MQ0'.

    induction s; intros.
    1: exists [], MN0; eattac; exists []; eattac.

    assert (exists MN1 na MQ1',
               (MN0 =(na)=> MN1)
               /\ MQ_Clear MQ0'
               /\ NetMod.get n MN1 = mq (MQ0 ++ MQ1') {| handle := h; state := s |} S0
               /\ (forall m MQ M S,
                     NetMod.get m MN0 = mq MQ M S ->
                     exists MQ' M',
                       NetMod.get m MN1 = mq (MQ ++ MQ') M' S
                       /\ (n <> m -> M' = M)
                       /\ MQ_Clear MQ')).
    {
      clear - Heqm H.
      destruct to as [n' t'].
      pose (NetMod.put n (mq (MQ0 ++ MQ0') {| handle := h; state := s|} S0) MN0) as MN1'.
      destruct (NetMod.get n' MN1') as [MQ M S] eqn:?.
      exists (NetMod.put n' (mq (MQ ++ [EvRecv (n, t') msg]) M &S) MN1').
      exists (NComm n n' t' ^ msg).
      smash_eq n n'.
      - exists (MQ0' ++ [EvRecv (n, t') msg]).
        repeat split; compat_hsimpl in |- *; auto.
        + apply NT_Comm with (N0':=MN1'); subst MN1'; attac.
        + subst MN1'.
          rewrite app_assoc.
          eattac.
        + subst MN1'.
          intros.
          hsimpl.
          smash_eq n m; hsimpl in *.
          * exists [EvRecv (n, t') msg]. eexists; eattac.
          * eexists [], _. compat_hsimpl. eattac. (* TODO hsimpl doesn't rewrite app_nil_r? *)
      - exists MQ0'.
        repeat split; hsimpl in |- *; auto.
        + apply NT_Comm with (N0':=MN1'); subst MN1'; attac.
        + subst MN1'. eattac.
        + subst MN1'.
          intros.
          smash_eq_on m n n'; subst; hsimpl in *; hsimpl in |- *.
          * exists [], {| handle := h; state := s |}. eattac.
          * exists [EvRecv (n, t') msg], M. eattac.
          * eexists [], _; compat_hsimpl; eattac.
    }
    hsimpl in *.

    assert (exists (mpath : list MNAct) (MN2 : MNet),
               (MN1 =[ mpath ]=> MN2)
               /\ ready_in n MN2
               /\ (forall m MQ M S,
                      NetMod.get m MN1 = mq MQ M S ->
                      exists MQ' M',
                        NetMod.get m MN2 = mq (MQ ++ MQ') M' S
                        /\ (n <> m -> M' = M)
                        /\ MQ_Clear MQ')).
    {
      consider (exists MQ' M',
                   NetMod.get n MN1 = mq ((MQ0 ++ MQ0') ++ MQ') M' S0
                   /\ (n <> n -> M' = {| handle := h; state := MSend to msg s |})
                   /\ MQ_Clear MQ').
      eapply IHs with (MQ0':=(MQ0' ++ MQ')); eattac.
    }
    compat_hsimpl in *.

    exists (na :: mpath), MN2.
    eattac.

    consider (exists MQ' M',
                 NetMod.get m MN1 = mq (MQ ++ MQ') M' &S
                 /\ (n <> m -> M' = M)
                 /\ MQ_Clear MQ').

    consider (exists MQ'' M'',
                 NetMod.get m MN2 = mq ((MQ ++ MQ') ++ MQ'') M'' &S
                 /\ (n <> m -> M'' = M')
                 /\ MQ_Clear MQ'').

    exists (MQ' ++ MQ''), M''.
    smash_eq m n; hsimpl.
    - rewrite app_assoc; attac.
    - rewrite app_assoc; eattac.
      transitivity '(M'); auto.
  Qed.


  Lemma flush_one1 MN0 e MQ0 h s S0 n :
    NetMod.get n MN0 = mq (e :: MQ0) {|handle:=h;state:=MRecv s|} S0 ->
    exists na MN1 MQ1' S1,
      (MN0 =(na)=> MN1)
      /\ NetMod.get n MN1 = mq (MQ0 ++ MQ1') {|handle:=h;state:=h e s|} S1
      /\ MQ1' = match e with
                | TrSend (m, t) v => if NAME.eqb n m then [TrRecv (n, t) v] else []
                | _ => []
                end
      /\ forall m MQ M S,
        n <> m ->
        NetMod.get m MN0 = mq MQ M S ->
        exists MQ', NetMod.get m MN1 = mq (MQ ++ MQ') M S
                    /\ MQ' =
                         match e with
                         | TrSend (m', t) v => if NAME.eqb m' m then [TrRecv (n, t) v] else []
                         | _ => []
                         end.
  Proof.
    intros.

    pose {|handle:=h; state:=h e s|} as M1.

    destruct e as [[m t]|[m t]|[m p]] > [smash_eq n m| |]; hsimpl in |- *.
    - pose (NetMod.put n (mq MQ0 M1 S0) MN0) as MN0'.
      exists (NComm n n &t # v).
      exists (NetMod.put n (mq (MQ0 ++ [TrRecv (n, &t) v]) M1 S0) MN0').
      exists [TrRecv (n, &t) v].
      exists S0.
      repeat split; intros; auto.
      + apply NT_Comm with (N0':=MN0'); subst MN0' M1; attac.
      + hsimpl in |- *. subst MN0' M1. auto.
      + smash_eq n m; hsimpl in *; doubt.
        subst MN0'.
        hsimpl in |- *.
        exists [].
        eattac.
    - pose (NetMod.put n (mq MQ0 M1 S0) MN0) as MN0'.
      destruct (NetMod.get m MN0') as [MQm Mm Sm] eqn:?.
      exists (NComm n m &t # v).
      exists (NetMod.put m (mq (MQm ++ [TrRecv (n, &t) v]) Mm Sm) MN0').
      exists [].
      exists S0.
      repeat split; intros; auto.
      + apply NT_Comm with (N0':=MN0'); subst MN0' M1; attac.
      + hsimpl in |- *. subst MN0' M1. attac.
      + subst MN0'.
        smash_eq_on m0 m n; subst; hsimpl in *; hsimpl in |- *; eexists; eattac.
    - destruct S0 as [I0 P0 O0].
      pose (NetMod.put n (mq MQ0 M1 (pq (I0 ++ [(m, &t, v)]) P0 O0)) MN0) as MN0'.
      exists (NTau n (MActP (Recv (m, &t) v))).
      exists MN0'.
      exists [].
      exists (pq (I0 ++ [(m, &t, v)]) P0 O0).
      subst MN0' M1; attac.
      constructor. attac. constructor. rewrite H. attac.
      eexists. eattac.
    - pose (NetMod.put n (mq MQ0 M1 S0) MN0) as MN0'.
      exists (NTau n (MActM Tau)).
      exists MN0'.
      exists [].
      exists S0.
      subst MN0' M1; attac.
      constructor. attac. constructor. rewrite H. attac.
      eexists. eattac.
  Qed.


  Lemma flush_ready_one1 MN0 e MQ0 M0 S0 n :
    NetMod.get n MN0 = mq (e :: MQ0) M0 S0 ->
    exists mpath MN1 MQ1' M1 S1,
      (MN0 =[mpath]=> MN1)
      /\ NetMod.get n MN1 = mq (MQ0 ++ MQ1') M1 S1
      /\ Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ1'
      /\ ((forall t v, e <> TrSend (n, t) v) -> MQ_Clear MQ1')
      /\ forall m MQ M S,
        n <> m ->
        NetMod.get m MN0 = mq MQ M S ->
        exists MQ', NetMod.get m MN1 = mq (MQ ++ MQ') M S
                    /\ Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ'
                    /\ ((forall t v, e <> TrSend (m, t) v) -> MQ_Clear MQ').

  Proof.
    intros.

    enough (exists mpath0 MN1,
               (MN0 =[mpath0]=> MN1)
               /\ ready_in n MN1
               /\ forall m MQ M S,
                 NetMod.get m MN0 = mq MQ M S ->
                 exists MQ' M', NetMod.get m MN1 = mq (MQ ++ MQ') M' S
                                /\ (n <> m -> M' = M)
                                /\ (Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ')
                                /\ ((forall t v, e <> TrSend (m, t) v) -> MQ_Clear MQ')
           ) as Hx.
    {
      hsimpl in Hx.
      consider (exists MQ' M1, NetMod.get n MN1 = mq ((e :: MQ0) ++ MQ') M1 S0 /\ (n <> n -> M1 = M0)
                               /\ (Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ')
                               /\ ((forall t v, e <> TrSend (n, t) v) -> MQ_Clear MQ')).
      unfold ready_in, ready_q in *.

      hsimpl in *.

      specialize (flush_one1 MN1 e (MQ0 ++ MQ') h s S0 n ltac:(auto)) as Hxx.
      hsimpl in Hxx.

      exists (mpath0 ++ [na]), MN2.
      destruct e as [[n0 t]|?|?] eqn:? > [smash_eq n n0 | |].
      1: (exists (MQ' ++ [TrRecv (n, &t) v])).
      2-4: (exists MQ').
      all: (exists {| handle := h; state := h e s |}, S1).
      - rewrite app_assoc; attac.
        specialize (Hx1 m MQ M &S ltac:(auto)). hsimpl in Hx1.
        specialize (Hxx2 m (MQ ++ MQ'0) M' &S ltac:(auto) ltac:(auto)).
        hsimpl in Hxx2.
        exists MQ'0.
        replace M with M' by auto.
        eattac.
      - attac.
        specialize (Hx1 m MQ M &S ltac:(auto)). hsimpl in Hx1.
        specialize (Hxx2 m (MQ ++ MQ'0) M' &S ltac:(auto) ltac:(auto)).
        hsimpl in Hxx2.
        replace M with M' by auto.
        exists (MQ'0 ++ if NAME.eqb n0 m then [TrRecv (n, &t) v] else []).
        rewrite app_assoc. eattac.
        smash_eq n0 m; hsimpl in |- *; split; attac.
        smash_eq n0 m; attac.
      - attac.
        specialize (Hx1 m MQ M &S ltac:(auto)). hsimpl in Hx1.
        specialize (Hxx2 m (MQ ++ MQ'0) M' &S ltac:(auto) ltac:(auto)).
        hsimpl in Hxx2.
        replace M with M' by auto.
        exists MQ'0.
        eattac.
      - attac.
        specialize (Hx1 m0 MQ M &S ltac:(auto)). hsimpl in Hx1.
        specialize (Hxx2 m0 (MQ ++ MQ'0) M' &S ltac:(auto) ltac:(auto)).
        hsimpl in Hxx2.
        replace M with M' by auto.
        exists MQ'0.
        eattac.
    }

    specialize (make_ready MN0 n) as ?.
    hsimpl in *.
    exists mpath, MN1.
    eattac.

    consider (exists (MQ' : list Event) (M' : Mon), NetMod.get m MN1 = mq (MQ ++ MQ') M' &S /\ (n <> m -> M' = M) /\ MQ_Clear MQ').
    eexists MQ', M'.
    eattac.
  Qed.


  Lemma flush_one_w_sends MN0 n :
    exists mpath MN1,
      (MN0 =[mpath]=> MN1)
      /\ no_sends_in n MN1
      /\ forall m MQ M S,
        n <> m ->
        NetMod.get m MN0 = mq MQ M S ->
        exists MQ', NetMod.get m MN1 = mq (MQ ++ MQ') M S
                    /\ Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ'.

  Proof.
    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.

    remember ([] : list Event) as MQ0'.
    replace MQ0 with (MQ0 ++ MQ0') by attac.
    assert (Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ0') by attac.
    clear HeqMQ0'.

    generalize dependent MN0 MQ0' M0 S0.
    induction MQ0; intros.
    {
      unfold no_sends_in, NoTrSend, flushed_in, Flushed in *.
      exists [], MN0.
      hsimpl in *. hsimpl in |- *.
      eattac.
      exists []. eattac.
    }

    specialize (flush_ready_one1 MN0 a (MQ0 ++ MQ0') M0 S0 n ltac:(auto)) as ?.
    hsimpl in *.

    normalize_hyp @IHMQ0.
    specialize (IHMQ0 S1 M1 (MQ0' ++ MQ1') MN1).
    rewrite app_assoc in IHMQ0.
    specialize (IHMQ0 ltac:(attac) ltac:(attac)).
    hsimpl in IHMQ0.

    exists (mpath ++ mpath0), MN2.
    eattac.

    specialize (H4 m MQ M &S ltac:(auto) ltac:(auto)).
    hsimpl in H4.

    specialize (IHMQ2 m (MQ ++ MQ') M &S ltac:(auto) ltac:(auto)).
    hsimpl in IHMQ2.

    exists (MQ' ++ MQ'0).

    rewrite app_assoc; eattac.
  Qed.


  Lemma flush_one_wo_sends MN0 n :
    no_sends_in n MN0 ->
    exists mpath MN1,
      (MN0 =[mpath]=> MN1)
      /\ flushed_in n MN1
      /\ forall m MQ M S,
        n <> m ->
        NetMod.get m MN0 = mq MQ M S ->
        exists MQ', NetMod.get m MN1 = mq (MQ ++ MQ') M S
                    /\ MQ_Clear MQ'.

  Proof.
    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.

    remember ([] : list Event) as MQ0'.
    replace MQ0 with (MQ0 ++ MQ0') by attac.
    assert (MQ_Clear MQ0') by attac.
    clear HeqMQ0'.

    generalize dependent MN0 MQ0' M0 S0.
    induction MQ0; intros.
    {
      unfold no_sends_in, NoTrSend, flushed_in, Flushed in *.
      exists [], MN0.
      hsimpl in *. hsimpl in |- *.
      eattac.
      exists []. eattac.
    }

    specialize (flush_ready_one1 MN0 a (MQ0 ++ MQ0') M0 S0 n ltac:(auto)) as ?.
    hsimpl in *.

    normalize_hyp @IHMQ0.
    specialize (IHMQ0 S1 M1 (MQ0' ++ MQ1') MN1).

    assert (MQ_Clear (MQ0' ++ MQ1')).
    {
      enough (forall (t : Tag) v, a <> TrSend (n, t) v) by attac.
      intros.
      unfold no_sends_in, NoTrSend in *.
      rewrite Heqm in H0.
      destruct a; attac.
    }

    assert (no_sends_in n MN1) by (unfold no_sends_in, NoTrSend in *; attac).

    rewrite app_assoc in IHMQ0.
    specialize (IHMQ0 ltac:(attac)).
    specialize (IHMQ0 ltac:(attac)).
    specialize (IHMQ0 ltac:(attac)).
    hsimpl in *.

    exists (mpath ++ mpath0), MN2.
    eattac.

    specialize (H5 m MQ M &S ltac:(auto) ltac:(auto)).
    hsimpl in H5.

    specialize (IHMQ2 m (MQ ++ MQ') M &S ltac:(auto) ltac:(auto)).
    hsimpl in IHMQ2.

    assert (MQ_Clear (MQ' ++ MQ'0)).
    {
      enough (forall (t : Tag) v, a <> TrSend (m, t) v) by attac.
      intros.
      unfold no_sends_in, NoTrSend in *.
      rewrite Heqm in H0.
      destruct a; attac.
    }

    exists (MQ' ++ MQ'0).

    rewrite app_assoc; eattac.
  Qed.


  Lemma flush_one MN0 n :
    exists mpath MN1,
      (MN0 =[mpath]=> MN1)
      /\ no_sends_in n MN1
      /\ (no_sends_in n MN0 -> flushed_in n MN1)
      /\ forall m MQ M S,
        n <> m ->
        NetMod.get m MN0 = mq MQ M S ->
        exists MQ', NetMod.get m MN1 = mq (MQ ++ MQ') M S
                    /\ Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ'
                    /\ (no_sends_in n MN0 -> MQ_Clear MQ').

  Proof.
    assert (no_sends_in n MN0 \/ ~ no_sends_in n MN0) as [? | ?].
    {
      unfold no_sends_in, NoTrSend.
      destruct (NetMod.get n MN0) as [MQ0 _ _].
      induction MQ0; attac.
      destruct a.
      - right. eattac.
      - destruct IHMQ0. eattac. right. intros ?. eattac.
      - destruct IHMQ0. eattac. right. intros ?. eattac.
    }
    - specialize (flush_one_wo_sends MN0 n ltac:(auto)) as ?.
      hsimpl in *.
      exists mpath, MN1.
      eattac.
      consider (exists MQ', NetMod.get m MN1 = mq (MQ ++ MQ') M &S /\ MQ_Clear MQ').
      eexists; eattac.
    - specialize (flush_one_w_sends MN0 n) as ?.
      hsimpl in *.
      exists mpath, MN1.
      eattac.
      consider (exists MQ' : list Event,
                   NetMod.get m MN1 = mq (MQ ++ MQ') M &S /\
                     Forall (fun e : Event => match e with
                                              | TrSend _ _ => False
                                              | _ => True
                                              end) MQ').
      eexists; eattac.
  Qed.


  Lemma flush_one_until [MN0 n MQ00 MQ01] :
    get_MQ MN0 n = MQ00 ++ MQ01 ->
    exists MQ1' M1 S1 mpath MN1,
      (MN0 =[mpath]=> MN1)
      /\ NetMod.get n MN1 = mq (MQ01 ++ MQ1') M1 S1
      /\ ready M1
      /\ Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ1'
      /\ (Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ00 -> MQ_Clear MQ1')
      /\ forall m MQ M S,
        n <> m ->
        NetMod.get m MN0 = mq MQ M S ->
        exists MQ', NetMod.get m MN1 = mq (MQ ++ MQ') M S
                    /\ Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ'
                    /\ (Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ00 -> MQ_Clear MQ').

  Proof.
    intros.
    unfold get_MQ in *.
    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.
    subst.

    remember ([] : list Event) as MQ0'.
    replace MQ01 with (MQ01 ++ MQ0') by attac.
    assert (Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ0') by attac.
    clear HeqMQ0'.

    generalize dependent MN0 MQ0' M0 S0.
    induction MQ00; intros.
    {
      specialize (make_ready MN0 n) as ?.
      hsimpl in *.
      consider (exists (MQ1' : list Event) (M1 : Mon),
                   NetMod.get n MN1 = mq ((MQ01 ++ MQ0') ++ MQ1') M1 S0 /\ (n <> n -> M1 = M0) /\ MQ_Clear MQ1').
      exists MQ1', M1, S0.
      exists mpath, MN1.

      assert (ready M1) by (unfold ready_in in *; rewrite H3 in H1; attac).
      assert (Forall (fun e0 : Event => match e0 with
                                        | TrSend _ _ => False
                                        | _ => True
                                        end) MQ1') by (clear - H5; induction MQ1'; attac).

      eattac.

      consider (exists (MQ' : list Event) (M' : Mon), NetMod.get m MN1 = mq (MQ ++ MQ') M' &S /\ (n <> m -> M' = M) /\ MQ_Clear MQ').
      exists MQ'.
      replace M with M' by auto.
      eattac.
    }

    specialize (flush_ready_one1 MN0 a (MQ00 ++ MQ01 ++ MQ0') M0 S0 n ltac:(auto)) as ?.
    hsimpl in H0.

    normalize_hyp @IHMQ00.
    specialize (IHMQ00 S1 M1 (MQ0' ++ MQ1') MN1).
    repeat (rewrite app_assoc in * ).

    specialize (IHMQ00 ltac:(attac)).
    specialize (IHMQ00 ltac:(attac)).
    hsimpl in IHMQ00.

    exists (MQ1' ++ MQ1'0), {| handle := h; state := MRecv s |}, S2.
    exists (mpath ++ mpath0), MN2.
    rewrite app_assoc; eattac.
    1: destruct a; attac.

    specialize (H4 m MQ M &S ltac:(auto) ltac:(auto)). hsimpl in H4.
    specialize (IHMQ05 m (MQ ++ MQ') M &S ltac:(auto) ltac:(auto)). hsimpl in IHMQ05.

    exists (MQ' ++ MQ'0).
    rewrite app_assoc; eattac.

    destruct a; attac.
  Qed.


  Lemma flush_one_In [MN0 n e] :
    List.In e (get_MQ MN0 n) ->
    exists MQ00 MQ01 MQ1' M1 S1 mpath MN1,
      (get_MQ MN0 n) = MQ00 ++ e :: MQ01
      /\ (MN0 =[mpath]=> MN1)
      /\ NetMod.get n MN1 = mq (e :: MQ01 ++ MQ1') M1 S1
      /\ ready M1
      /\ Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ1'
      /\ (Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ00 -> MQ_Clear MQ1')
      /\ forall m MQ M S,
        n <> m ->
        NetMod.get m MN0 = mq MQ M S ->
        exists MQ', NetMod.get m MN1 = mq (MQ ++ MQ') M S
                    /\ Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ'
                    /\ (Forall (fun e => match e with TrSend _ _ => False | _ => True end) MQ00 -> MQ_Clear MQ').

  Proof.
    intros HIn.
    apply in_split in HIn as (MQ00 & MQ01 & ?).
    hsimpl in *.
    exists MQ00, MQ01.
    specialize (flush_one_until H) as ?.
    hsimpl in *.
    eexists _, _, _, _, _. eattac.
  Qed.


  Lemma propagation_init [MN0 : MNet] [n n' m] [v ] :
    net_sane '' MN0 ->
    KIC MN0 ->
    deadlocked n '' MN0 ->
    net_lock_on '' MN0 n n' ->
    List.In (TrRecv (m, Q) v) (get_MQ MN0 n) ->
    exists MN1 mpath MQ,
      (MN0 =[mpath]=> MN1)
      /\ get_MQ MN1 m = MQ ++ [hot_ev_of MN1 n n].

  Proof.
    intros.

    assert (exists mpath0 MN1 MQ1 h s S1,
               (MN0 =[mpath0]=> MN1)
               /\ NetMod.get n MN1 = mq (TrRecv (m, Q) v :: MQ1) ({|handle:=h; state:=MRecv s|}) S1
           ) as Hxx'.
    {
      specialize (flush_one_In ltac:(eauto)) as ?.
      hsimpl in *.
      exists mpath, MN1, (MQ01 ++ MQ1'), h, s, S1.
      attac.
    }
    hsimpl in Hxx'.

    assert (exists mpath1 MN2 M2 S2,
               (MN1 =[mpath1]=> MN2)
               /\ NetMod.get n MN2 = mq MQ1 {|handle:=h; state:=MSend (m, R) (hot_of MN2 n) M2|} S2
           ) as Hx.
    {
      assert (h = Rad_handle).
      {
        consider (KIC MN1) by eauto with LTS.
        specialize (H_Rad_C n).
        ltac1:(autounfold with LTS_get in H_Rad_C).
        rewrite `(NetMod.get n MN1 = _) in H_Rad_C.
        auto.
      }

      destruct S1 as [I1 P1 O1].
      pose (pq (I1 ++ [(m, Q, v)]) P1 O1) as S2.
      pose  {|self := self s
            ; lock_id := lock_id s
            ; lock := lock s
            ; waitees := m :: waitees s
            ; alarm := alarm s
            |} as s1.
      pose (NetMod.put n (mq MQ1 {| handle := h; state := h (TrRecv (m, Q) v) s |} S2) MN1) as MN1'.

      exists [NTau n (MActP (Recv (m, Q) v))], MN1', (MRecv s1), S2.

      destruct s.
      subst MN1' s1 S2.

      assert (lock0 <> None).
      {
        consider (KIC MN1) by eauto with LTS.
        consider (exists path, '' MN0 =[path]=> '' MN1) by eauto using Net_path_corr with LTS.
        assert (net_lock_on '' MN1 n n') by eauto with LTS.
        specialize (H_lock_C n n' ltac:(auto)).
        ltac1:(autounfold with LTS_get in H_lock_C).
        rewrite `(NetMod.get n MN1 = _) in H_lock_C.
        simpl in *.
        bullshit.
      }
      assert (n = self0).
      {
        consider (KIC MN1) by eauto with LTS.
        specialize (H_self_C n).
        ltac1:(autounfold with LTS_get in H_self_C).
        rewrite `(NetMod.get n MN1 = _) in H_self_C.
        auto.
      }

      destruct lock0. 2: bullshit.
      subst.

      attac.
      - hsimpl in |- *.
        apply path_seq0.
        constructor. constructor. attac.
        hrewrite NetMod.get; attac.
      - unfold hot_of, _of, get_Mc, get_M.
        hsimpl in *. rewrite NetMod.get_put_eq in *. (* TODO why this not auto? *)
        attac.
    }
    hsimpl in Hx.

    assert (exists MN3 MQ, (MN2 =(NComm n m R (MValM (hot_of MN2 n)))=> MN3) /\ get_MQ MN3 m = MQ ++ [hot_ev_of MN3 n n])
      as Hxx.
    {
      pose (NetMod.put n (mq MQ1 {|handle:=h; state:=M2|} S2) MN2) as MN2'.
      destruct (NetMod.get m MN2') as [MQm Mm Sm] eqn:?.
      exists (NetMod.put m (mq (MQm ++ [hot_ev_of MN2 n n]) Mm Sm) MN2'), MQm.

      subst MN2'.
      split.
      - econstructor; eattac.
      - unfold get_MQ, hot_ev_of, hot_of, _of, get_Mc, get_M.
        smash_eq n m; attac.
    }
    hsimpl in Hxx.

    exists MN3, (mpath0 ++ mpath1 ++ [(NComm n m R (MValM (hot_of MN2 n)))]).

    eattac.
  Qed.


  Lemma sends_probe_send [MN0 n m p] :
    net_lock_on '' MN0 n m ->
    KIC MN0 ->
    deadlocked m '' MN0 ->
    sends_probe (n, R) p (NetMod.get m MN0) ->
    hot MN0 p (init p) ->
    exists MN1 mpath MQn',
      (MN0 =[mpath]=> MN1)
      /\ (_of alarm MN1 m = true \/ (get_MQ MN1 n = MQn' ++ [EvRecv (m, R) p])).

  Proof. (* TODO adjust hint cost!!! Use Cut!!! *)
    intros Himlazy.
    intros.
    assert (net_sane '' MN0) by eauto with LTS.
    destruct (NetMod.get m MN0) as [MQ [h c] S] eqn:?.
    generalize dependent MN0 MQ n p.

    induction c; intros.
    - consider (sends_probe _ _ _).
      + consider (exists m', net_lock_on '' MN0 m m') by eauto using deadlocked_M_get_lock with LTS.
        consider (exists MN1 mpath MQ,
                     (MN0 =[mpath]=> MN1)
                     /\ get_MQ MN1 n = MQ ++ [hot_ev_of MN1 m m])
          by (eapply propagation_init; eauto;
              ltac1:(autounfold with LTS_get in * ); attac).

        assert (self state0 = m).
        {
          consider (KIC MN0).
          specialize (H_self_C m).
          clear - H_self_C Heqm0.
          ltac1:(autounfold with LTS_get in * ); attac.
        }
        assert (hot MN1 p (init p))
          by (destruct p; simpl in *; subst; eauto 3 using deadlocked_preserve_hot_probe  with LTS).
        assert (p = hot_of MN1 m)
          by (destruct p; simpl in *; subst; auto using hot_of_hot).

        exists MN1, mpath, MQ.
        unfold hot_ev_of in *.
        attac.

      + assert (get_MQ MN0 m = MQ0 ++ EvRecv (n', R) p :: MQ') as Hget0
            by (clear - Heqm0; ltac1:(autounfold with LTS_get in * ); eattac).

        specialize (flush_one_until Hget0) as (MQ1' & M1 & S1 & mpath0 & MN1 & ?).
        hsimpl in *. clear Hget_0.
        assert (MQ_Clear MQ1') by auto. clear H11 H12. (* NoSends, _ -> MQ_clear MQ1' *)

        assert (_of lock_id MN0 m = _of lock_id MN1 m) by eauto using deadlocked_preserve_M_lock_id with LTS.
        assert (_of lock MN0 m = _of lock MN1 m) by eauto using deadlocked_preserve_M_lock with LTS.
        assert (_of self MN1 m = m) by consider (KIC MN1).

        assert (List.In n (_of waitees MN1 m)).
        {
          destruct `(List.In n (waitees state0) \/ _).
          - eapply deadlocked_preserve_M_in_waitees; eauto with LTS.
            ltac1:(autounfold with LTS_get).
            rewrite `(NetMod.get m MN0 = _).
            auto.
          - hsimpl in H8.

            assert (net_lock_on '' MN1 n m) by
              (consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr with LTS;
               eauto 10 with LTS).
            enough (NoRecvQ_from n (get_MQ MN1 m)) by (consider (KIC MN1)).
            enough (NoRecvQ_from n MQ').
            {
              ltac1:(autounfold with LTS_get in * ).
              rewrite `(NetMod.get m MN1 = _).
              intros ? Hx.
              kill Hx.
              apply in_app_or in H17 as [|].
              1: specialize (H16 v0); bullshit.
              clear - H17 H10.
              unfold MQ_Clear in *.
              eapply Forall_forall in H10; eauto. eauto.
            }

            clear - Heqm0 H8 H.
            intros ? ?.
            destruct (NetMod.get m '' MN0) as [I0 P0 O0] eqn:?.
            assert (exists I00 I01, I0 = I00 ++ I01 /\ List.In (n, Q, v) I00 /\ List.In (n, Q, v0) I01).
            {
              unfold net_deinstr, deinstr in *.
              compat_hsimpl in *.
              destruct S.
              hsimpl in *.
              assert (List.In (n, Q, v) (MQ_r MQ0)) by eauto with LTS.
              assert (List.In (n, Q, v0) (MQ_r MQ')) by eauto with LTS.
              exists (l ++ MQ_r MQ0), (MQ_r MQ'). eattac.
            }

            hsimpl in *.

            consider (net_sane '' MN0).
            specialize (H_Sane_SRPC m) as [srpc Hsrpc].
            destruct Hsrpc.
            hsimpl in *.

            consider (exists v' I00', Deq (n, Q) v' I00 I00') by eauto using In_Deq.

            assert (Deq (n, Q) v' (I00 ++ I01) (I00' ++ I01)) by eauto with LTS.

            absurd (List.In (n, Q, v0) (I00' ++ I01)); attac.
        }

        pose (NetMod.put m (mq (MQ' ++ MQ1') {|handle:=h;state:=h (EvRecv (n', R) p) s|} S1) MN1) as MN2.
        assert (exists na, (MN1 =(na)=> MN2)).
        {
          eexists (NTau m (MActM Tau)).
          subst MN2.
          clear - H9. (* get m *)
          constructor; attac. (* TODO why constructor? *)
        }

        (* TODO abstract out *)
        assert (hot MN1 p (init p)).
        {
          split; auto.
          consider (hot MN0 p _).
          destruct p. simpl in *.
          clear - Heqm0 H13 H9 H11 H18. (* get m, of_lock_id, index0 = *)
          smash_eq m init0; hsimpl in *.
          unfold hot in *.
          ltac1:(autounfold with LTS_get in * ).
          destruct (NetMod.get init0 MN0) as [MQi Mi Si] eqn:?.
          specialize (H13 init0 MQi Mi Si ltac:(auto) ltac:(auto)).
          attac.
        }

        destruct s, p. simpl in *.
        assert (lock0 = Some n').
        {
          ltac1:(autounfold with LTS_get in * ).
          rewrite `(NetMod.get m MN0 = _) in *.
          rewrite `(NetMod.get m MN1 = _) in *.
          hsimpl in *.
          auto.
        } subst.

        assert (self0 = m).
        {
          ltac1:(autounfold with LTS_get in * ).
          rewrite `(NetMod.get m MN1 = _) in *.
          now hsimpl in *.
        } subst.

        assert (List.In n (waitees0)).
        {
          ltac1:(autounfold with LTS_get in * ).
          rewrite `(NetMod.get m MN1 = _) in *.
          now hsimpl in *.
        } subst.

        assert (h = Rad_handle).
        {
          consider (KIC MN1).
          specialize (H_Rad_C m).
          ltac1:(autounfold with LTS_get in * ).
          rewrite `(NetMod.get m MN1 = _) in *.
          now hsimpl in *.
        } subst.
        hsimpl in *.

        smash_eq m init0.
        * destruct (PeanoNat.Nat.eq_dec lock_id0 index0).
          -- subst.
             exists MN2, (mpath0 ++ [na]), [].
             unfold get_MQ, _of, get_Mc, get_M.
             subst MN2.
             compat_hsimpl in *.
             ltac1:(replace (index0 =? index0) with true in * by auto using eq_sym, PeanoNat.Nat.eqb_refl).
             compat_hsimpl.
             attac.

          -- exfalso.
             unfold hot, get_MQ, _of, get_Mc, get_M in *.
             hsimpl in *.
             bullshit.

        * enough (exists MN3 mpath1 MQn',
                     (MN2 =[ mpath1 ]=> MN3) /\
                       get_MQ MN3 n = MQn' ++ [EvRecv (m, R) {| init := init0; index := index0 |}]).
          {
            hsimpl in *.

            exists MN3, (mpath0 ++ [na] ++ mpath1), MQn'.
            ltac1:(autounfold with LTS_get in * ).
            destruct (NetMod.get n MN3) as [MQn3 Mn3 Sn3] eqn:?.
            destruct (NetMod.get n MN0) as [MQn0 Mn0 Sn0] eqn:?.
            subst.

            eattac.
          }

          subst MN2.
          unfold get_MQ, _of, get_Mc, get_M.
          simpl in *.

          hsimpl in *.
          ltac1:(replace (NAME.eqb init0 m) with false in * by eauto using eq_sym, NAME_H.neq_neqb_inv).
          hsimpl in |- *.

          clear - H16 H18. (* trans, List.In n waitees0 *)
          remember ((MRecv
                       {|
                         self := m;
                         lock_id := lock_id0;
                         lock := Some n';
                         waitees := waitees0;
                         alarm := alarm0
                       |})) as M.

          change  Que.Channel.Name with Mon.Proc.Que.Channel.Name in *.
          change  Conf.NAME.t' with Mon.Proc.Que.Channel.Name in *.
          rewrite <- HeqM in *. (* JEBAĆ COQ TEGO KUTASA OBSRANEGO *)
          clear HeqM.

          remember {| init := init0; index := index0 |} as p.
          clear Heqp.
          remember (MQ' ++ MQ1') as MQ''. clear HeqMQ'' MQ'. rename MQ'' into MQ'.
          clear - waitees0 H18.
          generalize dependent MN1 MQ'.
          induction waitees0; intros.
          1: bullshit.
          simpl in *.

          assert (exists MQ3 MN2 MQn',
                     (NetMod.put m (mq MQ' {| handle := Rad_handle; state := MSend_all (a :: waitees0) R p M |} S1) MN1
                      =(NComm m a R ^ p)=>
                        (NetMod.put m (mq MQ3 {| handle := Rad_handle; state := MSend_all waitees0 R p M |} S1) MN2)
                     )
                     /\ (get_MQ ((NetMod.put m (mq MQ3 {| handle := Rad_handle; state := MSend_all waitees0 R p M |} S1) MN2)) a) = MQn' ++ [EvRecv (m, R) p]
                 ).
          {
            smash_eq m a.
            - exists (MQ' ++ [EvRecv (m, R) p]), (NetMod.put m (mq MQ' {| handle := Rad_handle; state := MSend_all waitees0 R p M |} S1) MN1), MQ'.
              split.
              eapply NTrans_Comm_eq_inv; eattac. eattac.

            - destruct (NetMod.get a MN1) as [MQa Ma Sa] eqn:?.
              pose (mq MQ' {| handle := Rad_handle; state := MSend_all waitees0 R p M |} S1) as MSm.
              pose (mq (MQa ++ [EvRecv (m, R) p]) Ma Sa) as MSa.

              exists MQ'.
              exists (NetMod.put a MSa MN1).
              exists MQa.
              split.
              eapply NTrans_Comm_neq_inv. eattac.
              exists MSm, MSa.
              rewrite NetMod.put_put_neq; subst MSm MSa; compat_hsimpl; eattac.
              ltac1:(autounfold with LTS_get).
              eattac.
          }
          hsimpl in *.

          smash_eq n a.
          {
            eexists (NetMod.put m
                       (mq MQ3 {| handle := Rad_handle; state := MSend_all waitees0 R p M |} S1) MN2) ,_,MQn'.
            unfold get_MQ in *. eattac.
          }

          destruct `(a = n \/ List.In n waitees0); doubt.

          specialize (IHwaitees0 ltac:(auto) MQ3 ((NetMod.put m (mq MQ3 {| handle := Rad_handle; state := MSend_all waitees0 R p M |} S1) MN2))).
          hsimpl in IHwaitees0.

          exists MN3, (NComm m a R ^ p :: mpath1).
          eattac.

    - destruct to as [to t'].
      assert (exists MN1, MN0 =(NComm m to t' (MValM msg))=> MN1) as [MN1 ?].
      {
        assert (exists MS1, NetMod.get m MN0 =(send (to, t') (MValM msg))=> MS1)
          as [MS ?] by eattac.
        eauto using send_comm_available.
      }
      assert (deadlocked m '' MN1).
      {
        consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr with LTS.
        eauto with LTS.
      }
      assert (exists MQ1, NetMod.get m MN1 = mq (MQ ++ MQ1) {| handle := h; state := c |} &S) as [MQ1 ?].
      {
        kill H4; hsimpl in *.
        smash_eq m to.
        - exists [EvRecv (m, t') msg]. destruct M; attac.
        - exists []. destruct M1; attac.
      }

      consider (sends_probe (n, R) p (mq MQ {| handle := h; state := MSend (to, t') msg c |} &S)).
      + eexists MN1, [NComm m to R ^ msg].
        have (MN0 =( NComm m to R ^ msg )=> MN1).
        kill H4. hsimpl in *.
        unfold get_MQ.
        exists MQ0.
        hsimpl in |- *.
        attac.
      + have (net_sane '' MN1) by eauto with LTS.

        assert (sends_probe (n, R) p (mq (MQ ++ MQ1) {| handle := h; state := c |} &S))
          by auto using sends_probe_extend_r with LTS.

        assert (hot MN1 p (init p)).
        {
          split; auto.
          destruct p.
          smash_eq m init0; hsimpl in *; hsimpl in |- *.
          - assert (_of lock_id MN0 m = _of lock_id MN1 m)
              by eauto using deadlocked_preserve_M_lock_id with LTS.
            rewrite <- `(_of lock_id MN0 m = _).
            unfold hot in *.
            ltac1:(autounfold with LTS_get in * ).
            rewrite `(NetMod.get m MN0 = _) in *.
            hsimpl in *.
            auto.
          - unfold hot in *.
            ltac1:(autounfold with LTS_get in * ).
            smash_eq init0 to.
            + hsimpl in *.
              auto.
            + enough (NetMod.get init0 MN0 = NetMod.get init0 MN1) as Hx by (rewrite <- Hx; attac).
              eapply act_particip_stay; eauto.
              simpl; attac.
        }

        consider (exists (MN2 : MNet) (mpath : list MNAct) MQn',
                     (MN1 =[ mpath ]=> MN2)
                     /\ (_of alarm MN2 m = true
                         \/ get_MQ MN2 n = MQn' ++ [EvRecv (m, R) p])
                 ) by
          re_have (
              consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr1;
              apply IHc with (MQ:=MQ ++ MQ1); eauto 15 with LTS
            ).

        eexists MN2, _, MQn'; eattac.
  Qed.


  Lemma detection_finito [MN0 : MNet] [n m] :
    KIC MN0 ->
    deadlocked n '' MN0 ->
    net_lock_on '' MN0 n m ->
    List.In (hot_ev_of MN0 m n) (get_MQ MN0 n) ->
    exists MN1 mpath,
      (MN0 =[mpath]=> MN1) /\ _of alarm MN1 n = true.

  Proof.
    intros.
    assert (net_sane '' MN0) by eauto with LTS.
    assert (_of lock MN0 n = Some m) by eauto with LTS.

    assert (exists mpath0 MN1 MQ1 h s S1,
               (MN0 =[mpath0]=> MN1)
               /\ NetMod.get n MN1 = mq (hot_ev_of MN0 m n :: MQ1) ({|handle:=h; state:=MRecv s|}) S1
           ).
    {
      specialize (flush_one_In ltac:(eauto)) as ?.
      hsimpl in *.
      exists mpath, MN1, (MQ01 ++ MQ1'), h, s, S1.
      attac.
    }
    hsimpl in *.

    enough (exists na MN2, (MN1 =(na)=> MN2) /\ _of alarm MN2 n = true)
      by (hsimpl in *; exists MN2, (mpath0 ++ [na]); eattac).

    exists (NTau n (MActM Tau)).
    eexists.

    assert (h = Rad_handle).
    {
      consider (KIC MN1).
      specialize (H_Rad_C n).
      ltac1:(autounfold with LTS_get in * ).
      rewrite `(NetMod.get n MN1 = _) in *.
      attac.
    } subst.

    assert (_of lock MN1 n = Some m).
    {
      consider (KIC MN1).
      apply H_lock_C.
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr.
      eauto with LTS.
    }

    assert (hot_ev_of MN1 m n = hot_ev_of MN0 m n).
    {
      unfold hot_ev_of, hot_of in *.
      replace (_of lock_id MN1 n) with (_of lock_id MN0 n); auto.
      eauto using deadlocked_preserve_M_lock_id with LTS.
    }
    rewrite <- `(hot_ev_of MN1 m n = hot_ev_of MN0 m n) in *.

    assert (_of self MN1 n = n) by consider (KIC MN1).

    split.
    - ltac1:(autounfold with LTS_get in * ). hsimpl in |- *.
      constructor. constructor. constructor.
      destruct s.
      rewrite `(NetMod.get n MN1 = _). constructor.
      constructor.
    - unfold hot_of in *.
      ltac1:(autounfold with LTS_get in * ). hsimpl in |- *.
      destruct s.
      rewrite `(NetMod.get n MN1 = _) in *.
      simpl in *.
      subst.
      hsimpl in |- *.
      rewrite (PeanoNat.Nat.eqb_refl).
      attac.
  Qed.


  (** If you receive a hot probe, you either propagate or alarm  *)
  Lemma in_sends_probe [MN0 n' n m p MQ] :
    KIC MN0 ->
    net_lock_on '' MN0 n' n ->
    net_lock_on '' MN0 n m ->
    deadlocked m '' MN0 ->
    hot MN0 p (init p) ->
    get_MQ MN0 n = MQ ++ [EvRecv (m, R) p] ->
    exists MN1 mpath, (MN0 =[mpath]=> MN1)
                      /\ (_of alarm MN1 n = true \/ sends_probe (n', R) p (NetMod.get n MN1)).

  Proof.
    intros.
    assert (net_sane '' MN0) by eauto with LTS.

    destruct p.
    smash_eq n init0.
    2: exists MN0, []; attac; eauto using sends_probe_prop_foreign.

    simpl in *.
    consider (exists MN1 mpath0, (MN0 =[mpath0]=> MN1) /\ _of alarm MN1 n = true).
    {
      eapply detection_finito; eauto 15 with LTS.
      unfold hot_ev_of.
      replace (hot_of MN0 n) with {| init := n; index := index0 |} by eauto using hot_of_hot.
      rewrite `(get_MQ _ _ = _). attac.
    }

    exists MN1, mpath0.
    eattac.
  Qed.


  Lemma deadlocked_lock_chain_invariant1 [N0 N1 : PNet] [L] [n0 n1 : Name] [a] :
    (N0 =(a)=> N1) ->
    deadlocked n0 N0 ->
    lock_chain N0 n0 L n1 ->
    lock_chain N1 n0 L n1.

  Proof.
    intros.
    have (deadlocked n0 N1).
    enough (lock_chain N1 n0 L n1) by attac.
    hsimpl in *.
    generalize dependent N0 N1 n0 n1 L.
    induction L; intros; hsimpl in *; eauto with LTS.

    constructor; eauto with LTS.

    have (deadlocked a0 N1).

    normalize_hyp @IHL.
    specialize (IHL n1 a0 N1 N0).
    apply IHL; eauto with LTS.
  Qed.

  (* Hint Resolve  deadlocked_lock_chain_invariant1 | 0 : LTS. *)


  Lemma deadlocked_lock_chain_invariant [N0 N1 : PNet] [L] [n0 n1 : Name] [mpath] :
    (N0 =[mpath]=> N1) ->
    deadlocked n0 N0 ->
    lock_chain N0 n0 L n1 ->
    lock_chain N1 n0 L n1.

  Proof.
    generalize dependent N0.
    induction mpath; intros; hsimpl in *. 1: attac.
    assert (dep_on N2 n0 n1) by attac.
    eapply (IHmpath N2); eauto using deadlocked_lock_chain_invariant1 with LTS.
  Qed.

  #[export] Hint Resolve deadlocked_lock_chain_invariant | 0 : LTS.


  Lemma propagation1 [MN0 n' n m p] :
    KIC MN0 ->
    net_lock_on '' MN0 n' n ->
    net_lock_on '' MN0 n m ->
    deadlocked m '' MN0 ->
    sends_probe (n, R) p (NetMod.get m MN0) ->
    hot MN0 p (init p) ->
    deadlocked (init p) '' MN0 ->
    exists MN1 mpath,
      (MN0 =[mpath]=> MN1)
      /\ (_of alarm MN1 n = true \/ _of alarm MN1 m = true \/ sends_probe (n', R) p (NetMod.get n MN1)).
  Proof.
    intros.
    assert (net_sane '' MN0) by eauto with LTS.

    consider (exists MN1 mpath0 MQn',
                 (MN0 =[mpath0]=> MN1)
                 /\ (_of alarm MN1 m = true \/ (get_MQ MN1 n = MQn' ++ [EvRecv (m, R) p])))
      by eauto using sends_probe_send.

    destruct `(_of alarm MN1 m = true \/ get_MQ MN1 n = MQn' ++ [EvRecv (m, R) p]) as [|].
    1: eattac.

    consider ( exists MN2 mpath1, (MN1 =[mpath1]=> MN2)
                                  /\ (_of alarm MN2 n = true \/ sends_probe (n', R) p (NetMod.get n MN2))).
    {
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr.
      assert (deadlocked n '' MN0) by (eauto using deadlocked_dep' with LTS).
      assert (deadlocked n' '' MN0) by eauto using deadlocked_dep' with LTS.
      assert (net_lock_on '' MN1 n m) by eauto 3 with LTS.
      eapply in_sends_probe; eauto 5 using deadlocked_preserve_hot_probe with LTS.
    }

    destruct `( _of alarm MN2 n = true \/ sends_probe (n', R) p (NetMod.get n MN2)) as [|].
    all: exists MN2, (mpath0 ++ mpath1); eattac.
  Qed.


  Lemma propagation [MN0 : MNet] [n m m' p] :
    KIC MN0 ->
    dep_on '' MN0 n m ->
    net_lock_on '' MN0 m m' ->
    deadlocked m' '' MN0 ->
    sends_probe (m, R) p (NetMod.get m' MN0) ->
    hot MN0 p n ->
    deadlocked (init p) '' MN0 ->
    exists MN1 mpath n',
      (MN0 =[mpath]=> MN1)
      /\ ((_of alarm MN1 n' = true) \/ (net_lock_on '' MN1 n n' /\ sends_probe (n, R) p (NetMod.get n' MN1))).

  Proof.
    intros.

    assert (net_sane '' MN0) by eauto with LTS.
    apply dep_lock_chain in H0.
    hsimpl in *.
    clear H7. (* ~List.In m L *)

    generalize dependent n m m' MN0.
    ltac1:(rev_induction L); intros; hsimpl in *.
    {
      assert (n = init p) by consider (hot MN0 p n).
      specialize (@propagation1 MN0 n m m' p) as HP.
      specialize (HP ltac:(auto)).
      specialize (HP ltac:(auto)).
      specialize (HP ltac:(auto)).
      specialize (HP ltac:(auto)).
      specialize (HP ltac:(auto)).
      specialize (HP ltac:(subst;auto)).
      specialize (HP ltac:(subst;auto)).
      hsimpl in HP.
      destruct `(_of alarm MN1 m = true \/
                   _of alarm MN1 m' = true \/ sends_probe (n, R) p (NetMod.get m MN1)
        ) as [|[|]].
      1,2: eattac.
      assert (net_lock_on '' MN1 n m).
      {
        consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr with LTS.
        assert (deadlocked m '' MN0) by eauto using deadlocked_dep' with LTS.
        assert (deadlocked n '' MN0) by eauto using deadlocked_dep' with LTS.
        eauto 13 with LTS.
      }
      exists MN1, mpath, m; eattac.
    }

    assert (n = init p) by consider (hot MN0 p n).

    consider (exists MN1 mpath0,
                 (MN0 =[mpath0]=> MN1)
                 /\ (_of alarm MN1 m = true \/ _of alarm MN1 m' = true \/ sends_probe (a, R) p (NetMod.get m MN1))
             ) by (subst; auto 2 using propagation1).
    destruct `(_of alarm MN1 m = true \/ _of alarm MN1 m' = true \/ sends_probe (a, R) p (NetMod.get m MN1))
      as [|[|]].
    1,2: exists MN1, mpath0; eattac.

    assert (deadlocked m '' MN0) by eauto with LTS.

    assert (net_sane '' MN1).
    {
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr with LTS.
      eauto with LTS.
    }
    assert (KIC MN1) by eauto with LTS.
    assert (hot MN1 p (init p)).
    {
      unfold hot in *.
      rewrite <- `(n = init p) in *.
      assert (_of lock_id MN0 n = _of lock_id MN1 n) by
        eauto using deadlocked_preserve_M_lock_id with LTS.
      rewrite <- `(_of lock_id MN0 n = _of lock_id MN1 n).
      auto.
    }
    assert (deadlocked m '' MN1).
    {
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr with LTS.
      eauto 2 with LTS.
    }
    assert (net_lock_on '' MN1 a m).
    {
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr with LTS.
      assert (deadlocked m' '' MN0) by eauto using deadlocked_dep' with LTS.
      assert (deadlocked m '' MN0) by eauto using deadlocked_dep' with LTS.
      assert (deadlocked a '' MN0) by eauto using deadlocked_dep' with LTS.
      eauto using deadlocked_lock_on' with LTS.
    }
    assert (lock_chain '' MN1 n l a).
    {
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr with LTS.
      assert (deadlocked m' '' MN0) by eauto using deadlocked_dep' with LTS.
      assert (deadlocked m '' MN0) by eauto using deadlocked_dep' with LTS.
      assert (deadlocked a '' MN0) by eauto using deadlocked_dep' with LTS.
      eapply deadlocked_lock_chain_invariant. eauto with LTS.
      eapply deadlocked_dep'; eauto with LTS.
      eauto.
    }

    assert (deadlocked (init p) '' MN1).
    {
      subst.
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr with LTS.
      assert (deadlocked m' '' MN0) by eauto using deadlocked_dep' with LTS.
      assert (deadlocked m '' MN0) by eauto using deadlocked_dep' with LTS.
      assert (deadlocked a '' MN0) by eauto using deadlocked_dep' with LTS.
      eapply deadlocked_dep'; eauto with LTS.
    }

    assert (hot MN1 p n).
    {
      subst.
      consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr with LTS.
    }

    normalize_hyp @H.
    specialize (H MN1 m a n).
    specialize (H ltac:(auto)).
    specialize (H ltac:(eauto)).
    specialize (H ltac:(auto)).
    specialize (H ltac:(auto)).
    specialize (H ltac:(auto)).
    specialize (H ltac:(subst; auto)).
    specialize (H ltac:(subst; auto)).
    specialize (H ltac:(eauto 13 using deadlocked_preserve_hot_probe with LTS)).
    hsimpl in H.

    exists MN2, (mpath0 ++ mpath), n'; eattac.
  Qed.


  Lemma propagation_finito [MN0 : MNet] [n m m' p] :
    KIC MN0 ->
    dep_on '' MN0 n m ->
    net_lock_on '' MN0 m m' ->
    deadlocked m' '' MN0 ->
    hot MN0 p n ->
    sends_probe (m, R) p (NetMod.get m' MN0)  ->
    exists MN1 mpath,
      (MN0 =[mpath]=> MN1) /\ (exists n', _of alarm MN1 n' = true).
  (* TODO does propagation_init need net_lock_on assumption? *)
  Proof.
    intros.
    assert (net_sane '' MN0) by eauto with LTS.

    consider (exists MN1 mpath0 n',
                 (MN0 =[mpath0]=> MN1)
                 /\ ((_of alarm MN1 n' = true) \/ (net_lock_on '' MN1 n n' /\ sends_probe (n, R) p (NetMod.get n' MN1)))).
    {
      consider (hot MN0 p n).
      eapply propagation; eauto 3 with LTS.
      attac.
      assert (deadlocked m '' MN0) by eauto with LTS.
      eapply deadlocked_dep'; eauto with LTS.
    }

    destruct `(_of alarm MN1 n' = true \/ net_lock_on '' MN1 n n' /\ sends_probe (n, R) p (NetMod.get n' MN1)) as [|[? ?]].
    1: eattac.

    consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr.

    have (net_sane '' MN1) by eauto with LTS.
    have (KIC MN1) by auto with LTS.
    have (deadlocked m' '' MN1) by eauto with LTS.
    have (deadlocked m' '' MN0) by eauto with LTS.
    have (deadlocked m '' MN0) by eauto with LTS.
    have (deadlocked n '' MN0) by (eapply deadlocked_dep'; eauto with LTS).
    assert (hot MN1 p (init p)).
    {
      consider (hot MN0 p n).
      constructor; auto.
      replace (_of lock_id MN0 (init p)) with  (_of lock_id MN1 (init p))
        by re_have eauto using eq_sym, deadlocked_preserve_M_lock_id with LTS.
      ltac1:(autounfold with LTS_get in * ); auto.
    }

    consider (exists MN2 mpath1 MQn',
                 (MN1 =[mpath1]=> MN2)
                 /\ (_of alarm MN2 n' = true \/ (get_MQ MN2 n = MQn' ++ [EvRecv (n', R) p]))).
    {
      eapply sends_probe_send; re_have eauto with LTS.
    }

    destruct `(_of alarm MN2 n' = true \/ get_MQ MN2 n = MQn' ++ [EvRecv (n', R) p]).
    1: exists MN2, (mpath0 ++ mpath1); eattac.

    consider (exists ppath, '' MN1 =[ppath]=> '' MN2) by eauto using Net_path_corr.

    have (net_sane '' MN2) by eauto with LTS.
    have (KIC MN2) by auto with LTS.
    assert (deadlocked n '' MN2).
    {
      assert ('' MN0 =[ppath ++ ppath0]=> '' MN2) by eauto with LTS.
      re_have eauto 4 with LTS.
    }
    assert (hot MN2 p (init p)).
    {
      consider (n = init p) by (consider (hot MN0 p n)).
      consider (hot MN1 p (init p)).
      have (deadlocked (init p) '' MN1).
      constructor; auto.
      replace (_of lock_id MN2 (init p)) with  (_of lock_id MN1 (init p))
        by re_have eauto using eq_sym, deadlocked_preserve_M_lock_id with LTS.
      ltac1:(autounfold with LTS_get in * ); auto.
    }
    assert  (List.In (hot_ev_of MN2 n' n) (get_MQ MN2 n)).
    {
      unfold hot_ev_of.
      assert (p = hot_of MN2 n).
      {
        consider (hot MN2 p (init p)).
        consider (hot MN0 p n).
        destruct p; simpl in *.
        unfold hot_of.
        ltac1:(autounfold with LTS_get in * ).
        f_equal.
        auto.
      }  (* todo shit *)
      rewrite <- `(p = _).
      rewrite `(get_MQ _ _ = _).
      auto with datatypes.
    }
    have (List.In (hot_ev_of MN2 n' n) (get_MQ MN2 n)) by (unfold hot_ev_of; eauto with LTS).

    consider (exists MN3 mpath2, (MN2 =[mpath2]=> MN3) /\ _of alarm MN3 n = true)
      by re_have (eauto using detection_finito with LTS).

    exists MN3, (mpath0 ++ mpath1 ++ mpath2).
    eattac.
  Qed.


  (* TODO better name xd *)
  Lemma mq_Q_lock_sound [MN m n v] :
    net_sane '' MN ->
    List.In (TrRecv (m, Q) v) (get_MQ MN n) ->
    net_lock_on '' MN m n.
  Proof.
    intros.
    consider (net_sane '' MN).
    enough (pq_client m (NetMod.get n '' MN)); attac.
    unfold net_deinstr, get_MQ in *.
    destruct (NetMod.get n MN) as [MQ M S] eqn:?.
    hsimpl in |- *.
    destruct ((deinstr (NetMod.get n MN))) eqn:?.
    econstructor 1; attac.
    eapply deinstr_In_recv. eauto.
    rewrite Heqm0 in *.
    eauto.
  Qed.


  Lemma propagation_init' [MN0 : MNet] [n n' m] [v ] :
    KIC MN0 ->
    deadlocked n '' MN0 ->
    net_lock_on '' MN0 n n' ->
    List.In (TrRecv (m, Q) v) (get_MQ MN0 n) ->
    exists MN1 mpath,
      (MN0 =[mpath]=> MN1)
      /\ sends_probe (m, R) (hot_of MN1 n) (NetMod.get n MN1).

  Proof.
    intros.
    assert (net_sane '' MN0) by eauto with LTS.

    assert (exists mpath0 MN1 MQ1 h s S1,
               (MN0 =[mpath0]=> MN1)
               /\ NetMod.get n MN1 = mq (TrRecv (m, Q) v :: MQ1) ({|handle:=h; state:=MRecv s|}) S1
           ) as Hxx'.
    {
      specialize (flush_one_In ltac:(eauto)) as ?.
      hsimpl in *.
      exists mpath, MN1, (MQ01 ++ MQ1'), h, s, S1.
      attac.
    }
    hsimpl in Hxx'.

    assert (exists mpath1 MN2 M2 S2,
               (MN1 =[mpath1]=> MN2)
               /\ NetMod.get n MN2 = mq MQ1 {|handle:=h; state:=MSend (m, R) (hot_of MN2 n) M2|} S2
           ) as Hx.
    {
      assert (h = Rad_handle).
      {
        consider (KIC MN1) by eauto with LTS.
        specialize (H_Rad_C n).
        ltac1:(autounfold with LTS_get in H_Rad_C).
        rewrite `(NetMod.get n MN1 = _) in H_Rad_C.
        auto.
      }

      destruct S1 as [I1 P1 O1].
      pose (pq (I1 ++ [(m, Q, v)]) P1 O1) as S2.
      pose  {|self := self s
            ; lock_id := lock_id s
            ; lock := lock s
            ; waitees := m :: waitees s
            ; alarm := alarm s
            |} as s1.
      pose (NetMod.put n (mq MQ1 {| handle := h; state := h (TrRecv (m, Q) v) s |} S2) MN1) as MN1'.

      exists [NTau n (MActP (Recv (m, Q) v))], MN1', (MRecv s1), S2.

      destruct s.
      subst MN1' s1 S2.

      assert (lock0 <> None).
      {
        consider (KIC MN1) by eauto with LTS.
        consider (exists path, '' MN0 =[path]=> '' MN1) by eauto using Net_path_corr with LTS.
        assert (net_lock_on '' MN1 n n') by eauto with LTS.
        specialize (H_lock_C n n' ltac:(auto)).
        ltac1:(autounfold with LTS_get in H_lock_C).
        rewrite `(NetMod.get n MN1 = _) in H_lock_C.
        simpl in *.
        bullshit.
      }
      assert (n = self0).
      {
        consider (KIC MN1) by eauto with LTS.
        specialize (H_self_C n).
        ltac1:(autounfold with LTS_get in H_self_C).
        rewrite `(NetMod.get n MN1 = _) in H_self_C.
        auto.
      }

      destruct lock0. 2: bullshit.
      subst.

      attac.
      - hsimpl in |- *.
        eapply path_seq0.
        constructor. constructor.
        constructor. hrewrite NetMod.get.
        attac.
      - unfold hot_of, _of, get_Mc, get_M.
        hsimpl in *. rewrite NetMod.get_put_eq in *.
        attac.
    }
    hsimpl in Hx.

    exists MN2, (mpath0 ++ mpath1).
    split. eattac.

    rewrite `(NetMod.get n MN2 = _).
    constructor.
  Qed.


  Lemma propagation_init_finito [MN0 : MNet] [n m] [v] :
    KIC MN0 ->
    dep_on '' MN0 n m ->
    deadlocked m '' MN0 ->
    List.In (TrRecv (m, Q) v) (get_MQ MN0 n) ->
    exists MN1 mpath,
      (MN0 =[mpath]=> MN1) /\ (exists n', _of alarm MN1 n' = true).

  Proof.
    intros.
    assert (net_sane '' MN0) by eauto with LTS.

    assert (net_lock_on '' MN0 m n) by eauto using mq_Q_lock_sound.
    assert (dep_on '' MN0 n n) by eauto with LTS.
    assert (deadlocked n '' MN0) by eauto 2 with LTS.

    consider (exists MN1 mpath0,
                 (MN0 =[mpath0]=> MN1)
                 /\ sends_probe (m, R) (hot_of MN1 n) (NetMod.get n MN1))
      by (consider (dep_on '' MN0 n n) by eauto using propagation_init'; eauto using propagation_init').

    consider (exists ppath, '' MN0 =[ppath]=> '' MN1) by eauto using Net_path_corr.
    have (net_sane '' MN1) by eauto with LTS.
    have (KIC MN1) by auto with LTS.

    assert (deadlocked n '' MN1) by auto with LTS.
    assert (deadlocked m '' MN1) by eauto 2 with LTS. (* TODO why lag if not 2 gas? *)
    assert (net_lock_on '' MN1 m n) by eauto with LTS.
    assert (dep_on '' MN1 n n) by eauto with LTS.
    assert (dep_on '' MN1 n m) by eauto with LTS.

    consider (exists MN2 mpath1,
                 (MN1 =[mpath1]=> MN2) /\ (exists n', _of alarm MN2 n' = true))
      by eauto using propagation_finito, hot_hot_of with LTS.

    exists MN2, (mpath0 ++ mpath1).
    eattac.
  Qed.


  Theorem ac_to_alarm [MN0 : MNet] [n] :
    KIC MN0 ->
    ac n MN0 ->
    dep_on '' MN0 n n ->
    exists MN1 mpath, (MN0 =[mpath]=> MN1) /\ (exists n', _of alarm MN1 n' = true).

  Proof.
    intros.

    destruct (_of alarm MN0 n) eqn:?.
    1: exists MN0, []; eattac.

    assert (deadlocked n '' MN0) by eauto using dep_self_deadlocked with LTS.

    consider (ac n MN0).
    - consider (n = m \/ dep_on '' MN0 n m);
        eauto using propagation_finito, hot_hot_of with LTS.

    - consider (exists MN1 mpath0, (MN0 =[mpath0]=> MN1) /\ _of alarm MN1 n = true)
        by eauto using detection_finito.
      exists MN1, mpath0.
      eattac.
  Qed.


  Lemma KIC_AnySRPC_pq_instr [I N] : KIC (net_instr I N) ->
                                     forall n, AnySRPC_pq (NetMod.get n N).
  Proof.
    intros ?.
    consider (KIC _); attac.
  Qed.

  #[export] Hint Immediate KIC_AnySRPC_pq_instr : LTS.


  Theorem detection_completeness [N0] [I0] :
    KIC (net_instr I0 N0) ->
    Deadlocked N0 ->
    exists mpath MN1, (net_instr I0 N0 =[mpath]=> MN1) /\ exists n, _of alarm MN1 n = true.

  Proof.
    intros.
    assert (net_sane N0) by (kill H; hsimpl in *; auto). (* TODO to lemma... *)

    assert (exists n, dep_on N0 n n) as [n ?].
    {
      consider (Deadlocked N0).
      enough (exists n : Name, In n DL /\ dep_on N0 n n) by attac.
      eapply deadset_dep_self; eauto with LTS.
      intros ? ?.
      eauto using net_sane_lock_dec.
    }

    consider (exists n', dep_on '' (net_instr I0 N0) n n' /\ ac n' (net_instr I0 N0)).
    {
      consider (KIC _).
      assert (dep_on '' (net_instr I0 N0) n n) by (rewrite net_deinstr_instr; auto).
      eapply H_alarm_C; eauto.
    }

    assert (dep_on N0 n' n') by eauto using dep_reloop with LTS.

    assert (dep_on '' (net_instr I0 N0) n' n') by attac. (* TODO lemma... *)

    consider (exists MN1 mpath,
                 (net_instr I0 N0 =[ mpath ]=> MN1) /\ (exists n' : Name, _of alarm MN1 n' = true)) by eauto using ac_to_alarm.

    eattac.
  Qed.


  Corollary detection_completeness_uni [N0 N1] [ppath] [I0] :
    KIC (net_instr I0 N0) ->
    (N0 =[ ppath ]=> N1) ->
    Deadlocked N1 ->
    forall mpath0 I1,
      (net_instr I0 N0 =[ mpath0 ]=> net_instr I1 N1) ->
      exists mpath1 MN2,
        (net_instr I1 N1 =[ mpath1 ]=> MN2)
        /\ exists n, _of alarm MN2 n = true.

  Proof.
    intros; eauto using detection_completeness with LTS.
  Qed.


  Corollary detection_completeness_exi [N0 N1] [ppath] [I0] :
    KIC (net_instr I0 N0) ->
    (N0 =[ ppath ]=> N1) ->
    Deadlocked N1 ->
    exists mpath0 I1 mpath1 MN2,
      (net_instr I0 N0 =[ mpath0 ]=> net_instr I1 N1)
      /\ (net_instr I1 N1 =[ mpath1 ]=> MN2)
      /\ exists n, _of alarm MN2 n = true.
  Proof.
    intros.

    consider (exists mpath0 I1, net_instr I0 N0 =[ mpath0 ]=> net_instr I1 N1)
      by eauto using Net_Transp_completeness.

    exists mpath0, I1.

    consider (exists mpath1 MN2, (net_instr I1 N1 =[ mpath1 ]=> MN2)
                            /\ exists n, _of alarm MN2 n = true)
      by eauto using detection_completeness with LTS.

    eattac.
  Qed.


  Conjecture detection_completeness_path' : forall [N0 N1] [ppath] [I0],
      net_sane '' N0 ->
      KIC (net_instr I0 N0) ->
      (N0 =[ ppath ]=> N1) ->
      Deadlocked '' N1 ->
      exists I1 mpath0,
        (net_instr I0 N0 =[ mpath0 ]=> net_instr I1 N1)
        /\ exists n, _of alarm (net_instr I1 N1) n = true.
End COMPL_F.

Module Type COMPL(Conf : DETECT_CONF) := Conf <+ DETECT_PARAMS(Conf) <+ COMPL_F.
