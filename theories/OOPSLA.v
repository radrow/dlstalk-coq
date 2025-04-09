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

From Coq Require Import Lists.List.
From Coq Require Import Structures.Equalities.
Import ListNotations.

Import GenServerNet.
Import Sound.
Import SrpcDefs.

(* begin hide *)
(* Things in here would be put in separate files; we paste them here to simplify
the patch. Please skip to the "Introduction" section. *)

Module PaperCompat.
  Definition serv_lock (n : Name) (S : Serv) :=
    (forall v E, ~ Deq (n, R) v (serv_i S) E) /\ (exists c, SRPC (Locked c n) (serv_p S)) /\ (serv_o S = []).

  Definition dead_set (DS : list Name) N :=
    DS <> []  /\  (forall n0, In n0 DS -> exists n1, lock N n0 n1 /\ In n1 DS).

  Inductive SRPCI : SRPC_State -> Proc -> Prop :=
  | SRPCI_R h :
    (forall c t, h (c, t) <> None -> t = Q) ->
    (forall c v, exists cont, h (c, Q) = Some cont /\ SRPCI (Working c) (cont v)) ->
    SRPCI Ready (PRecv h)
  | SRPCI_WR c v P : SRPCI (Working c) (PSend (c, R) v P)
  | SRPCI_WT c P : SRPCI (Working c) P -> SRPCI (Working c) (STau P)
  | SRPCI_WQ c s v P : SRPCI (Locked c s) P -> SRPCI (Working c) (PSend (s, Q) v P)
  | SRPCI_L c s h cont :
    (forall nc, h nc <> None -> nc = (s, R)) ->
    (h (s, R) = Some cont) ->
    (forall v, SRPCI (Working c) (cont v)) ->
    SRPCI (Locked c s) (PRecv h)
  .

  CoInductive SRPCC : SRPC_State -> Proc -> Prop :=
  | SRPCC_R P0 : (forall c v P1, P0 =(Recv (c, Q) v)=> P1 -> SRPCC (Working c) P1) -> SRPCI Ready P0 -> SRPCC Ready P0
  | SRPCC_W c P0 :
    (forall v P1, P0 =(Send (c, R) v)=> P1 -> SRPCC Ready P1) ->
    (forall P1, P0 =(Tau)=> P1 -> SRPCC (Working c) P1) ->
    (forall s v P1, P0 =(Send (s, Q) v)=> P1 -> SRPCC (Locked c s) P1) ->
    SRPCI (Working c) P0 -> SRPCC (Working c) P0
  | SRPCC_L c s P0 : (forall v P1, P0 =(Recv (s, R) v)=> P1 -> SRPCC (Working c) P1) -> SRPCI (Locked c s) P0 -> SRPCC (Locked c s) P0
  .

  Definition client (n : Name) (S : Serv) :=
    (exists v, In (n, Q, v) (serv_i S)  \/ In (n, R, v) (serv_o S))
    \/ SRPCC (Working n) (serv_p S)  \/  (exists s, SRPCC (Locked n s) (serv_p S)).


  Definition ac (n : Name) (MN : MNet) :=
    exists n1 n2,
      trans_lock MN n n1
      /\ lock MN n1 n2
      /\ (forall n', (n' = n2 \/ trans_lock MN n' n2) -> locked (MN n') <> None)
      /\ ( alarm (MN n) = true
          \/ (exists n', locked (MN n) = Some n'
                   /\ In (active_ev_of MN n' n) (mserv_q (MN n)))
          \/ (sends_to MN n2 n1 (active_probe_of MN n))
          \/ (exists n', lock MN n2 n'
                   /\ In (active_ev_of MN n' n) (mserv_q (MN n2))
                   /\ In n1 (wait (MN n2)))
          \/ (exists n' v MQ0 MQ1,
                lock MN n2 n'
                /\ mserv_q (MN n2) = MQ0 ++ (active_ev_of MN n' n) :: MQ1
                /\ In (MqRecv (n1, Q) v) MQ0)
          \/ (exists v, In (MqRecv (n1, Q) v) (mserv_q (MN n)))
        ).
End PaperCompat.


Fact serv_lock_eq : forall S n, AnySRPC_serv S -> serv_lock [n] S <-> PaperCompat.serv_lock n S.
Proof.
  split; intros.
  - consider (serv_lock _ _).
    repeat split; repeat (intros ?); simpl in *.
    + bs (In (n, R, v) &I).
    + eauto using lock_SRPC_Locked with LTS.
  - destruct S.
    consider (PaperCompat.serv_lock _ _).
    hsimpl in *.
    repeat split; repeat (intros ?); simpl in *; eauto with LTS.
    assert (exists v' E, Deq (n0, R) v' serv_i0 E) by eauto using In_Deq.
    hsimpl in *.
    bs.
Qed.


Fact dead_set_eq : forall N DS, SRPC_net N -> dead_set DS N <-> PaperCompat.dead_set DS N.

Proof.
  unfold PaperCompat.dead_set.
  split; intros; repeat constructor; intros.
  - attac.
  - consider (dead_set _ _).
    consider (exists L, lock_set N L n0 /\ incl L DS).
    unfold lock_set, lock in *.
    consider (exists n1, serv_lock [n1] (NetMod.get n0 N)) by eauto with LTS.
    exists n1.
    eattac.
  - attac.
  - hsimpl in *.
    consider (exists n1, lock N n n1 /\ _) by eauto.
    exists [n1].
    unfold incl, lock in *.
    attac.
Qed.


Inductive SRPC_measure : Proc -> Prop :=
| ms_reply n v P : SRPC_measure (PSend (n, R) v P)
| ms_tau P : SRPC_measure P -> SRPC_measure (STau P)
| ms_query n v P : SRPC_measure P -> SRPC_measure (PSend (n, Q) v P)
| ms_recv h : (forall v nc cont, h nc = Some cont -> SRPC_measure (cont v)) -> SRPC_measure (PRecv h)
.

Lemma SRPCI_measure : forall srpc P, srpc <> Ready -> PaperCompat.SRPCI srpc P -> SRPC_measure P.
Proof.
  intros.
  induction H0; intros; constructor; eattac.
  specialize (H0 nc ltac:(attac)); attac.
  rewrite H4 in H1.
  attac.
Qed.

Lemma SRPCC_SRPCI : forall srpc P, PaperCompat.SRPCC srpc P -> PaperCompat.SRPCI srpc P.
  intros. kill H.
Qed.

Lemma SRPCC_measure : forall srpc P, srpc <> Ready -> PaperCompat.SRPCC srpc P -> SRPC_measure P.
  intros.
  eauto using SRPCC_SRPCI, SRPCI_measure.
Qed.

Lemma SRPCB_measure : forall c (srpc : SRPC_Busy_State c) P, SRPC_Busy srpc P -> SRPC_measure P.
  intros.
  induction H; intros.
  - destruct P0; eattac.
    + destruct n as [n [|]].
      * constructor; attac.
      * constructor; attac.
    + constructor.
      attac.
  - specialize (HReplyAll some_val) as [? ?]; attac.
    constructor.
    attac.
Qed.


Fact SRPCB_eq : forall P c (srpc : SRPC_Busy_State c), SRPC_Busy srpc P <-> PaperCompat.SRPCI (Busy srpc) P.

Proof.
  split; intros.
  - induction H.
    + destruct P0.
      * bs.
      * destruct n as [n [|]].
        -- constructor.
           eauto with LTS.
        -- consider (c = n) by eauto with LTS.
           constructor.
      * bs.
      * constructor.
        eauto with LTS.
    + destruct P0.
      * specialize (HReplyAll some_val) as [? ?]; bs.
      * specialize (HReplyAll some_val) as [? ?]; bs.
      * specialize (HReplyAll some_val) as [? ?]; attac.
        econstructor; eattac.
        destruct nc.
        destruct (handle (n, t)) eqn:?; doubt.
        specialize (HReplyOnly (Recv (n, t) some_val) (p some_val)) as [? ?]; eattac.
      * specialize (HReplyAll some_val) as [? ?]; bs.
  - assert (SRPC_measure P) by (apply SRPCI_measure with (srpc:=Busy srpc); attac).
    generalize dependent srpc.
    induction H0; intros; consider (PaperCompat.SRPCI _ _); attac.
    + constructor; attac.
    + constructor; attac.
    + constructor; attac.
    + constructor; eattac.
      * consider (n = (s, R)); attac.
      * kill H1.
        consider (n = (s, R)); attac.
Qed.

Fact SRPC_eq : forall P srpc, SRPC srpc P <-> PaperCompat.SRPCC srpc P.

Proof.
  split; intros.
  - generalize dependent srpc P.
    ltac1:(cofix C).
    intros P srpc Hsrpc.
    destruct P > [| destruct n as [n [|]] | | ]; kill Hsrpc > [|kill HBusy].
    all: try (solve [clear C; specialize (HQueryAll some_name some_val); kill HQueryAll; bs]).
    all: try (solve [clear C; specialize (HReplyAll some_val); kill HReplyAll; bs]).
    + apply PaperCompat.SRPCC_W; intros; eauto.
      econstructor.
      eapply SRPCB_eq.
      eapply HQuery0.
      attac.
    + eapply PaperCompat.SRPCC_W; intros; eauto.
      eapply SRPCB_eq.
      econstructor; attac.
    + eapply PaperCompat.SRPCC_R; intros.
      1: { specialize HQueryOnly with (a:=Recv (c, Q) v)(P1 := P1) as [? [? ?]]; eattac. }
      econstructor; intros.
      * destruct (handle (c, t)) eqn:?; doubt.
        specialize HQueryOnly with (a:=Recv (c, t) some_val)(P1 := p some_val) as [? [? ?]]; eattac.
      * specialize (HQueryAll c v) as [? ?].
        eattac.
        exists cont.
        eattac.
        specialize HQueryOnly with (a:=Recv (c, Q) v0)(P1 := cont v0) as [? [? ?]]; eattac.
        eapply SRPCB_eq.
        kill H1; attac.
    + constructor; intros; eauto.
      eapply SRPCB_eq.
      econstructor; intros; eauto.
    + eapply PaperCompat.SRPCC_W; intros; eauto.
      eapply SRPCB_eq.
      econstructor; intros; eauto.
  - generalize dependent srpc P.
    ltac1:(cofix C).
    intros P srpc Hsrpc.
    kill Hsrpc; constructor; intros; doubt.
    + kill H0.
      specialize (H2 c v); eattac.
    + kill H0.
      attac.
      destruct n.
      specialize H3 with (c:=n)(v:=v); attac.
      specialize (H2 n t ltac:(attac)); attac.
      assert (cont0 = cont). cbv in *. rewrite H3 in H4; attac.
      subst.
      assert (PaperCompat.SRPCC (Working n) (cont v)). apply H with (v:=v). exists (n, Q), v, cont. attac.
      exists n, v.
      eattac.
    + apply SRPCB_eq.
      eauto.
    + eauto.
    + eauto.
    + eauto.
    + eapply SRPCB_eq.
      eauto.
    + apply C.
      kill H0.
      consider ((s0, R) = (s, R)). apply H2; attac.
      apply H in H1.
      auto.
Qed.


Fact client_eq : forall n S, serv_client n S <-> PaperCompat.client n S.
Proof.
  unfold PaperCompat.client.
  split; intros.
  - consider (serv_client _ _); unfold proc_client in *; attac.
    rewrite SRPC_eq in *.
    destruct srpcb; eattac.
  - destruct S.
    destruct `(_ \/ _); hsimpl in *.
    + destruct `(_ \/ _); eattac.
    + destruct `(_ \/ _); eattac; rewrite <- SRPC_eq in *; eattac.
Qed.


Lemma KIC_lock_locked : forall n n' MN, KIC MN -> trans_lock MN n n' -> locked (MN n) <> None.
Proof. intros. consider (trans_lock _ _ _); attac. Qed.
Hint Resolve KIC_lock_locked : LTS.

Lemma KIC_lock_locked_loop : forall n n' MN, KIC MN -> trans_lock MN n n -> trans_lock MN n n' -> locked (MN n') <> None.
Proof. intros. assert (trans_lock MN n' n). eapply dep_loop; eauto with LTS. eapply SRPC_lock_set_uniq; eauto with LTS. eauto with LTS. Qed.
Hint Resolve KIC_lock_locked_loop : LTS.

Lemma alarm_condition_eq : forall n MN,
    KIC MN -> trans_lock '' MN n n ->
    alarm_condition n MN <-> PaperCompat.ac n MN.
Proof.
  split; intros.
  - consider (alarm_condition _ _).
    + consider (exists n', lock MN n n') by (consider (trans_lock MN n n); eauto with LTS).
      exists n, n'.
      repeat split; intros; eauto with LTS.
      destruct `(_ = _ \/ _); subst; eauto with LTS.
    + assert (n = m \/ (n <> m /\ trans_lock MN n m)) as [|]
          by (smash_eq n m; destruct `(_ = _ \/ _); attac); clear H2; subst.
      * assert (m' = self (MN m')) by attac.
        assert (m = self (MN m)) by attac.
        assert (locked (MN m) = Some m') by attac.
        consider (exists m'', lock MN m' m'').
        {
          consider (trans_lock MN m' m). eapply dep_loop; eauto with LTS. eapply SRPC_lock_set_uniq; attac.
          all: eauto with LTS.
        }
        assert (locked (MN m') = Some m'') by attac.
        exists m, m'.
        repeat split; intros; eauto.
        1: { destruct `(_ = _ \/ _); subst; eauto with LTS. }

        unfold sends_to, active_ev_of, active_probe_of, NetGet in *.
        destruct (NetMod.get m' MN) as [MQ' M' S'] eqn:HMN'.
        destruct (NetMod.get m MN) as [MQ M S] eqn:HMN.
        assert (m = m' -> M = M' /\ MQ = MQ' /\ m' = m'') by attac.
        clear HMN HMN'.
        hsimpl in *; simpl in *.
        generalize dependent M.
        induction M'; intros.
        -- destruct state; hsimpl in *; simpl in *.
           consider (sends_probe _ _ _).
           ++ right; right; right; right. eattac.
           ++ destruct `(In _ _ \/ _).
              ** right; right; left. exists n'. eattac.
              ** right; right; right; left. eattac.
        -- consider (sends_probe _ _ _); attac.
           destruct (NAME.eq_dec (self M) (self M')); attac.
           ++ rewrite <- e in *. clear e.
              attac.
              specialize IHM' with (M := M').
              destruct IHM' as [|[|[|[|]]]]; attac.
              right; right; left.
              destruct `(_ \/ _); constructor; attac.
           ++ specialize IHM' with (M := M).
              destruct IHM' as [|[|[|[|]]]]; attac.
              right; right; left.
              destruct `(_ \/ _); constructor; attac.
      * assert (m' = self (MN m')) by attac.
        assert (m = self (MN m)) by attac.
        assert (n = self (MN n)) by attac.
        assert (locked (MN m) = Some m') by attac.
        consider (exists m'', lock MN m' m'').
        {
          consider (trans_lock MN m' n). eapply dep_loop; eauto with LTS. eapply SRPC_lock_set_uniq; attac.
          all: eattac.
        }
        assert (locked (MN m') = Some m'') by attac.
        hsimpl in *.
        exists m, m'.
        repeat split; intros; eauto.
        1: { destruct `(_ = _ \/ _); subst; eauto with LTS. }

        unfold sends_to, active_ev_of, active_probe_of, NetGet in *.
        destruct (NetMod.get n MN) as [MQ0 M0 S0] eqn:HMN0.
        destruct (NetMod.get m' MN) as [MQ' M' S'] eqn:HMN'.
        destruct (NetMod.get m MN) as [MQ M S] eqn:HMN.
        assert (n = m' -> M0 = M' /\ MQ0 = MQ') by attac.
        clear HMN HMN' HMN0.
        hsimpl in *; simpl in *.
        generalize dependent M0.
        induction M'; intros.
        -- destruct state; hsimpl in *; simpl in *.
           consider (sends_probe _ _ _).
           ++ right; right; right; right. eattac.
           ++ destruct `(In _ _ \/ _).
              ** right; right; left. exists n'. eattac.
              ** right; right; right; left. eattac.
        -- consider (sends_probe _ _ _); attac.
           destruct (NAME.eq_dec (self M0) (self M')); attac.
           ++ rewrite <- e in *. clear e.
              attac.
              specialize IHM' with (M0 := M').
              destruct IHM' as [|[|[|[|]]]]; attac.
              right; right; left.
              destruct `(_ \/ _); constructor; attac.
           ++ specialize IHM' with (M0 := M0).
              destruct IHM' as [|[|[|[|]]]]; attac.
              right; right; left.
              destruct `(_ \/ _); constructor; attac.
    + exists n, n'.
      repeat split; intros; eauto with LTS.
      destruct `(_ \/ _); subst; eauto with LTS.
  - unfold PaperCompat.ac in *.
    hsimpl in *.
    consider (exists n', lock MN n n') by (consider (trans_lock MN n n); eauto with LTS).
    destruct `(_ \/ _) as [|[|[|[|[|]]]]]; hsimpl in *; eauto with LTS.
    + econstructor 3 with (n':=n'); eauto.
      enough (locked (MN n) = Some n'); attac.
    + econstructor 2 with (m:=n1)(m':=n2); eauto.
      unfold sends_to, active_ev_of, active_probe_of, NetGet in *.
      destruct (NetMod.get n2 MN).
      induction mserv_m0; attac.
      consider (sends_to_mon _ _ _); attac.
      specialize (IHmserv_m0 ltac:(auto)).
      econstructor 4; eattac.
      destruct `(_ \/ _); eauto.
    + smash_eq n n2.
      {
        consider (n'0 = n') by (eapply SRPC_lock_set_uniq; eattac).
        constructor 3 with (n':=n'); eattac.
      }

      econstructor 2 with (m:=n1)(m':=n2); eauto with LTS.

      assert (NoRecvR_from n'0 (mserv_q (MN n2))).
      {
        unfold NoRecvR_from, NetGet, lock, lock_set in *. attac.
        destruct (NetMod.get n2 MN) as [MQ0 M0 S0] eqn:?.
        consider (serv_lock _ (NetMod.get n2 _)). attac.
        intros ?.
        apply H13 with (v:=v) in H4.
        unfold deinstr in *. rewrite NetMod.get_map in *. attac.
        unfold serv_deinstr in *. attac.
        destruct S0; attac.
      }

      assert (NoSends_MQ (mserv_q (MN n2))).
      {
        unfold NetGet, lock, lock_set in *. attac.
        destruct (NetMod.get n2 MN) as [MQ0 M0 S0] eqn:?.
        consider (serv_lock _ (NetMod.get n2 _)). attac.
        apply Forall_forall. intros. destruct x; attac.
        apply H14 with (v:=v) in H4.
        unfold deinstr in *. rewrite NetMod.get_map in *. attac.
        unfold serv_deinstr in *. attac.
        destruct S0; attac.
        apply in_split in H10; attac.
        clear - H15.
        induction l1; attac.
        destruct a; attac.
      }

      assert (locked (MN n2) = Some n'0) by attac.
      assert (self (MN n2) = n2) by attac.

      unfold sends_to, active_ev_of, active_probe_of, NetGet in *.
      hsimpl in *. simpl in *.
      destruct (NetMod.get n2 MN) as [MQ0 M0 S0].
      hsimpl in *; simpl in *.
      induction M0.
      * apply in_split in H6 as (MQ0l & MQ0r & ?); subst.
        econstructor 2; attac.
        intros ? ?.
        eapply H8; eattac.
      * hsimpl in *. simpl in *.
        unfold Name in *; attac.
        destruct (NameTag_eq_dec to (n1, R)),
          (MProbe_eq_dec msg0 {| origin := n; lock_id := lock_count (Transp.Net.NetMod.get n MN) |}).
        2,3,4: constructor 4; eattac.
        subst.
        constructor 3.
    + smash_eq n n2.
      {
        consider (n'0 = n') by (eapply SRPC_lock_set_uniq; eattac).
        constructor 3 with (n':=n'); eattac.
        rewrite `(mserv_q _ = _). attac.
      }

      econstructor 2 with (m:=n1)(m':=n2); eauto with LTS.

      assert (NoRecvR_from n'0 (mserv_q (MN n2))).
      {
        clear - H4 H6.
        unfold active_ev_of, active_probe_of, NoRecvR_from, NetGet, lock, lock_set in *; attac.
        destruct (NetMod.get n2 MN) as [MQ0' M0 S0] eqn:?.
        consider (serv_lock _ (NetMod.get n2 _)).
        attac.
        intros ?.
        apply H1 with (v:=v) in H4.
        unfold deinstr in *. rewrite NetMod.get_map in *. attac.
        unfold serv_deinstr in *. attac.
        destruct S0; attac.
        intros ?.
        attac.
        apply H1 with (v:=v) in H4.
        unfold deinstr in *. rewrite NetMod.get_map in *. attac.
        unfold serv_deinstr in *. attac.
        destruct S0; attac.
      }

      assert (NoSends_MQ (mserv_q (MN n2))).
      {
        unfold NetGet, lock, lock_set in *. attac.
        destruct (NetMod.get n2 MN) as [MQ0' M0 S0] eqn:?.
        consider (serv_lock _ (NetMod.get n2 _)).
        apply Forall_forall. intros. destruct x; attac.
        apply H14 with (v:=v) in H4.
        unfold deinstr in *. rewrite NetMod.get_map in *. attac.
        unfold serv_deinstr in *. attac.
        destruct S0; attac.
        clear - H10 H15.
        destruct `(_ \/ _).
        - apply in_split in H; hsimpl in *.
          induction l1; attac. destruct a; attac.
        - apply in_split in H; hsimpl in *.
          induction MQ0; attac.
          + induction l1; eattac. destruct a; attac.
          + destruct a; attac.
      }

      assert (locked (MN n2) = Some n'0) by attac.
      assert (self (MN n2) = n2) by attac.

      unfold sends_to, active_ev_of, active_probe_of, NetGet in *.
      hsimpl in *. simpl in *.
      destruct (NetMod.get n2 MN) as [MQ0' M0 S0].
      hsimpl in *; simpl in *.
      induction M0.
      * apply in_split in H7 as (MQ0l & MQ0r & ?); subst.
        econstructor 2; attac.
        intros ? ?.
        eapply H8; eattac.
      * hsimpl in *. simpl in *.
        unfold Name in *; attac.
        destruct (NameTag_eq_dec to (n1, R)),
          (MProbe_eq_dec msg0 {| origin := n; lock_id := lock_count (Transp.Net.NetMod.get n MN) |}).
        2,3,4: constructor 4; eattac.
        subst.
        constructor 3.
    + econstructor 2 with (m:=n1)(m':=n); eauto.
      1: {
        enough (serv_client n1 (NetMod.get n '' MN)). assert (well_formed MN). attac. kill H7.
        eapply H_lock_complete. eattac.
        unfold deinstr, serv_deinstr in *.
        attac.
        unfold NetGet in *.
        destruct (NetMod.get n MN) eqn:?.
        attac.
      }

      assert (NoRecvR_from n' (mserv_q (MN n))).
      {
        unfold NoRecvR_from, NetGet, lock, lock_set in *. attac.
        destruct (NetMod.get n MN) as [MQ0 M0 S0] eqn:?.
        consider (serv_lock _ (NetMod.get n _)). attac.
        intros ?.
        apply H10 with (v:=v0) in H5.
        unfold deinstr in *. rewrite NetMod.get_map in *. attac.
        unfold serv_deinstr in *. attac.
        destruct S0; attac.
      }

      assert (NoSends_MQ (mserv_q (MN n))).
      {
        unfold NetGet, lock, lock_set in *. attac.
        destruct (NetMod.get n MN) as [MQ0 M0 S0] eqn:?.
        consider (serv_lock _ (NetMod.get n _)). attac.
        apply Forall_forall. intros. destruct x; attac.
        apply H11 with (v:=v0) in H5.
        unfold deinstr in *. rewrite NetMod.get_map in *. attac.
        unfold serv_deinstr in *. attac.
        destruct S0; attac.
        apply in_split in H7; attac.
        clear - H12.
        induction l1; attac.
        destruct a; attac.
      }

      assert (locked (MN n) = Some n') by attac.
      assert (self (MN n) = n) by attac.

      unfold sends_to, active_ev_of, active_probe_of, NetGet in *.
      hsimpl in *. simpl in *.
      destruct (NetMod.get n MN) as [MQ0 M0 S0].
      simpl in *.
      induction M0.
      * apply in_split in H4; attac.
        econstructor 1; attac.
        unfold NoRecvR_from in *; attac.
        specialize (H6 v0).
        attac.
      * hsimpl in *. simpl in *.
        unfold Name in *; attac.
        destruct (NameTag_eq_dec to (n1, R)),
          (MProbe_eq_dec msg0 {| origin := self M0; lock_id := lock_count M0 |}).
        2,3,4: constructor 4; eattac.
        subst.
        constructor 3.
Qed.
(* end hide *)

(** * Introduction *)

(** This file outlines the mechanised theory presented in our submission to
OOPSLA 2025. The structure of this file closely follows how the submission is
divided into sections. Theorems and definitions used in the submissions are
pointed out in third-level headers. This outline works best if viewed
interactively in a Coq/Rocq IDE, because it allows previewing context-dependent
outputs. *)

(** ** Differences *)
(** The mechanisation introduces some concepts in a slightly different flavour,
mostly due to quirks of the tool; we provided explanations where the connection
might be less obvious. The most notable differences are:

- We do not provide semantics for generic SRPC processes. Instead, the
  mechanisation operates on _concrete processes_ implemented directly in Gallina
  via coinduction. [SRPC] is then a coinductive property that asserts adherence
  to the SRPC protocol as described in the submission.

- The mechanisation does not include _casts_, and the [C] tag is non-existent.

- We do not allow "no-client" (n^\bot) SRPC states. All working and locked
  processes must handle a query from another member of the network.

The lack of "clientless" SRPC states makes well-formedness much more
restrictive. This is because each service named [n0] that is [Working n1] needs
to be paired with an actual service [n1] that is locked on it (recall the
equivalence between _lock_ and _client_ relations in Definition 6.4, point 2).
Consequently, [n1] must be [Locked n2 n0] for some [n2] --- which in turn must
be locked on [n1]. This expands endlessly, requiring the _sort_ of names to be
infinite (otherwise we would "run out of" names for services that are neither
ready nor locked in cycles). Our mechanisation is compatible with that
requirement: the only restriction we put on the [Name] type is that it belongs
to the [Set] sort and has decidable equality. This lets us model an initially
[Working] service [n0] via an infinite stream of services transitively locked on
[n0]. To this end, we provide an Erlang-inspired framework ([GenServerNet]) for
modelling well-formed initial networks with [gen_server]-style services and
initiators to engage with them as external clients. The framework is also used
to show that our invariants are mutually sound and hold in a practical class of
systems. See the "appendix" of this file for more details and examples. *)

(** ** Axioms and other things that may appear "assumed"

A couple of objects are declared as "Axioms", "Parameters", "Variables". Most of
them are abstracting away definitions that are not relevant for the modules they
are declared in, and are specialised only when their implementation matters. The
full list is attached below:

- [Val : Set] (in [DlStalk.ModelData] and [DlStalk.GenFramework]) --- The
  message payload. Never used in the theory, instantiated to [nat] only in
  examples for our [gen_server]-ish framework.

- [valnat : Val = nat] (in [DlStalk.GenFramework]) --- Used to "forcefully"
  instantiate [Val] to [nat] in the examples as stated above.

- [some_name : Name] (in [DlStalk.Locks]) --- We assume that [Name] is
  non-empty, otherwise the theory does not make any sense.

- [some_val : Val] (in [DlStalk.Locks]) --- We assume that [Val] is non-empty.

- [Msg : Set] (in [DlStalk.Model]) --- Uninstantiated probe type. Abstracted
  where the theory does not need it.

- [MState : Set] (in [DlStalk.Model]) --- Uninstantiated monitor state type.
  Abstracted where the theory does not need it.

- [mon_handle : EMsg -> MState -> MProc] (in [DlStalk.Model]) --- Uninstantiated
  monitor algorithm function. Abstracted where the theory does not need it.

- [lock_uniq : lock_uniq_type], [lock_uniq0], [lock_uniq1] (in
  [DlStalk.NetLocks]) --- section parameter, instantiated in
  [SRPC_lock_set_uniq].

- [lock_neq_nil : lock_neq_nil_type], [lock_neq_nil0], [lock_neq_nil1] (in
  [DlStalk.NetLocks]) --- section parameter, instantiated in
  [SRPC_lock_set_neq_nil].

- [lock_dec : lock_dec_in] (in [DlStalk.NetLocks]) --- section parameter,
  instantiated in [well_formed_lock_dec].

- [DlStalk.Network.NET_MOD] --- Abstraction of "updatable functions". The
  interface, akin to a typical hash map, declares a constructor type [t] for the
  collection, a couple of methods, and a few "axioms" such as [get_put_eq]
  saying that accessing a freshly updated service indeed returns that service.
  Note that it is a total mapping, thus for every [Name] there must be a
  corresponding service [Serv]. We left it unimplemented because Coq standard
  library does not offer good data structures supporting extensional equality.

On top of that, we extensively use module types following the pattern proposed
by Michael Soegtrop in
https://coq-club.inria.narkive.com/ux8RG4m7/module-best-practices . While useful
in code organisation, this sometimes obfuscates in-code locations of identifiers
--- we therefore explicitly point to [.v] files where automatic navigation
provided by [coqdoc] fails. *)


(** * Correctness Criteria for Deadlock Detection Monitors in Distributed Systems *)

(** We begin by introducing generic definitions and notations for labelled
transition systems (see [DlStalk.LTS]). [LTS] is a class instantiated by almost
all entities featuring operational semantics in the submission. We use [N0
=(a)=> N1] to say that [N0] transitions to [N1] through some action [a].
Similarly, [N0 =[path]=> N1] means that [N0] can reach [N1] through a sequence
of transitions following path (a list of actions) [path]. *)
Print LTS.
Print ptrans.
Locate "_ =( _ )=> _".
Locate "_ =[ _ ]=> _".


Module CorrectnessCriteria.
  (** ** Transparency *)
  (** *** _Criterion 2.1_ *)
  (** [Net] is an _unmonitored network_, [MNet] is _monitored_. [instr] is an
  _instrumentation_. Their definitions are discussed later in this document. We
  use names like [ppath] to describe paths of unmonitored networks, and [mpath]
  for monitored. *)

  Definition transp_completeness (N0 : Net) (i0 : instr) :=
    forall path N1, (N0 =[ path ]=> N1) ->
    exists mpath (i1 : instr), (i0 N0 =[ mpath ]=> i1 N1).

  Definition transp_soundness (N0 : Net) (i0 : instr) :=
    forall mpath0 (MN1 : MNet), (i0 N0 =[ mpath0 ]=> MN1) ->
    exists mpath1 ppath (i2 : instr) (N2 : Net),
      (MN1 =[ mpath1 ]=> i2 N2) /\ (N0 =[ ppath ]=> N2).

  (** ** Preciseness *)
  (** *** _Criterion 2.2_ *)

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
    /\ detect_completeness N i
    /\ detect_soundness N i.
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

(** *** _Definition 3.1_ : Services (and queues) *)

Check ((_ : Que Val) : list (Name * Tag * Val)).

Print Serv.
Check serv_i : Serv -> Que Val.
Check serv_p : Serv -> Proc.
Check serv_o : Serv -> Que Val.

(** *** _Definition 3.2_ : Abstract and concrete SRPC processes, and SRPC services *)

(** The mechanisation operates primarily on concrete processes ([Proc])
programmed coinductively in Gallina (see [DlStalk.Model]). *)
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

(** The generic SRPC process is captured under the [SRPC_State] type (see [DlStalk.SRPC]). *)

Print SRPC_State.
Print SRPC_Busy_State.

(** *** _Fig 3_ : We characterise concrete SRPC processes via a coinductive property [SRPCC]
to describe the simulation relation, and [SRPCI] for inductive features such as
weak termination of each query. (see [DlStalk.PresentationCompat]) *)

Print PaperCompat.SRPCC.

(** [[
CoInductive SRPCC : SRPC_State -> Proc -> Prop :=
    SRPCC_R : forall P0 : Proc,
              (forall (c : Que.Channel.Name) (v : Que.Channel.Val)
                 (P1 : Proc),
               P0 =( Recv (c, Q) v )=> P1 -> SRPCC ((Working) c) P1) ->
              SRPCI Ready P0 -> SRPCC Ready P0
  | SRPCC_W : forall (c : Que.Channel.Name) (P0 : Proc),
              (forall (v : Que.Channel.Val) (P1 : Proc),
               P0 =( Send (c, R) v )=> P1 -> SRPCC Ready P1) ->
              (forall P1 : Proc,
               P0 =( Tau )=> P1 -> SRPCC ((Working) c) P1) ->
              (forall (s : Que.Channel.Name) (v : Que.Channel.Val)
                 (P1 : Proc),
               P0 =( Send (s, Q) v )=> P1 -> SRPCC ((Locked) c s) P1) ->
              SRPCI ((Working) c) P0 -> SRPCC ((Working) c) P0
  | SRPCC_L : forall (c : Srpc.Locks.Proc.Que.Channel.Name)
                (s : Que.Channel.Name) (P0 : Proc),
              (forall (v : Que.Channel.Val) (P1 : Proc),
               P0 =( Recv (s, R) v )=> P1 -> SRPCC ((Working) c) P1) ->
              SRPCI ((Locked) c s) P0 -> SRPCC ((Locked) c s) P0.
]]
 *)

Print PaperCompat.SRPCI.

(** [[
Inductive SRPCI : SRPC_State -> Proc -> Prop :=
    SRPCI_R : forall
                h : Srpc.Locks.Proc.Que.Channel.Name * Tag_ ->
                    option (Que.Channel.Val -> Proc),
              (forall (c : Srpc.Locks.Proc.Que.Channel.Name) (t : Tag_),
               h (c, t) <> None -> t = Q) ->
              (forall (c : Srpc.Locks.Proc.Que.Channel.Name)
                 (v : Que.Channel.Val),
               exists cont : Que.Channel.Val -> Proc,
                 h (c, Q) = Some cont /\ SRPCI ((Working) c) (cont v)) ->
              SRPCI Ready (PRecv h)
  | SRPCI_WR : forall (c : Srpc.Locks.Proc.Que.Channel.Name)
                 (v : Que.Channel.Val) (P : Proc),
               SRPCI ((Working) c) (PSend (c, R) v P)
  | SRPCI_WT : forall (c : Srpc.Locks.Proc.Que.Channel.Name) (P : Proc),
               SRPCI ((Working) c) P ->
               SRPCI ((Working) c) (STau P)
  | SRPCI_WQ : forall (c s : Srpc.Locks.Proc.Que.Channel.Name)
                 (v : Que.Channel.Val) (P : Proc),
               SRPCI ((Locked) c s) P ->
               SRPCI ((Working) c) (PSend (s, Q) v P)
  | SRPCI_L : forall (c s : Srpc.Locks.Proc.Que.Channel.Name)
                (h : Srpc.Locks.Proc.Que.Channel.Name * Tag_ ->
                     option (Que.Channel.Val -> Proc))
                (cont : Que.Channel.Val -> Proc),
              (forall nc : Srpc.Locks.Proc.Que.Channel.Name * Tag_,
               h nc <> None -> nc = (s, R)) ->
              h (s, R) = Some cont ->
              (forall v : Que.Channel.Val, SRPCI ((Working) c) (cont v)) ->
              SRPCI ((Locked) c s) (PRecv h).
]]
 *)

(** Internally, the mechanisation uses a bit more messy [SRPC] property. We
prove both equivalent. (see [DlStalk.SRPC] and [DlStalk.PresentationCompat]). *)

Print SRPC.
Print SRPC_Busy.

Check SRPC_eq : forall (P : Proc) (srpc : SRPC_State),
    SRPC srpc P <-> PaperCompat.SRPCC srpc P.

(** *** _Definition 3.4_ : Semantics of services (see [DlStalk.Que] and [DlStalk.Model]). *)
(** Queue actions *)

Print QAct.

(** [[
  Inductive QAct (E : Set) : Set :=
    QEnq : Que.Channel.NameTag -> E -> QAct E
  | QDeq : Que.Channel.NameTag -> E -> QAct E.
]]
 *)

(** Generic actions used by processes, services and monitored services. [Tau] is
opaque in the mechanisation. *)

Print Act.

(** [[
Inductive Act (Payload : Set) : Set :=
    Send : Que.Channel.NameTag -> Payload -> Act
  | Recv : Que.Channel.NameTag -> Payload -> Act
  | Tau : Act.
]]
 *)

(** *** _Fig 4_ : Process Queue and Service transitions *)
(** All are instances of the LTS class. *)
Print ProcTrans.
Print QTrans.
Print STrans.

Check trans_Serv : LTS PAct Serv.

(** *** _Definition 3.5_ : Networks *)
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

(** *** _Fig 5_ : Network semantics. *)
(** [NVTrans] is used as a helper to progress nodes within a network (see
[DlStalk.Network]). *)
Print NVTrans.
Print NTrans.

Goal Net = NetMod.t Serv.
Proof. reflexivity. Defined.

(** ** Locks and Deadlocks *)
(** *** _Definition 3.6_ : Lock (see [DlStalk.PresentationCompat]) *)

Print PaperCompat.serv_lock.

(** [[
fun (n : Name) (S : Serv) =>
    (forall (v : Val) (E : Val), ~ Deq (n, R) v (serv_i S) E)
 /\ (exists c : Name, SRPC (Locked c n) (serv_p S))
 /\ serv_o S = []
]]
 *)

(** *** _Definition 3.7_ : Deadlock (see [DlStalk.PresentationCompat]) *)

Print PaperCompat.dead_set.

(** [[
PaperCompat.dead_set =
  fun (DS : Names) (N : Net) =>
     DS <> []
  /\ (forall n0, In n0 DS -> exists n1, lock N n0 n1 /\ In n1 DS)
]]
 *)

(** Definitions used in the proofs are slightly different, i.e. more general to
aim at compatibility with the OR model (see [DlStalk.Locks] and
[DlStalk.NetLocks]). *)
Print proc_lock.
Print serv_lock.
Print lock_set.
Print lock.
Print dead_set.

(** Compatibility of project and submission definitions (for SRPC services; see
[DlStalk.SRPCNet]). Note that [proc_lock] is more generic and uses lock lists
--- for future compatibility with the OR model. In case of SRPC this is always a
singleton (modulo duplicates). Additionally, [serv_lock] relies on an additional
predicate [Decisive], which asserts that the process does not receive queries
and responses at the same time --- in the submission, this problem is irrelevant
as it is prevented by the syntax, thus not mentioned there to avoid confusion.
*)
Print Decisive.
Check serv_lock_eq : forall S n,
    (exists srpc, SRPC_serv srpc S) ->
    serv_lock [n] S <-> PaperCompat.serv_lock n S.

Check dead_set_eq : forall (N : Net) (DS : Names),
    SRPC_net N ->
    dead_set DS N <-> PaperCompat.dead_set DS N.

(** *** _Lemma 3.8_ *)
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
    serv_lock [n] S <-> PaperCompat.serv_lock n S.

Check dead_set_eq : forall (N : Net) (DS : Names),
    SRPC_net N ->
    dead_set DS N <-> PaperCompat.dead_set DS N.

(** * A Model of Generic Distributed Black-Box Outline Monitors *)

(** ** Monitored Services and Networks *)


(** *** _Definition 4.1_ : Monitored services (see [DlStalk.Model]) *)
(** **** Monitor messages *)
(** Items stored in the monitor queue. [MqProbe] is an _incoming_ probe.
Outgoing probes are handled differently, as described below. *)
Print EMsg.
(** [[
Inductive EMsg : Set :=
    MqSend : (Name * Tag) -> Val -> EMsg
  | MqRecv : (Name * Tag) -> Val -> EMsg
  | MqProbe : (Name * Tag) -> MProbe' -> EMsg.
]]
 *)

Goal MQue = list EMsg.
Proof. reflexivity. Defined.

(** **** Monitor process *)
(** In the mechanisation, monitors do not push outgoing
messages to the front of their queues, but instead they maintain a "monitor
process" with two possible states: receiving ([MRecv]), when it is ready to pick
a message from the monitor queue (equivalent to _not_ having an outgoing probe
at the front of the queue); and sending ([MSend]), where the monitor sends a
probe to another monitored service (equivalent to having that outgoing message
at the front of the monitor queue). *)
Print MProc.
Check MRecv : MState -> MProc.
Check MSend : (Name * Tag) -> MProbe -> MProc -> MProc.

(** **** Monitored service *)
Print MServ.
(** Monitor queue *)
Check mserv_q : MServ -> MQue.
(** Monitor process / monitor state *)
Check mserv_m : MServ -> MProc.
(** Supervised service *)
Check mserv_s : MServ -> Serv.

(** *** _Fig 9_ : Semantics of monitored services (see [DlStalk.Model]) *)
Print MTrans.

(** *** _Definition 4.3_ : Monitored networks *)
(** We reuse the same network model, but with monitored services.
Internal/external actions are abstracted through a the [gen_Act] class, so
everything connects smoothly (see [DlStalk.Network] and [DlStalk.Transp]). *)

Goal MNet = NetMod.t MServ.
Proof. reflexivity. Defined.

Check (NetMod.get : Name -> MNet -> MServ).
Check (NetMod.get : Name -> Net  -> Serv).

(** ** Instrumentation of Services and Transparency *)

(** *** _Definition 4.4_ : Instrumentation *)
(** (see [DlStalk.Model] and [DlStalk.Transp]) *)
Print mon_assg.
Print instr.
Check apply_instr : instr -> Net -> MNet.

(** *** _Definition 4.5_ : Deinstrumentation *)
(** [deinstr] is a _Coercion_: that means, we can apply predicates defined for
unmonitored networks (e.g. [dead_set]) to monitored networks. In such a case,
[deinstr] would be applied implicitly (see [DlStalk.Model] and
[DlStalk.Transp]). *)
Print retract_recv.
Print retract_send.
Print serv_deinstr.
Print deinstr.

(** *** _Proposition 4.6_ *)
Check instr_inv : forall (i : instr) N, deinstr (i N) = N.

(** *** _Definition 4.7_ : Stripping monitor actions *)

Print MNAct_to_PNAct.
(** [[
fix MNAct_to_PNAct (ma : MNAct) :=
  match ma with
  | NComm n m t (MValP v) => Some (@NComm PAct _ n m t v)
  | NTau n (MActP Tau) => Some (NTau n Tau)
  | _ => None
  end  : MNAct -> option PNAct.
]]
 *)

Print MNPath_to_PNPath.
(** [[
fix MNPath_to_PNPath (mpath : list MNAct) : list PNAct :=
  match mpath with
  | [] => []
  | ma :: mpath' =>
      match MNAct_to_PNAct ma with
      | None => MNPath_to_PNPath mpath'
      | Some a => a :: MNPath_to_PNPath mpath'
      end
  end  : list MNAct -> list PNAct.
]]
 *)

(** *** _Lemma 4.9_ *)
(** We realised that proofs in the [DlStalk.Transp] module do not expose the
path correspondence for completeness (the [MNPath_to_PNPath mpath = path] part).
To fix this, we provide an additional module [DlStalk.TranspImproved] which
serves as a replacement for [DlStalk.Transp], where the full version is
addressed. *)

Module TranspImprovedSandbox.
  Require DlStalk.TranspImproved.
  Module Import TI := Empty <+ DlStalk.TranspImproved.TRANSP(DetConf).
  Check @transp_complete : forall path (i0 : instr) (N0 N1 : Net),
      (N0 =[ path ]=> N1) ->
      exists (mpath : list MNAct) (I1 : instr),
        (i0 N0 =[ mpath ]=> I1 N1)
        /\ MNPath_to_PNPath mpath = path.
End TranspImprovedSandbox.

(** *** _Theorem 4.8_ : Transparency --- completeness *)
Lemma oopsla_transp_completeness : forall N0 i0,
    CorrectnessCriteria.transp_completeness N0 i0.

Proof.
  unfold CorrectnessCriteria.transp_completeness.
  intros.
  specialize @transp_complete with (I0:=i0)(path:=path)(N0:=N0)(N1:=N1)
    as (mpath & i1 & ?); attac.
Qed.

(** *** _Lemma 4.12_ *)
(** We first prove that a path of *any* monitored network is replicable after
deinstrumentation. *)
Check MNPath_do : forall (mpath : list (NAct (Act:=MAct))) (MN0 MN1 : MNet),
    MN0 =[ mpath ]=> MN1 -> deinstr MN0 =[ mpath ]=> deinstr MN1.

(** We now show the statement from the submission. *)

Goal forall (N0 : Net) (i0 : instr) mpath0 (MN1 : MNet),
    (i0 N0 =[ mpath0 ]=> MN1) ->
    exists mpath1 (i2 : instr) (N2 : Net),
      (MN1 =[ mpath1 ]=> i2 N2)
    /\ (N0 =[ MNPath_to_PNPath (mpath0 ++ mpath1) ]=> N2).
Proof.
  intros.
  specialize @transp_sound_instr with (mnpath0:=mpath0)(I0:=i0)(N0:=N0)(MN1:=MN1)
    as (mpath1 & ppath & i2 & N2 & ? & ?); auto.
  exists mpath1, i2, N2.
  split; auto.
  assert (deinstr (i0 N0) =[mpath0 ++ mpath1]=> deinstr (i2 N2))
    by eauto using MNPath_do with LTS.
  repeat (rewrite instr_inv in * ).
  remember (mpath0 ++ mpath1) as mpath; clear Heqmpath.
  clear - H2.
  generalize dependent N0.
  induction mpath; attac.
  apply IHmpath in H3.
  consider (N0 =(a)=> N1); attac.
  - destruct_ma a0; eattac.
    apply path_seq1 with (middle:=(NetMod.put n &S N0)); attac.
  - destruct v; attac.
    apply path_seq1 with (middle:=(NetMod.put n' &S (NetMod.put n &S0 N0))); eattac.
    econstructor; eattac.
Qed.


(** *** _Theorem 4.11_ : Transparency --- soundness *)
Lemma oopsla_transp_soundness : forall N0 i0,
    CorrectnessCriteria.transp_soundness N0 i0.

Proof.
  unfold CorrectnessCriteria.transp_soundness.
  intros.
  eauto using transp_sound_instr.
Qed.

(** * A Distributed Black-Box Monitoring Algorithm for Deadlock Detection *)

(** *** _Proposition 5.1_ : Deadset-cycle equivalence (see [DlStalk.NetLocks]) *)
Check dead_set_cycle : forall N : Net,
    lock_uniq_type N -> lock_neq_nil_type N -> locks_dec_in N ->
    forall DS, dead_set DS N -> exists n, In n DS /\ trans_lock N n n.

Check cycle_dead_set : forall N : Net,
    lock_uniq_type N -> lock_neq_nil_type N ->
    forall n, trans_lock N n n -> exists DS, In n DS /\ dead_set DS N.


(** *** _Definition 5.2_ Implementation of the algorithm (see [DlStalk.Compl])
*)
(** **** Monitor state (see [DlStalk.Compl]). *)
(** We implement "fresh probes" by storing the name of the originator ([self]
becomes [origin]) and counting how many times the service has been locked
([lock_count] becomes [lock_id]). *)
Locate MState.
Print MState'.
Check self       : MState -> Name.
Check locked     : MState -> option Name.
Check wait       : MState -> list Name.
Check lock_count : MState -> nat.
Check alarm      : MState -> bool.

(** **** Probes *)
(** [MProbe] is an alias for a slightly more generic [MProbe'] (see
[DlStalk.Compl]) *)
Locate MProbe.
Print MProbe'.
Check origin  : MProbe -> Name.
Check lock_id : MProbe -> nat.

Module Type Alg.
  (* It needs to be a bit backdoored to instantiate abstract parameters *)
  Declare Module Conf : DETECT_CONF.
  Declare Module Params : MON_PARAMS(Conf).
  Include Mh(Conf)(Params).

  (** **** The algorithm *)
  Check mon_handle : EMsg -> MState -> MProc.
  Print mon_handle.
End Alg.

(** * Proving the Preciseness of Our Distributed Deadlock Detection Monitors *)

(** ** Invariant Properties of Well-Formed SRPC Networks *)

(** *** _Definition 6.2_ : The client relation *)
(** (see [DlStalk.NetLocks] and [DlStalk.PresentationCompat] for compatibility
lemmas) *)
Print PaperCompat.client.
Print serv_client.
Check client_eq : forall n S, serv_client n S <-> PaperCompat.client n S.

(** *** _Definition 6.3_ : Well-formedness *)
(** (see [DlStalk.SRPCNet]) *)
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

(** *** _Definition 6.4_ *)
Print well_formed.

(** *** _Theorem 6.5_ *)
Check well_formed_invariant : trans_invariant well_formed always.

(** ** Monitor Knowledge Invariant for Complete Deadlock Detection  *)
(** (see [DlStalk.Compl]) *)

Print sends_probe.

(** *** _Definition 6.8_ *)

Print PaperCompat.ac.

(** [[
PaperCompat.ac =
fun (n : Name) (MN : MNet) =>
exists (n1 : Name) (n2 : Que.Channel.Name),
  trans_lock '' MN n n1 /\
  lock '' MN n1 n2 /\
  (forall n' : Que.Channel.Name,
   n' = n2 \/ trans_lock '' MN n' n2 -> locked (MN n') <> None) /\
  (alarm (MN n) = true \/
   (exists n' : DetConf.NAME.t',
      locked (MN n) = Some n' /\ In (active_ev_of MN n' n) (mserv_q (MN n))) \/
   sends_to MN n2 n1 (active_probe_of MN n) \/
   (exists n' : Que.Channel.Name,
      lock '' MN n2 n' /\
      In (active_ev_of MN n' n) (mserv_q (MN n2)) /\ In n1 (wait (MN n2))) \/
   (exists
      (n' : Que.Channel.Name) (v : Mon.Proc.Que.Channel.Val)
    (MQ0 MQ1 : MQue),
      lock '' MN n2 n' /\
      mserv_q (MN n2) = MQ0 ++ active_ev_of MN n' n :: MQ1 /\
      In (MqRecv (n1, Q) v) MQ0) \/
   (exists v : Mon.Proc.Que.Channel.Val,
      In (MqRecv (n1, Q) v) (mserv_q (MN n))))
     : Name -> MNet -> Prop
]]
 *)

(** The definition used in the mechanisation is slightly different, but we show
them equivalent for deadlocked processes in [KIC] networks (the only place where
it is used). *)

Print alarm_condition.

Check alarm_condition_eq : forall (n : Name) (MN : MNet),
    KIC MN -> trans_lock '' MN n n ->
    alarm_condition n MN <-> PaperCompat.ac n MN.

(** *** _Definition 6.7_ *)
Print KIC.

(** *** _Lemma 6.9_ *)
Check ac_to_alarm : forall MN0 n,
    KIC MN0 ->
    alarm_condition n MN0 ->
    trans_lock '' MN0 n n ->
    exists DS mpath MN1,
      (MN0 =[ mpath ]=> MN1)
      /\ dead_set DS '' MN0
      /\ detect_path DS mpath
      /\ alarm (MN1 n) = true.

(** *** _Theorem 6.10_ *)
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

(** *** _Definition 6.11_ *)
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

(** Monitor message (in monitor queue) holding an active probe *)
Print active_ev_of.

(** *** _Theorem 6.12_ *)
Check KIS_invariant : trans_invariant KIS always.

(** ** Deadlock Detection Preciseness Result *)

(** *** _Theorem 6.13_ *)

Check KIS_detection_sound : forall (i0 : instr) N0 MN1 mpath n,
    KIS (i0 N0) -> (i0 N0 =[ mpath ]=> MN1) ->
    alarm (MN1 n) = true ->
    exists DS, dead_set DS '' MN1 /\ In n DS.


Check KIC_detection_complete : forall (i0 : instr) N0 MN1 mpath0 DS,
    KIC (i0 N0) ->
    (i0 N0 =[ mpath0 ]=> MN1) ->
    dead_set DS '' MN1 ->
    exists mpath1 MN2 n,
      (MN1 =[ mpath1 ]=> MN2) /\ In n DS /\ alarm (MN2 n) = true.


Lemma oopsla_detect_soundness : forall (i0 : instr) N0,
  KIS (i0 N0) -> CorrectnessCriteria.detect_soundness N0 i0.

Proof.
  unfold CorrectnessCriteria.detect_soundness; intros.
  specialize KIS_detection_sound
    with (i0:=i0)(N0:=N0)(MN1:=MN1)(n:=n)(mpath:=path')
    as (mpath1 & MN2 & n'); attac.
Qed.

Lemma oopsla_detect_completeness : forall (i0 : instr) N0,
    KIC (i0 N0) -> CorrectnessCriteria.detect_completeness N0 i0.

Proof.
  unfold CorrectnessCriteria.detect_completeness; intros.
  specialize KIC_detection_complete
    with (i0:=i0)(N0:=N0)(MN1:=MN1)(mpath0:=path0')(DS:=DS)
    as (mpath1 & MN2 & n'); eauto.
Qed.

(** Finally, total correctness. *)

Lemma oopsla_correct : forall (i0 : instr) N0,
    KIC (i0 N0) -> KIS (i0 N0) -> CorrectnessCriteria.detect_correct N0 i0.

Proof.
  unfold CorrectnessCriteria.detect_correct; intros.
  repeat split;
    eauto using
      oopsla_transp_soundness,
      oopsla_transp_completeness,
      oopsla_detect_soundness,
      oopsla_detect_completeness.
Qed.

(** Assumptions are described in the introduction. In the final result, only
[Val], [some_val], [some_name] and [NetMod] are left declared. *)
Print Assumptions oopsla_correct.


(** * Appendix: A Coq Framework for Modelling Erlang/OTP-Style SRPC Networks *)

(** _Contents of this section are not addressed in the submission_ *)

(** Proving implementation of actual Erlang code is a daunting task. Instead, we
prove that the premises of our theory are sound and applicable by we providing a
Coq framework for modelling networks of SRPC services in the style of
[gen_server]s. Networks are assembled by assigning names (as strings) to
services. All services begin as [Ready] with empty input and output queues. The
network can start progressing via one or more _initiators_, which act as
external clients that send queries to the services. *)

Section Framework. 
  Import String.
  Open Scope string.

  (** Services are implemented through the [ServiceConf] record: the [state_t]
      field describes the type of internal state of the service (which can
      differ among services); [init] is the initial state; [handle_call]
      (following the convention from Erlang) describes how the service reacts to
      a query [msg] received [from] a certain sender while in a given [state].

      Initiators are anonymous and set [from] to [None]. For a regular service
      named [n] it is set to [Some n])

      The return type of [handle_call] is an opaque [Handler] which represents
      SRPC-compliant code of the handling function; to construct it, we provide
      the programmer with auxiliary syntax (discussed below). *)

  Print ServiceConf.

  (** [[
      Record ServiceConf : Type := sconf
      { state_t : Set;
        init : state_t;
        handle_call : option string -> Val -> state_t -> Handler state_t
      }.
      ]]
   *)

  (** The simplest SRPC service is [echo] defined below, which handles queries
      by immediately replying with the message it received. In [handle_call],
      the auxiliary syntax [reply msg state] allows for sending [msg] and using
      [state] as the next service state (which in case of [echo] is [tt :
      unit]). *)

  Goal GenServerNet.echo =
         {|state_t := unit;
           init := tt;
           handle_call from msg st :=
             reply msg st
         |}.
  Proof. reflexivity. Defined.

  (** The more complex service shown below defines [fwd_service], which acts as
      a proxy by forwarding messages to a [target]. Each message carries a
      natural number decremented at each forwarding; if [fwd_service] receives
      0, it instead instantly replies with the number of messages forwarded so
      far (tracked in the state). The example showcases the auxiliary syntax
      [let? x := target ! msg' in ]... to perform an RPC call: it sends the
      query [msg'] to the service [target], awaits a response, and assigns the
      response payload to the variable [x]. *)

  (** Note that the framework instantiates [Val] with [nat] *)
  Check valnat : Val = nat.

  Goal GenServerNet.fwd_service = fun (target : string) =>
      {|state_t := _;
        init := tt;
        handle_call (_from : option string) (msg : Val) st :=
          match valnat_trans msg with
          | 0 => reply msg st
          | S msg' =>
              let? x := target ! msg' in
              reply x st
          end
      |}.
  Proof. reflexivity. Defined.


  (** Initiators are specified by the [InitConf] record with two fields:
      [target] which names the service to be called; and [msg] for the message
      to be sent. Networks are assembled by the [gen_net] function based on the
      provided configuration ([NetConf]) which maps names to initiators and
      services. Note that initiator names are unrelated to service names, even
      if they share the same string value: internally, the framework represents
      them differently and makes it impossible to query an initiator. Because
      the mapping has to be exhaustive, we use [echo] as a default service and
      set superfluous initiators to call an unused name. *)

  Print InitConf.

  (** [[
      Record InitConf : Set := iconf
      { target : string;
        msg : Srpc.Locks.Proc.Que.Channel.Val
      }.
      ]]
   *)

  (** Network configuration: *)

  Check gen_net : NetConf -> Net.
  Print NetConf.

  (** [[
      Record NetConf :=
      { services : string -> ServiceConf;
        inits : string -> InitConf
      }.
      ]]
   *)

  (** All networks generated by [gen_net] contain only SRPC services. *)
  Check gen_net_SRPC : forall conf n,
    exists srpc, SrpcDefs.SRPC_serv srpc (NetMod.get n (gen_net conf)).

  (** Moreover, they are [well_formed] *)
  Check gen_well_formed : forall conf, well_formed (gen_net conf).

  (** We provide an instrumentation [gen_instr] which fulfills our [KIS] and
  [KIC] invariants. *)

  Check gen_instr : instr.
  Check gen_KIS : forall conf, KIS (gen_instr (gen_net conf)).
  Check gen_KIC : forall conf, KIC (gen_instr (gen_net conf)).

  (** Therefore, networks implemented in this framework can be correctly
  monitored. *)

  Lemma gen_net_correct : forall conf,
      CorrectnessCriteria.detect_correct (gen_net conf) gen_instr.
  Proof. eauto using oopsla_correct, gen_KIS, gen_KIC. Qed.

  (** ** Example network defined in the framework. *)
  Goal GenServerNet.example_net =
      gen_net
        {| services name :=
            match name with
            | "C" => fwd_service "B" | "D" => fwd_service "A"
            | "A" => fwd_service "C" | "B" => fwd_service "D"
            | _ => GenServerNet.echo
            end;
          inits name :=
            match name with
            | "iA" => iconf "A" 2 | "iB" => iconf "B" 2
            | _ => iconf "" 0
            end
        |}.
  Proof. reflexivity. Defined.

  (** It may deadlock! *)
  Check can_deadlock : exists path N,
      (example_net =[ path ]=> N) /\ dead_set ["A"; "B"; "C"; "D"]%list N.
End Framework.
