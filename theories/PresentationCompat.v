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

From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Structures.Equalities.
Import ListNotations.
Open Scope string_scope.

Module DetConf <: Compl.DETECT_CONF.
  Parameter Val : Set.

  Declare Module NAME : UsualDecidableSet.
  Module TAG := Locks.Tag_.

  Declare Module NetMod : Network.NET_MOD(NAME).

  Definition Msg := @Compl.MProbe' NAME.t'.
  Definition MState := @Compl.MState' NAME.t'.
End DetConf.

Module Import Theory := ModelData.Empty <+ Sound.SOUND(DetConf).
Import SrpcDefs.

Module Paper.
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
End Paper.


Fact serv_lock_eq : forall S n, AnySRPC_serv S -> serv_lock [n] S <-> Paper.serv_lock n S.
Proof.
  split; intros.
  - consider (serv_lock _ _).
    repeat split; repeat (intros ?); simpl in *.
    + bs (In (n, R, v) &I).
    + eauto using lock_SRPC_Locked with LTS.
  - destruct S.
    consider (Paper.serv_lock _ _).
    hsimpl in *.
    repeat split; repeat (intros ?); simpl in *; eauto with LTS.
    assert (exists v' E, Deq (n0, R) v' serv_i0 E) by eauto using In_Deq.
    hsimpl in *.
    bs.
Qed.


Fact deadset_eq : forall N DS, SRPC_net N -> dead_set DS N <-> Paper.dead_set DS N.

Proof.
  unfold Paper.dead_set.
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

Lemma SRPCI_measure : forall srpc P, srpc <> Ready -> Paper.SRPCI srpc P -> SRPC_measure P.
Proof.
  intros.
  induction H0; intros; constructor; eattac.
  specialize (H0 nc ltac:(attac)); attac.
  rewrite H4 in H1.
  attac.
Qed.

Lemma SRPCC_SRPCI : forall srpc P, Paper.SRPCC srpc P -> Paper.SRPCI srpc P.
  intros. kill H.
Qed.

Lemma SRPCC_measure : forall srpc P, srpc <> Ready -> Paper.SRPCC srpc P -> SRPC_measure P.
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


Fact SRPCB_eq : forall P c (srpc : SRPC_Busy_State c), SRPC_Busy srpc P <-> Paper.SRPCI (Busy srpc) P.

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
    induction H0; intros; consider (Paper.SRPCI _ _); attac.
    + constructor; attac.
    + constructor; attac.
    + constructor; attac.
    + constructor; eattac.
      * consider (n = (s, R)); attac.
      * kill H1.
        consider (n = (s, R)); attac.
Qed.

Fact SRPC_eq : forall P srpc, SRPC srpc P <-> Paper.SRPCC srpc P.

Proof.
  split; intros.
  - generalize dependent srpc P.
    ltac1:(cofix C).
    intros P srpc Hsrpc.
    destruct P > [| destruct n as [n [|]] | | ]; kill Hsrpc > [|kill HBusy].
    all: try (solve [clear C; specialize (HQueryAll some_name some_val); kill HQueryAll; bs]).
    all: try (solve [clear C; specialize (HReplyAll some_val); kill HReplyAll; bs]).
    + apply Paper.SRPCC_W; intros; eauto.
      econstructor.
      eapply SRPCB_eq.
      eapply HQuery0.
      attac.
    + eapply Paper.SRPCC_W; intros; eauto.
      eapply SRPCB_eq.
      econstructor; attac.
    + eapply Paper.SRPCC_R; intros.
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
    + eapply Paper.SRPCC_W; intros; eauto.
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
      assert (Paper.SRPCC (Working n) (cont v)). apply H with (v:=v). exists (n, Q), v, cont. attac.
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
