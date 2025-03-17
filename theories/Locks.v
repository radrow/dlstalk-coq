From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Std.

From Ltac2 Require Fresh.
From Ltac2 Require Import Control.
From Ltac2 Require Import Message.
From Ltac2 Require Import Std.
From Ltac2 Require Import Printf.

Import Ltac2.Notations.

Require Import DlStalk.LTS.
Require Import DlStalk.Model.
Require Import DlStalk.ModelData.
Require Import DlStalk.Network.
Require Import DlStalk.Tactics.
Require Import DlStalk.Que.
Require Import DlStalk.Lemmas.

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


Set Diffs "on".

Inductive Tag_ : Set := Q | R. (* this must be extracted or else coq bugs *)
Lemma Tag_neq_QR : Q <> R. attac. Qed.
Lemma Tag_neq_RQ : R <> Q. attac. Qed.
Hint Resolve Tag_neq_QR Tag_neq_RQ : core.

Module Tag_ <: UsualDecidableSet.
  Definition t' := Tag_.
  Definition t := Tag_.
  Definition eq := @eq t.

  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition eq_equiv := Build_Equivalence eq eq_refl eq_sym eq_trans.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof.
    intros x y.
    destruct x; destruct y; first [left; solve [eattac] | right; solve [eattac]].
  Defined.

  Definition eqb : t -> t -> bool.
    intros x y. destruct (eq_dec x y) > [apply true | apply false].
  Defined.

  Lemma eqb_eq : forall x y : t, eqb x y = true <-> eq x y.
  Proof.
    intros x y. split; intros H.
    - destruct x; destruct y; unfold eqb in H; try (bs); apply eq_refl.
    - destruct x; destruct y; unfold eqb; simpl; kill H.
  Qed.

  Lemma eqb_neq : forall x y : t, eqb x y = false <-> x <> y.
  Proof.
    intros x y. split; intros H.
    - destruct x; destruct y; unfold eqb in H; try (bs); apply eq_refl.
    - destruct x; destruct y; unfold eqb; simpl; try (bs); auto.
  Qed.
End Tag_.


Module Type LOCKS_CONF := PROC_CONF with Module TAG := Tag_.

Module Type LOCKS_PARAMS(Conf : LOCKS_CONF).
  Declare Module Export Proc : PROC(Conf) with Module TAG := Tag_.
End LOCKS_PARAMS.


Module MonNetTactics(Import Conf : LOCKS_CONF)(Import Params : LOCKS_PARAMS(Conf)).
  Ltac2 destruct_mna_ a :=
    first
      [destruct $a as [? [[[? [|]]|[? [|]]|]|[[? ?]|[? ?]|]|[[? ?]|[? ?]|]] | ? ? [|] [?|?]] (* Q/R tags *)
      |destruct $a as [? [[[? ?]|[? ?]|]|[[? ?]|[? ?]|]|[[? ?]|[? ?]|]] | ? ? ? [?|?]] (* Anon tags *)
      ]; doubt.

  Ltac2 Notation "destruct_mna" a(constr) := destruct_mna_ a.
End MonNetTactics.

Module Type LOCKS_F(Import Conf : LOCKS_CONF)(Import Params : LOCKS_PARAMS(Conf)).

  (** We need to assume that there are _some_ names and values... *)
  Parameter some_name : Name.
  Parameter some_val : Val.

  Notation Names := (list Name).


  (** A "decisive" process always filters one tag *)
  CoInductive Decisive : Proc -> Prop :=
  | DecRecv [handle]
      (** If it accepts a Q for any name, it must not accept any R; and it must proceeed as decisive *)
      (HDecQ : (forall n P, handle (n, Q) = Some P -> (forall m, handle (m, R) = None) /\ (forall v,  Decisive (P v))))
      (** If it accepts an R for any name, it must not accept any Q; and it must proceeed as decisive *)
      (HDecR : (forall n P, handle (n, R) = Some P -> (forall m, handle (m, Q) = None) /\ (forall v,  Decisive (P v))))
    : Decisive (PRecv handle)
  | DecSend [n v P] :
    Decisive P ->
    Decisive (PSend n v P)
  | DecTau [P] :
    Decisive P ->
    Decisive (STau P)
  .

  #[export] Hint Constructors Decisive : LTS.

  (** Service decisiveness *)
  Definition Decisive_serv (S : Serv) := Decisive (serv_p S).

  #[export] Hint Transparent Decisive_serv : LTS.


  (** Process is locked on L when it's waiting for a Reply from some n in L *)
  Definition proc_lock (L : Names) (P : Proc) :=
    match P with
    | PRecv handle => forall n,
        (List.In n L <-> handle (n, R) <> None)
        /\ handle (n, Q) = None
    | _ => False
    end.

  #[export] Hint Transparent proc_lock : LTS.


  (** Service is locked when: *)

(*         - its process is locked and; *)
(*         - there is no acceptable reply in the inbox and; *)
(*         - there are no sends scheduled *)

(*         We also consider only decisive processes here. *)
(*    *)
  Inductive serv_lock (L : Names) : Serv -> Prop :=
  | PQ_Locked [I P] :
    Decisive P ->
    proc_lock L P ->
    (forall n v, List.In n L -> not (List.In (n, R, v) I)) ->
    serv_lock L (serv I P []).

  #[export] Hint Constructors serv_lock : LTS.


  Section Examples.
    CoFixpoint echo : Proc :=
          PRecv (
              fun m =>
                let (c, t) := m in
                match t with
                | R => None
                | Q => Some (fun v => PSend (c, R) v echo)
                end
            ).

    Local Example ex_Decisive_echo : Decisive echo.
    ltac1:(cofix C).
    unfold echo.
    rewrite unfold_Proc.
    apply DecRecv; intros.
    - kill H.
      split; auto.
      intros.
      constructor.
      Guarded.
      assumption.
    - split; try (bs).
    Qed.
  End Examples.

  Lemma Decisive_serv_inv I P O : Decisive_serv (serv I P O) <-> Decisive P.
  Proof. split; intros; eattac. Qed.

  #[export] Hint Rewrite -> Decisive_serv_inv using assumption : LTS LTS_concl.
  #[export] Hint Resolve <- Decisive_serv_inv : LTS.
  #[export] Hint Immediate Decisive_serv_inv : LTS.


  (** Decisiveness is invariantd under transitions *)
  Fact Decisive_invariant : trans_invariant Decisive always.

  Proof with attac.
    repeat (intros ?).
    consider (_ =(_)=> _); attac.
    consider (Decisive _).
    destruct n as [n [|]]; eassert (_ /\ forall v, Decisive (P v)); eauto.
    all: eattac.
  Qed.

  #[export] Hint Resolve Decisive_invariant : LTS inv.


  Lemma prop_transport_l_Decisive :
    prop_transport_l Decisive_serv Decisive (fun S => match S with serv _ P _ => P end).

  Proof.
    unfold prop_transport_l.
    intros.
    destruct N0; subst.
    eauto with LTS.
  Qed.


  Lemma prop_transport_r_Decisive :
    prop_transport_r Decisive_serv Decisive (fun S => match S with serv _ P _ => P end).

  Proof.
    unfold prop_transport_r.
    intros.
    destruct N0; subst.
    eauto with LTS.
  Qed.

  #[export] Hint Resolve prop_transport_l_Decisive : inv.
  #[export] Hint Resolve prop_transport_r_Decisive : inv.


  (** Decisiveness is invariantd under transitions (service version) *)
  Fact Decisive_serv_invariant : trans_invariant Decisive_serv always.

  Proof with eattac.
    unfold trans_invariant.
    intros.
    kill H; eattac.
  Qed.

  #[export] Hint Resolve Decisive_serv_invariant : LTS inv.


  (** Unlocking message is a reply with sender in the lockset *)
  Definition unlocking_msg (L : Names) (a : PAct) :=
    match a with
    | Recv (n, R) _ => List.In n L
    | _ => False
    end.

  #[export] Hint Transparent unlocking_msg : LTS.


  Lemma unlocking_msg_inv L a :
    unlocking_msg L a <-> exists n v, a = Recv (n, R) v /\ List.In n L.
  Proof. destruct a; split; eattac. destruct n as [? [|]]; attac. Qed.

  #[export] Hint Rewrite -> unlocking_msg_inv using assumption : LTS.


  (** Not-unlocking message is a message that is not really unlocking, makes sense bro? *)
  Definition not_unlocking_msg (L : Names) (a : PAct) :=
    not (unlocking_msg L a).

  #[export] Hint Transparent not_unlocking_msg : LTS.


  Lemma mk_proc_lock [L P handle] :
    P = PRecv handle ->
    (forall n, List.In n L -> handle (n, R) <> None) ->
    (forall n P', handle (n, R) = Some P' -> List.In n L) ->
    (forall n, handle (n, Q) = None) ->
    proc_lock L P.
  Proof. unfold proc_lock. destruct P; attac. destruct (&handle (n, R)) eqn:?; eattac. Qed.

  #[export] Hint Resolve mk_proc_lock | 20 : LTS.

  Lemma proc_lock_STau_inv L P : proc_lock L (STau P) <-> False.
  Proof. unfold proc_lock. attac. Qed.

  Lemma proc_lock_PSend_inv L nc v P : proc_lock L (PSend nc v P) <-> False.
  Proof. unfold proc_lock. attac. Qed.

  #[export] Hint Rewrite -> proc_lock_STau_inv proc_lock_PSend_inv using spank : LTS LTS_concl.


  (** Lockeded process can only receive from its lock set *)
  Theorem proc_lock_recv [L P a P'] :
    proc_lock L P ->
    (P =(a)=> P') ->
    unlocking_msg L a.

  Proof with attac.
    intros.
    destruct P...
    consider (PRecv _ =(a)=> _).
    destruct n as [n t].
    consider ((In n L <-> handle (n, R) <> None) /\ handle (n, Q) = None).
    destruct `(Tag).
    - cbv in *; bs.
    - enough (handle (n, R) <> None) by eattac.
      cbv in *; bs.
  Qed.

  #[export] Hint Resolve proc_lock_recv : LTS.


  Lemma proc_lock_recv_inv [L P a P'] :
    proc_lock L P ->
    (P =(a)=> P') <->
      exists handle cont n v,
        P = PRecv handle
        /\ handle (n, R) = Some cont
        /\ P' = cont v
        /\ a = Recv (n, R) v
        /\ List.In n L.
  Proof. attac. assert (unlocking_msg L a); eattac. Qed.

  #[export] Hint Rewrite -> @proc_lock_recv_inv using spank : LTS.


  Lemma serv_lock_P_inv [L I P O] :
    serv_lock L (serv I P O) -> proc_lock L P.
  Proof. intros H; kill H. Qed.

  Lemma serv_lock_O_inv [L I P O] :
    serv_lock L (serv I P O) -> O = [].
  Proof. intros H; kill H. Qed.

  Lemma serv_lock_I_inv [L I P O n v] :
    serv_lock L (serv I P O) -> List.In n L -> ~ List.In (n, R, v) I.
  Proof. intros; kill H. attac. Qed.

  #[export] Hint Resolve serv_lock_P_inv serv_lock_I_inv serv_lock_O_inv : LTS.


  (** Extraction of decisiveness from the lock property (it's guaranteed trivially) *)
  Fact serv_lock_Decisive L S : serv_lock L S -> Decisive_serv S.

  Proof with attac.
    intros.
    kill H...
  Qed.

  #[export] Hint Immediate serv_lock_Decisive : LTS.


  (** If a decisive processes accepts queries, then it does not accept replies *)
  Lemma Decisive_Q [n handle] :
    Decisive (PRecv handle) ->
    handle (n, Q) <> None ->
    forall m, handle (m, R) = None.

  Proof.
    intros.
    kill H.
    destruct (&handle (n, Q)) eqn:HEq; try (bs).
    apply HDecQ in HEq.
    apply HEq.
  Qed.


  (** If a decisive processes accepts replies, then it does not accept queries *)
  Lemma Decisive_R [n handle] :
    Decisive (PRecv handle) ->
    handle (n, R) <> None ->
    forall m, handle (m, Q) = None.

  Proof.
    intros.
    kill H.
    destruct (&handle (n, R)) eqn:HEq; try (bs).
    apply HDecR in HEq.
    apply HEq.
  Qed.


  (** If a decisive processes accepts queries, then it does not accept replies *)
  Lemma Decisive_Q_e [m handle] :
    Decisive (PRecv handle) ->
    (exists n, handle (n, Q) <> None) ->
    handle (m, R) = None.

  Proof.
    intros.
    kill H. hsimpl in *.
    destruct (&handle (n, Q)) eqn:HEq; try (bs).
    apply HDecQ in HEq.
    apply HEq.
  Qed.


  (** If a decisive processes accepts replies, then it does not accept queries *)
  Lemma Decisive_R_e [m handle] :
    Decisive (PRecv handle) ->
    (exists n, handle (n, R) <> None) ->
    handle (m, Q) = None.

  Proof.
    intros.
    kill H. hsimpl in *.
    destruct (&handle (n, R)) eqn:HEq; try (bs).
    apply HDecR in HEq.
    apply HEq.
  Qed.

  #[export] Hint Rewrite -> @Decisive_Q_e @Decisive_R_e using solve [eauto 2|congruence] : LTS LTS_concl.


  (** Special case of [Decisive_Q] when [n = m] *)
  Corollary Decisive_Q' [n handle] :
    Decisive (PRecv handle) ->
    handle (n, Q) <> None ->
    handle (n, R) = None.

  Proof. attac. Qed.


  (** Special case of [Decisive_R] when [n = m] *)
  Corollary Decisive_R' [n handle] :
    Decisive (PRecv handle) ->
    handle (n, R) <> None ->
    handle (n, Q) = None.

  Proof. attac. Qed.


  (** Non-unlocking messages invariant process lock *)
  Proposition proc_lock_invariant L :
    trans_invariant (proc_lock L) (not_unlocking_msg L).

  Proof with eattac.
    unfold proc_lock.
    unfold trans_invariant.
    intros N0 N1 a T HL0 Ha.
    destruct N0; try (bs).
    unfold not_unlocking_msg in Ha. unfold unlocking_msg in Ha.
    kill T.
    destruct n.
    destruct (HL0 n).
    destruct t.
    - cbv in *; bs.
    - assert (handle (n, R) <> None).
      {
        unfold not. intros.
        cbv in *; bs.
      }
      absurd (Some P = None)...
  Qed.

  #[export] Hint Resolve proc_lock_invariant : LTS inv.


  (** Lockeded services only receive *)
  Proposition serv_lock_recv [L a S0 S1] :
    serv_lock L S0 ->
    (S0 =(a)=> S1) ->
    match a with Recv _ _ => True | _ => False end.

  Proof with attac.
    intros HL0 T.

    kill HL0.
    rename H into HD.
    rename H0 into HL.
    rename H1 into HUnl.

    destruct P; try (bs).

    kill T...
    bs (In (n0, R, v0) &I).
  Qed.


  Lemma serv_lock_recv_inv [L a S0 S1] :
    serv_lock L S0 ->
    (S0 =(a)=> S1) <->
      exists I P O nc v,
        S0 = serv I P O
        /\ S1 = serv (I ++ [(nc, v)]) P O
        /\ a = Recv nc v.
  Proof. attac. specialize (serv_lock_recv H H0) as ?. destruct a; eattac. Qed.

  #[export] Hint Rewrite -> serv_lock_recv_inv using spank : LTS.


  (** Non-unlocking messages invariant service lock *)
  Proposition serv_lock_invariant [L] :
    trans_invariant (serv_lock L) (not_unlocking_msg L).

  Proof with eattac.
    intros S0 S1 a T HL0 Ha.

    specialize (serv_lock_recv HL0 T) as H.

    kill HL0.
    kill T; try (bs).
    attac.

    unfold not; intros.
    hsimpl in *.
    absurd (List.In (n0, R, v0) &I); attac.
    hsimpl in *.
    consider (List.In (n0, R, v0) &I \/ List.In _ [(n, v)]) by auto using in_app_or with LTS.
    destruct `(_ \/ _); attac.
  Qed.

  #[export] Hint Resolve serv_lock_invariant : LTS inv.


  (** Locked sets are equivalent *)
  Lemma proc_lock_incl [P L0 L1] :
    proc_lock L0 P ->
    proc_lock L1 P ->
    incl L0 L1.

  Proof.
    unfold proc_lock.
    intros HL0 HL1.

    destruct P; try (bs).

    unfold incl.
    intros n HIn.

    apply HL0 in HIn.
    apply HL1 in HIn.
    assumption.
  Qed.

  #[export] Hint Resolve proc_lock_incl : LTS.


  (** Locked sets are *actually* equivalent *)
  Lemma proc_lock_equiv [P L0 L1] :
    proc_lock L0 P ->
    proc_lock L1 P ->
    incl L0 L1 /\ incl L1 L0.

  Proof.
    intros HL0 HL1.
    split; eapply proc_lock_incl; eauto.
  Qed.


  (** If you are locked on a set, then you are locked on all equivalent ones *)
  Lemma proc_lock_equiv_inv [P L0 L1] :
    proc_lock L0 P ->
    incl L0 L1 ->
    incl L1 L0 ->
    proc_lock L1 P.

  Proof.
    unfold proc_lock.
    intros HL HIncl0 HIncl1.

    destruct P; try (bs).

    intro n.
    specialize (HL n) as [Hh HNeq].
    split; auto.

    split; intros.
    - apply Hh.
      auto with datatypes.
    - apply Hh in H.
      auto with datatypes.
  Qed.

  #[export] Hint Immediate proc_lock_equiv_inv : LTS.


  (** Locked sets are equivalent *)
  Lemma serv_lock_incl [S L0 L1] :
    serv_lock L0 S ->
    serv_lock L1 S ->
    incl L0 L1.

  Proof.
    intros HL0 HL1.

    destruct S as [I P O].

    kill HL0.
    kill HL1.
    eapply proc_lock_incl; eauto.
  Qed.

  #[export] Hint Resolve serv_lock_incl : LTS.


  (** Locked sets are *actually* equivalent *)
  Lemma serv_lock_equiv [S L0 L1] :
    serv_lock L0 S ->
    serv_lock L1 S ->
    incl L0 L1 /\ incl L1 L0.

  Proof.
    intros HL0 HL1.

    destruct S as [I P O].

    kill HL0.
    kill HL1.
    eapply proc_lock_equiv; eauto.
  Qed.


  (** If you are locked on a set, then you are locked on all equivalent ones *)
  Lemma serv_lock_equiv_inv [S L0 L1] :
    serv_lock L0 S ->
    incl L0 L1 ->
    incl L1 L0 ->
    serv_lock L1 S.

  Proof.
    intros HL HIncl0 HIncl1.

    destruct S as [I P O].
    kill HL.

    constructor; eauto.
    eapply proc_lock_equiv_inv; eauto.
  Qed.

  #[export] Hint Immediate serv_lock_equiv_inv : LTS.


  Lemma proc_lock_nodup [L P] :
    proc_lock L P ->
    proc_lock (nodup NAME.eq_dec L) P.

  Proof.
    intros.
    assert (incl (nodup NAME.eq_dec L) L) by (intros ?; attac; eapply nodup_In; eauto).
    assert (incl L (nodup NAME.eq_dec L)) by (intros ?; attac; eapply nodup_In; eauto).
    eauto using proc_lock_equiv_inv.
  Qed.

  Lemma serv_lock_nodup [L S] :
    serv_lock L S ->
    serv_lock (nodup NAME.eq_dec L) S.

  Proof.
    intros.
    destruct S as [I P O].
    consider (serv_lock _ _).
    constructor.
    - auto.
    - auto using proc_lock_nodup.
    - intros.
      enough (In n L) by auto.
      eapply nodup_In; eauto.
  Qed.

  Lemma serv_tau_no_lock_l [S0 S1 L] :
    (S0 =(Tau)=> S1) ->
    ~ serv_lock L S0.

  Proof.
    intros; intros ?.
    consider (_ =(_)=> _).
  Qed.

  Lemma serv_send_no_lock_l [S0 S1 nc v L] :
    (S0 =(Send nc v)=> S1) ->
    ~ serv_lock L S0.

  Proof.
    intros; intros ?.
    consider (_ =(_)=> _).
  Qed.


  Lemma serv_recv_R_bad_sender_derive_lock [S0 S1 n v L] :
    ~ In n L ->
    serv_lock L S1 ->
    (S0 =(Recv (n, R) v)=> S1) ->
    serv_lock L S0.

  Proof.
    intros.
    consider (_ =(_)=> _); simpl in *.
    consider (serv_lock _ _).

    eattac.
    bs (~ In (n0, R, v0) (I0 ++ [(n, R, v)])).
  Qed.

  Lemma serv_recv_no_new_lock [S0 S1 nc v L] :
    ~ serv_lock L S0 ->
    (S0 =(Recv nc v)=> S1) ->
    ~ serv_lock L S1.

  Proof.
    intros; intros ?.
    apply `(~ serv_lock _ _).
    consider (_ =(_)=> _); simpl in *.
    consider (serv_lock _ _).
    eattac.
    bs (~ In (n, R, v0) (I0 ++ [(nc, v)])).
  Qed.

  Lemma serv_recv_Q_derive_lock [S0 S1 n v L] :
    serv_lock L S1 ->
    (S0 =(Recv (n, Q) v)=> S1) ->
    serv_lock L S0.

  Proof.
    intros.
    consider (_ =(_)=> _); simpl in *.
    consider (serv_lock _ _).
    eattac.
    bs (~ In (n0, R, v0) (I0 ++ [(n, Q, v)])).
  Qed.
End LOCKS_F.

Module Type LOCKS(Conf : LOCKS_CONF) := Conf <+ LOCKS_PARAMS <+ LOCKS_F.

