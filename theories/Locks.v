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

Inductive Tag_ := Q | R. (* this must be extracted or else coq bugs https://github.com/coq/coq/issues/19994 *)
Lemma Tag_neq_QR : Q <> R. attac. Qed.
Lemma Tag_neq_RQ : R <> Q. attac. Qed.
Hint Resolve Tag_neq_QR Tag_neq_RQ : core.

Module Tag <: UsualDecidableSet.
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
    - destruct x; destruct y; unfold eqb in H; try (bullshit); apply eq_refl.
    - destruct x; destruct y; unfold eqb; simpl; kill H.
  Qed.

  Lemma eqb_neq : forall x y : t, eqb x y = false <-> x <> y.
  Proof.
    intros x y. split; intros H.
    - destruct x; destruct y; unfold eqb in H; try (bullshit); apply eq_refl.
    - destruct x; destruct y; unfold eqb; simpl; try (bullshit); auto.
  Qed.
End Tag.


Module Type PROC_DATA_LOCKS :=
  PROC_DATA
  with Module TAG := Tag.

Module Type PROC_FOR_LOCKS := PROC_DATA_LOCKS <+ QUE <+ PROC.


Module Type LOCKS(Import Proc : PROC_FOR_LOCKS).

(*   Module MD <: MODEL_DATA. *)
(*     Module NAME := Name. *)
(*     Module TAG := Tag. *)

(*     Record MProbe : Set := {init : NAME.t'; index : nat}. *)

(*     Record MState' := *)
(*       { self : NAME.t' *)
(*       ; lock_id : nat *)
(*       ; lock : option NAME.t' *)
(*       ; waitees : list NAME.t' *)
(*       ; deadlock : bool *)
(*       }. *)

(*     Definition Val := Val. *)
(*     Definition MState := MState'. *)
(*     Definition Msg := MProbe. *)
(*   End MD. *)
(* End LOCKS. *)

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
    Decisive (PTau P)
  .

  #[export] Hint Constructors Decisive : LTS.

  (** Service decisiveness *)
  Definition Decisive_q (S : PQued) := Decisive (pq_P S).

  #[export] Hint Transparent Decisive_q : LTS.


  (** Process is locked on L when it's waiting for a Reply from some n in L *)
  Definition proc_lock (L : Names) (P : Proc) :=
    match P with
    | PRecv handle => forall n,
        (List.In n L <-> handle (n, R) <> None)
        /\ handle (n, Q) = None
    | _ => False
    end.

  #[export] Hint Transparent proc_lock : LTS.


  (** Service is locked when:

        - its process is locked and;
        - there is no acceptable reply in the inbox and;
        - there are no sends scheduled

        We also consider only decisive processes here.
   *)
  Inductive pq_lock (L : Names) : PQued -> Prop :=
  | PQ_Lock [I P] :
    Decisive P ->
    proc_lock L P ->
    (forall n v, List.In n L -> not (List.In (n, R, v) I)) ->
    pq_lock L (pq I P []).

  #[export] Hint Constructors pq_lock : LTS.


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
    - split; try (bullshit).
    Qed.
  End Examples.

  Lemma Decisive_q_inv I P O : Decisive_q (pq I P O) <-> Decisive P.
  Proof. split; intros; eattac. Qed.

  #[export] Hint Rewrite -> Decisive_q_inv using assumption : LTS LTS_concl.
  #[export] Hint Resolve <- Decisive_q_inv : LTS.
  #[export] Hint Immediate Decisive_q_inv : LTS.


  (** Decisiveness is invariantd under transitions *)
  Fact trans_invariant_Decisive : trans_invariant Decisive always.

  Proof with attac.
    attac.
    consider (_ =(_)=> _); attac.
    consider (Decisive _).
    destruct n as [n [|]]; eassert (_ /\ forall v, Decisive (P v)); eauto.
    all: eattac.
  Qed.

  #[export] Hint Resolve trans_invariant_Decisive : LTS inv.


  Lemma prop_transport_l_Decisive :
    prop_transport_l Decisive_q Decisive (fun S => match S with pq _ P _ => P end).

  Proof.
    unfold prop_transport_l.
    intros.
    destruct N0; subst.
    eauto with LTS.
  Qed.


  Lemma prop_transport_r_Decisive :
    prop_transport_r Decisive_q Decisive (fun S => match S with pq _ P _ => P end).

  Proof.
    unfold prop_transport_r.
    intros.
    destruct N0; subst.
    eauto with LTS.
  Qed.

  #[export] Hint Resolve prop_transport_l_Decisive : inv.
  #[export] Hint Resolve prop_transport_r_Decisive : inv.


  (** Decisiveness is invariantd under transitions (service version) *)
  Fact trans_invariant_Decisive_q : trans_invariant Decisive_q always.

  Proof with eattac.
    unfold trans_invariant.
    intros.
    kill H; eattac.
  Qed.

  #[export] Hint Resolve trans_invariant_Decisive_q : LTS inv.


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

  Lemma proc_lock_PTau_inv L P : proc_lock L (PTau P) <-> False.
  Proof. unfold proc_lock. attac. Qed.

  Lemma proc_lock_PSend_inv L nc v P : proc_lock L (PSend nc v P) <-> False.
  Proof. unfold proc_lock. attac. Qed.

  #[export] Hint Rewrite -> proc_lock_PTau_inv proc_lock_PSend_inv using spank : LTS LTS_concl.


  (** Locked process can only receive from its lock set *)
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
    - cbv in *; bullshit.
    - enough (handle (n, R) <> None) by eattac.
      cbv in *; bullshit.
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


  Lemma pq_lock_P_inv [L I P O] :
    pq_lock L (pq I P O) -> proc_lock L P.
  Proof. intros H; kill H. Qed.

  Lemma pq_lock_O_inv [L I P O] :
    pq_lock L (pq I P O) -> O = [].
  Proof. intros H; kill H. Qed.

  Lemma pq_lock_I_inv [L I P O n v] :
    pq_lock L (pq I P O) -> List.In n L -> ~ List.In (n, R, v) I.
  Proof. intros; kill H. attac. Qed.

  #[export] Hint Resolve pq_lock_P_inv pq_lock_I_inv pq_lock_O_inv : LTS.


  (** Extraction of decisiveness from the lock property (it's guaranteed trivially) *)
  Fact pq_lock_Decisive L S : pq_lock L S -> Decisive_q S.

  Proof with attac.
    intros.
    kill H...
  Qed.

  #[export] Hint Immediate pq_lock_Decisive : LTS.


  (** If a decisive processes accepts queries, then it does not accept replies *)
  Lemma Decisive_Q [n handle] :
    Decisive (PRecv handle) ->
    handle (n, Q) <> None ->
    forall m, handle (m, R) = None.

  Proof.
    intros.
    kill H.
    destruct (&handle (n, Q)) eqn:HEq; try (bullshit).
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
    destruct (&handle (n, R)) eqn:HEq; try (bullshit).
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
    destruct (&handle (n, Q)) eqn:HEq; try (bullshit).
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
    destruct (&handle (n, R)) eqn:HEq; try (bullshit).
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
    destruct N0; try (bullshit).
    unfold not_unlocking_msg in Ha. unfold unlocking_msg in Ha.
    kill T.
    destruct n.
    destruct (HL0 n).
    destruct t.
    - cbv in *; bullshit.
    - assert (handle (n, R) <> None).
      {
        unfold not. intros.
        cbv in *; bullshit.
      }
      absurd (Some P = None)...
  Qed.

  #[export] Hint Resolve proc_lock_invariant : LTS inv.


  (** Locked services only receive *)
  Proposition pq_lock_recv [L a S0 S1] :
    pq_lock L S0 ->
    (S0 =(a)=> S1) ->
    match a with Recv _ _ => True | _ => False end.

  Proof with attac.
    intros HL0 T.

    kill HL0.
    rename H into HD.
    rename H0 into HL.
    rename H1 into HUnl.

    destruct P; try (bullshit).

    kill T...
  Qed.


  Lemma pq_lock_recv_inv [L a S0 S1] :
    pq_lock L S0 ->
    (S0 =(a)=> S1) <->
      exists I P O nc v,
        S0 = pq I P O
        /\ S1 = pq (I ++ [(nc, v)]) P O
        /\ a = Recv nc v.
  Proof. attac. specialize (pq_lock_recv H H0) as ?. destruct a; eattac. Qed.

  #[export] Hint Rewrite -> pq_lock_recv_inv using spank : LTS.


  (** Non-unlocking messages invariant service lock *)
  Proposition pq_lock_invariant [L] :
    trans_invariant (pq_lock L) (not_unlocking_msg L).

  Proof with eattac.
    intros S0 S1 a T HL0 Ha.

    specialize (pq_lock_recv HL0 T) as H.

    kill HL0.
    kill T; try (bullshit).
    attac.

    unfold not; intros.
    hsimpl in *.
    absurd (List.In (n0, R, v0) &I); attac.
    hsimpl in *.
    consider (List.In (n0, R, v0) &I \/ List.In _ [(n, v)]) by auto using in_app_or with LTS.
    destruct `(_ \/ _); attac.
  Qed.

  #[export] Hint Resolve pq_lock_invariant : LTS inv.


  (** Lock sets are equivalent *)
  Lemma proc_lock_incl [P L0 L1] :
    proc_lock L0 P ->
    proc_lock L1 P ->
    incl L0 L1.

  Proof.
    unfold proc_lock.
    intros HL0 HL1.

    destruct P; try (bullshit).

    unfold incl.
    intros n HIn.

    apply HL0 in HIn.
    apply HL1 in HIn.
    assumption.
  Qed.

  #[export] Hint Resolve proc_lock_incl : LTS.


  (** Lock sets are *actually* equivalent *)
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

    destruct P; try (bullshit).

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


  (** Lock sets are equivalent *)
  Lemma pq_lock_incl [S L0 L1] :
    pq_lock L0 S ->
    pq_lock L1 S ->
    incl L0 L1.

  Proof.
    intros HL0 HL1.

    destruct S as [I P O].

    kill HL0.
    kill HL1.
    eapply proc_lock_incl; eauto.
  Qed.

  #[export] Hint Resolve pq_lock_incl : LTS.


  (** Lock sets are *actually* equivalent *)
  Lemma pq_lock_equiv [S L0 L1] :
    pq_lock L0 S ->
    pq_lock L1 S ->
    incl L0 L1 /\ incl L1 L0.

  Proof.
    intros HL0 HL1.

    destruct S as [I P O].

    kill HL0.
    kill HL1.
    eapply proc_lock_equiv; eauto.
  Qed.


  (** If you are locked on a set, then you are locked on all equivalent ones *)
  Lemma pq_lock_equiv_inv [S L0 L1] :
    pq_lock L0 S ->
    incl L0 L1 ->
    incl L1 L0 ->
    pq_lock L1 S.

  Proof.
    intros HL HIncl0 HIncl1.

    destruct S as [I P O].
    kill HL.

    constructor; eauto.
    eapply proc_lock_equiv_inv; eauto.
  Qed.

  #[export] Hint Immediate pq_lock_equiv_inv : LTS.


  Lemma proc_lock_nodup [L P] :
    proc_lock L P ->
    proc_lock (nodup NAME.eq_dec L) P.

  Proof.
    intros.
    assert (incl (nodup NAME.eq_dec L) L) by (attac; eapply nodup_In; eauto).
    assert (incl L (nodup NAME.eq_dec L)) by (attac; eapply nodup_In; eauto).
    eauto using proc_lock_equiv_inv.
  Qed.

  Lemma pq_lock_nodup [L S] :
    pq_lock L S ->
    pq_lock (nodup NAME.eq_dec L) S.

  Proof.
    intros.
    destruct S as [I P O].
    consider (pq_lock _ _).
    constructor.
    - auto.
    - auto using proc_lock_nodup.
    - intros.
      enough (In n L) by auto.
      eapply nodup_In; eauto.
  Qed.

  Lemma pq_tau_no_lock_l [S0 S1 L] :
    (S0 =(Tau)=> S1) ->
    ~ pq_lock L S0.

  Proof.
    intros; intros ?.
    consider (_ =(_)=> _).
  Qed.

  Lemma pq_send_no_lock_l [S0 S1 nc v L] :
    (S0 =(Send nc v)=> S1) ->
    ~ pq_lock L S0.

  Proof.
    intros; intros ?.
    consider (_ =(_)=> _).
  Qed.


  Lemma pq_recv_R_bad_sender_derive_lock [S0 S1 n v L] :
    ~ In n L ->
    pq_lock L S1 ->
    (S0 =(Recv (n, R) v)=> S1) ->
    pq_lock L S0.

  Proof.
    intros.
    consider (_ =(_)=> _); simpl in *.
    consider (pq_lock _ _).
    eattac.
  Qed.

  Lemma pq_recv_no_new_lock [S0 S1 nc v L] :
    ~ pq_lock L S0 ->
    (S0 =(Recv nc v)=> S1) ->
    ~ pq_lock L S1.

  Proof.
    intros; intros ?.
    apply `(~ pq_lock _ _).
    consider (_ =(_)=> _); simpl in *.
    consider (pq_lock _ _).
    eattac.
  Qed.

  Lemma pq_recv_Q_derive_lock [S0 S1 n v L] :
    pq_lock L S1 ->
    (S0 =(Recv (n, Q) v)=> S1) ->
    pq_lock L S0.

  Proof.
    intros.
    consider (_ =(_)=> _); simpl in *.
    consider (pq_lock _ _).
    eattac.
  Qed.
End LOCKS.


Module Type LOCKS_INST := PROC_FOR_LOCKS <+ LOCKS.

(* Module Type NET_LOCKS_PARAMS. *)
(*   Declare Module Locks : LOCKS_INST. *)
(*   Declare Module Net : NET_WITH(Locks). *)
(*   Export Locks. *)
(* End NET_LOCKS_PARAMS. *)

Module Type NET_LOCKS(Import Locks : LOCKS_INST)(Import Net : NET_WITH(Locks)).
  Notation PNet := (NetMod.t PQued).

  (** Network is decisive when all services are *)
  Definition Decisive_net N := forall n, Decisive_q (NetMod.get n N).

  Lemma Decisive_lookup [N n I P O] :
    Decisive_net N ->
    NetMod.get n N = pq I P O ->
    Decisive P.
  Proof. intros. specialize (H n). rewrite H0 in *. auto. Qed.

  Lemma Decisive_pq_lookup [N n S] :
    Decisive_net N ->
    NetMod.get n N = S ->
    Decisive_q S.
  Proof. intros. specialize (H n). rewrite H0 in *. auto. Qed.

    #[export] Hint Resolve Decisive_lookup : LTS.  (* pq variant seems redundant *)


    (** Decisive network remains decisive *)
    Lemma Decisive_net_invariant :
      @trans_invariant _ _ (@trans_net _ _ _ trans_pqued) Decisive_net always.

    Proof with attac.
      unfold Decisive_net.
      intros N0 N1 a T HD _ n.
      kill T; subst.
      - kill H0.
        smash_eq n n0; eattac.
      - hsimpl in *.

        smash_eq_on n n0 n'; eattac.
    Qed.

    #[export] Hint Resolve Decisive_net_invariant : LTS inv.


    (** Process locked in a network; referred by name *)
    Definition net_lock N L n := pq_lock L (NetMod.get n N).

    #[export] Hint Transparent net_lock : LTS.
    #[export] Hint Unfold net_lock : LTS.


    (** Relation of n being locked on m in a network *)
    Definition net_lock_on N n m :=
      exists L, List.In m L /\ net_lock N L n.

    #[export] Hint Transparent net_lock_on : LTS.


    (** Lock sets are equivalent  *)
    Lemma net_lock_equiv [N L0 L1 n] :
      net_lock N L0 n ->
      net_lock N L1 n ->
      incl L0 L1 /\ incl L1 L0.

    Proof with eattac.
      intros HL0 HL1.
      unfold net_lock in *.
      eapply pq_lock_equiv; eauto.
    Qed.

    #[export] Hint Resolve net_lock_equiv : LTS.


    Lemma net_lock_inv_I n n' v N L I P O :
      NetMod.get n N = pq I P O ->
      List.In n' L ->
      net_lock N L n ->
      ~ List.In (n', R, v) I.
    Proof. intros. kill H1. attac. Qed.

    Lemma net_lock_inv_P n N L I P O :
      NetMod.get n N = pq I P O ->
      net_lock N L n ->
      proc_lock L P.
    Proof. intros. kill H0. Qed.

    Lemma net_lock_inv_P_Decisive n N L I P O :
      NetMod.get n N = pq I P O ->
      net_lock N L n ->
      Decisive P.
    Proof. intros. kill H0. Qed.

    Lemma net_lock_inv_O n N L I P O :
      NetMod.get n N = pq I P O ->
      net_lock N L n -> O = [].

    Proof. intros. kill H0. Qed.

    #[export] Hint Resolve net_lock_inv_I net_lock_inv_P net_lock_inv_P_Decisive net_lock_inv_O : LTS.


    Lemma net_lock_on_in [N L n0 n1] :
      net_lock N L n0 ->
      net_lock_on N n0 n1 ->
      List.In n1 L.

    Proof.
      intros HL HL0.
      destruct HL0 as [L0 [HIn HL0]].
      destruct (net_lock_equiv HL HL0); attac.
    Qed.

    #[export] Hint Resolve net_lock_on_in : LTS.


    Fact net_lock_move_eq L n N0 N1 :
      NetMod.get n N0 = NetMod.get n N1 ->
      net_lock N0 L n <-> net_lock N1 L n.

    Proof.
      unfold net_lock.
      intros.
      split; attac.
    Qed.


    Fact net_lock_on_move_eq n0 n1 N0 N1 :
      NetMod.get n0 N0 = NetMod.get n0 N1 ->
      net_lock_on N0 n0 n1 <-> net_lock_on N1 n0 n1.
    Proof.
      unfold net_lock_on, net_lock.
      split; intros; hsimpl in *; exists L; attac.
    Qed.

    #[export] Hint Resolve net_lock_move_eq net_lock_on_move_eq : LTS.


    (** Deadlocked set is a list of processes so that their lock lists are sublists of it *)
    Inductive DeadSet (DS : list Name) N :=
      deadset
        (HDS_Nil : DS <> [])
        (HDS_Sub : forall (n : Name),
            List.In n DS ->
            exists (L : list Name), net_lock N L n /\ incl L DS
        )
        : DeadSet DS N.


    (** Network is deadlocked when it has a deadlocked set *)
    Inductive Deadlocked N : Prop :=
    | deadnet (DL : Names) :
      DeadSet DL N ->
      Deadlocked N
    .

    #[export] Hint Constructors Deadlocked : LTS.


    Example dead_net_example [N n0 n1 n2] :
      net_lock N [n0] n1 ->
      net_lock N [n1] n2 ->
      net_lock N [n2] n0 ->
      Deadlocked N.

    Proof with attac.
      intros HL0 HL1 HL2.
      apply (deadnet N [n0; n1; n2]).

      split...

      destruct H > [subst|destruct H > [subst|destruct H]]; eattac 5.
    Qed.


    (** Obtaining lock sets of deadset members *)
    Lemma deadset_net_lock [N DS n] :
      DeadSet DS N ->
      List.In n DS ->
      exists (L : list Name), net_lock N L n /\ incl L DS.

    Proof.
      intros HDS HIn.
      kill HDS; auto.
    Qed.

    #[export] Hint Resolve deadset_net_lock : LTS.


    (** Deadset is not empty *)
    Lemma deadset_nil [N DS] :
      DeadSet DS N ->
      DS <> [].

    Proof.
      intros HDS.
      kill HDS; auto.
    Qed.

    #[export] Hint Resolve deadset_nil : LTS.


    Lemma deadset_nil_inv N DS : DS = [] -> DeadSet DS N <-> False.
    Proof. attac. Qed.

    #[export] Hint Rewrite -> deadset_nil_inv using spank : LTS LTS_concl.


    (** Decidability of locks within deadsets *)
    Lemma deadset_lock_on_dec [N DS n0] :
      DeadSet DS N ->
      List.In n0 DS ->
      forall n1, (net_lock_on N n0 n1 \/ not (net_lock_on N n0 n1)).

    Proof with eattac.
      intros HDS HIn0 n1.

      apply (deadset_net_lock HDS) in HIn0 as [L [HL Hincl]].
      unfold net_lock_on.
      destruct (in_dec NAME.eq_dec n1 L)...
    Qed.


    (** Remove duplicates from a deadset *)
    Theorem deadset_nodup [N DS] :
      DeadSet DS N ->
      DeadSet (nodup NAME.eq_dec DS) N.

    Proof with (auto with datatypes).
      intros HDS.
      kill HDS.
      constructor.
      - destruct DS...
        assert (List.In n ((n::DS)))...
        apply (nodup_In NAME.eq_dec) in H.
        destruct (nodup NAME.eq_dec (n :: DS))...
      - intros n HIn.
        ltac1:(apply -> (nodup_In NAME.eq_dec) in HIn).
        specialize (HDS_Sub n HIn) as [L [HL HIn']].
        exists L.
        split...
        apply nodup_incl...
    Qed.

    #[export] Hint Immediate deadset_nodup : LTS.


    (** Helper lemma for transforming statements on deadsets by adding [NoDup] *)
    Lemma with_deadset_nodup {P : Prop} [N DS] :
      (forall DS, DeadSet DS N -> NoDup DS -> P) ->
      DeadSet DS N -> P.

    Proof.
      intros F HDS.
      specialize (deadset_nodup HDS) as HDS'.
      specialize (NoDup_nodup NAME.eq_dec DS) as HNoDup.
      apply (F _ HDS' HNoDup).
    Qed.


    (** No members of a deadlocked set do tau *)
    Corollary deadset_no_tau [N0 N1 DL n a] :
      DeadSet DL N0 ->
      List.In n DL ->
      not (N0 =(NTau n a)=> N1).

    Proof with attac.
      unfold not.
      intros HDL HIn T.
      consider (exists (L : list Name), net_lock N0 L n /\ incl L DL).
      unfold net_lock in *.
      hsimpl in *.
      rewrite pq_lock_recv_inv in T; eauto.
      hsimpl in *. bullshit.
    Qed.


    (** No members of a deadlocked set send *)
    Corollary deadset_no_send [N0 N1 DL ns nr t v] :
      DeadSet DL N0 ->
      List.In ns DL ->
      not (N0 =(NComm ns nr t v)=> N1).

    Proof with attac.
      unfold not.
      intros HDS HIn T.

      kill T.

      apply (deadset_net_lock HDS) in HIn as [L [HL _]].
      kill H.
      have (NetMod.get ns N0 =( send (nr, &t) v )=> &S).

      absurd ( match send (nr, &t) v with
               | Recv _ _ => True
               | _ => False
               end ).
      1: attac.

      have (pq_lock L (NetMod.get ns N0)).
      eapply pq_lock_recv; re_have eauto.
    Qed.


    (** If a member of a deadlocked set is involved in a communication, then it's not the sender *)
    Corollary deadset_no_send' [N0 N1 DL ns nr n t v] :
      DeadSet DL N0 ->
      List.In n DL ->
      (N0 =(NComm ns nr t v)=> N1) ->
      n <> ns.

    Proof.
      unfold not.
      intros HDL HIn T HEq.
      subst.
      eapply deadset_no_send; eauto.
    Qed.


    (** If a member of a deadlocked set is involved in an action, then it's a receiver *)
    Corollary deadset_recv [N0 N1 DL nr a] :
      DeadSet DL N0 ->
      List.In nr DL ->
      (N0 =(a)=> N1) ->
      List.In nr (act_particip a) ->
      exists ns t v, a = NComm ns nr t v.

    Proof with attac.
      intros HDL HInD T HInP.

      destruct a; simpl in HInP.
      - destruct HInP; auto; subst.
        eapply deadset_no_tau in T; eauto.
        bullshit.
        bullshit.
      - destruct HInP; auto; subst.

        eapply deadset_no_send in T; eauto.
        bullshit.

        destruct H; subst; eauto.
        bullshit.
    Qed.


    (** A member of a deadlocked set remains deadlocked after any transition *)
    Theorem deadset_stay1 [a N0 N1 DL n I0 P0 O0] :
      DeadSet DL N0 ->
      List.In n DL ->
      (N0 =(a)=> N1) ->
      NetMod.get n N0 = (pq I0 P0 O0) ->
      exists I', NetMod.get n N1 = (pq (I0 ++ I') P0 O0).

    Proof with eattac.
      intros HDL HInD T HEq0.

      destruct (in_dec NAME.eq_dec n (act_particip a)).
      - destruct (deadset_recv HDL HInD T i) as (ns & t & v & HEq).
        subst.

        specialize (deadset_no_send' HDL HInD T) as HNeq.
        clear i.
        exists [(ns, &t, v)].

        hsimpl in *.
        hsimpl in |- *.

        rewrite HEq0 in T0.
        ltac1:(autorewrite with LTS in T0)... (* TODO coq bug *)

      - exists [].
        rewrite app_nil_r.
        rewrite <- HEq0.
        apply eq_sym.
        eapply (act_particip_stay `(~ List.In n _)).
        attac.
    Qed.


    (** Members of a deadlocked set retain their locksets *)
    Theorem deadset_invariant_lock [N0 N1 DL L a n] :
      DeadSet DL N0 ->
      net_lock N0 L n ->
      List.In n DL ->
      (N0 =(a)=> N1) ->
      net_lock N1 L n.

    Proof.
      intros HDL HL HInD T.

      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:HEq0.
      destruct (deadset_stay1 HDL HInD T HEq0) as [I' HEq1].

      destruct (in_dec NAME.eq_dec n (act_particip a)).
      - destruct (deadset_recv HDL HInD T i) as (ns & t & v & HEq).
        subst.

        have (N0 =( NComm ns n &t v )=> N1).

        specialize (deadset_no_send' HDL HInD T) as HNeq.
        clear i.

        hsimpl in *.
        ltac1:(autorewrite with LTS in * ).

        unfold net_lock.
        hsimpl in *. hsimpl in |- *.

        consider (&O = []) by attac.

        constructor; attac.

        enough (~ In (n0, R, v) [(ns, &t, v0)]).
        {
          hsimpl in *.
          apply in_app_or in H1.
          assert (In (n0, R, v) &I \/ In (n0, R, v) [(ns, &t, v0)]) as [|]; attac.
        }

        intros Hx; kill Hx; hsimpl in *.

        assert (exists (L : list Name), net_lock N0 L n /\ incl L DL) by attac; hsimpl in *.
        assert (incl L L0) by (unfold net_lock in *; eapply pq_lock_incl; eauto).
        assert (List.In n0 DL) by attac.
        re_have (eapply deadset_no_send'; eauto with LTS).

      - eapply act_particip_stay in n0; eauto.
        unfold net_lock in *.
        rewrite <- n0.
        auto.
    Qed.


    (** Deadlocked set remains after any transition *)
    Theorem deadset_invariant DL : trans_invariant (DeadSet DL) always.

    Proof with attac.
      unfold trans_invariant.
      intros N0 N1 a T HDS _.

      constructor; intros; kill HDS...
      destruct (HDS_Sub n H) as [L [HL HIncl]].

      exists L...

      eapply deadset_invariant_lock...
    Qed.

    #[export] Hint Resolve deadset_invariant : inv.
    #[export] Hint Extern 2 (DeadSet _ _) => solve_invariant : LTS.


    (** Deadlocked processes can only change their inbox *)
    Theorem deadset_stay [path N0 N1 DL n I0 P0 O0] :
      DeadSet DL N0 ->
      List.In n DL ->
      (N0 =[path]=> N1) ->
      NetMod.get n N0 = (pq I0 P0 O0) ->
      exists I', NetMod.get n N1 = (pq (I0 ++ I') P0 O0).

    Proof.
      generalize dependent I0.
      generalize dependent N0.
      induction path; intros N0 I0 HDL HInD T HEq0.
      - kill T. exists []. rewrite app_nil_r. auto.
      - apply path_split1 in T as [N0' [T0 T1]].

        destruct (deadset_stay1 HDL HInD T0 HEq0) as [I' HEq1].
        specialize (IHpath N0' (I0 ++ I') ltac:(eattac) HInD T1 HEq1) as [I'' HEq]; eattac.
        exists (I' ++ I'').
        rewrite HEq.

        ltac1:(rewrite_strat bottomup progress app_assoc  ).
        repeat (rewrite app_assoc).
        eattac.
    Qed.


    (** If you are a member of a deadset, then your lock set is its subset *)
    Lemma deadset_incl [N DS n L] :
      DeadSet DS N ->
      net_lock N L n ->
      List.In n DS ->
      incl L DS.

    Proof with eauto.
      intros HDS HL HIn.
      eapply deadset_net_lock in HIn as [L' [HL' Hincl]]...
      eapply incl_tran...
      eapply net_lock_equiv...
    Qed.

    #[export] Hint Immediate deadset_incl : LTS.


    (** If [n0] is a member of a deadset and locked on [n1], then [n1] is too *)
    Lemma deadset_in [N DS n0 n1] :
      DeadSet DS N ->
      List.In n0 DS ->
      net_lock_on N n0 n1 ->
      List.In n1 DS.

    Proof.
      intros HDS HIn HL.
      destruct HL as [L [HIn' HL]]...
      eapply deadset_incl; eauto.
    Qed.

    #[export] Hint Immediate deadset_in : LTS.


    (** Deadlocks are invariantd across network transitions *)
    Corollary deadlock_invariant : trans_invariant Deadlocked always.

    Proof.
      unfold trans_invariant; intros N0 N1 a T HDL _.
      kill HDL.
      apply (deadnet N1 DL); auto.
      eapply (deadset_invariant); eauto.
    Qed.

    #[export] Hint Resolve deadlock_invariant : inv.


    (** Transitive closure of the individual lock relation *)
    Inductive dep_on (N : PNet) (n0 : Name) : Name -> Prop :=
    | dep_on_Direct [n1] :
      net_lock_on N n0 n1 ->
      dep_on N n0 n1
    | dep_on_Indirect [n1 n2] :
      net_lock_on N n0 n1 ->
      dep_on N n1 n2 ->
      dep_on N n0 n2
    .

    #[export] Hint Immediate dep_on_Direct : LTS.

    #[export] Hint Extern 4 (dep_on _ _ _) =>
      match goal with
      (* | [h0 : net_lock_on ?N ?a ?b |- dep_on ?N ?a ?b ] => (apply (dep_on_Direct _ _ h0)) *)
      | [h0 : net_lock_on ?N ?a ?b, h1 : dep_on ?N ?b ?c |- dep_on ?N ?a ?c ] => (apply (dep_on_Indirect _ _ h0 h1))
      end : LTS.


    (** Indirect lock is transitive *)
    Lemma dep_on_seq [N : PNet] [n0 n1 n2] :
      dep_on N n0 n1 ->
      dep_on N n1 n2 ->
      dep_on N n0 n2.

    Proof with (eauto with LTS).
      intros HL0 HL1.
      generalize dependent n2.
      induction HL0; intros...
      enough (dep_on N n1 n3)...
    Qed.

    #[export] Hint Resolve dep_on_seq : LTS.


    (** Indirect lock is transitive over locks (front) *)
    Lemma dep_on_seq1 [N : PNet] [n0 n1 n2] :
      net_lock_on N n0 n1 ->
      dep_on N n1 n2 ->
      dep_on N n0 n2.

    Proof with (eauto with LTS).
      intros HL0 HL1...
    Qed.


    (** Indirect lock is transitive over locks (back) *)
    Lemma dep_on_seq1' [N : PNet] [n0 n1 n2] :
      dep_on N n0 n1 ->
      net_lock_on N n1 n2 ->
      dep_on N n0 n2.

    Proof with (eauto with LTS).
      intros HL0 HL1.
      eauto with LTS.
    Qed.

    #[export] Hint Immediate dep_on_seq1' : LTS.


    (** Collection of all names on which a given service is indirectly or directly locked on *)
    Definition dep_set N L n :=
      forall m, List.In m L <-> dep_on N n m.

    #[export] Hint Transparent dep_set : LTS.


    (** Dep set is a superset of the lock set *)
    Lemma dep_set_lock_incl [N IL L n] :
      dep_set N IL n ->
      net_lock N L n ->
      incl L IL.

    Proof.
      unfold incl.
      unfold dep_set.
      intros HIL HL m HIn.
      apply HIL.
      constructor.
      unfold net_lock_on.
      eauto with LTS.
    Qed.

    #[export] Hint Resolve dep_set_lock_incl : LTS.


    (** All dep sets are mutually inclusive *)
    Lemma dep_set_incl [N L0 L1 n] :
      dep_set N L0 n ->
      dep_set N L1 n ->
      incl L0 L1.

    Proof.
      intros HD0 HD1.
      intros m HIn.
      apply HD0 in HIn.
      apply HD1 in HIn.
      auto.
    Qed.

    #[export] Hint Resolve dep_set_incl : LTS.


    (** If you are a member of your own depset, then you depend on yourself *)
    Fact dep_set_in_self [N DS n] :
      dep_set N DS n ->
      List.In n DS ->
      dep_on N n n.

    Proof with attac.
      intros HDS HIn.
      apply HDS in HIn...
    Qed.

    #[export] Hint Immediate dep_set_in_self : LTS.


    (** If you are a member of a deadset, then everyone you depend on is also in that deadset *)
    Lemma deadset_dep_in [N DS n0 n1] :
      DeadSet DS N ->
      List.In n0 DS ->
      dep_on N n0 n1 ->
      List.In n1 DS.

    Proof.
      intros HDS HIn HD.
      induction HD.
      - eapply deadset_in; eauto.
      - eapply deadset_in in H; eauto.
    Qed.

    #[export] Hint Immediate deadset_dep_in : LTS.


    (** If you are a member of a deadset, then your dep set is its subset *)
    Theorem deadset_dep_set_incl [N DS L n] :
      DeadSet DS N ->
      dep_set N L n ->
      List.In n DS ->
      incl L DS.

    Proof.
      intros HDS HL HIn.
      intros n0 HIn0.
      eapply deadset_dep_in; eauto with LTS.
      apply HL; auto.
    Qed.

    #[export] Hint Immediate deadset_dep_set_incl : LTS.


    (** Transitive closure of lock relation with exposed connection *)
    Inductive lock_chain (N : PNet) : Name -> list Name -> Name -> Prop :=
    | LC_nil [n0 n1] :
      net_lock_on N n0 n1 ->
      lock_chain N n0 [] n1
    | LC_cons [n0 n1 n2 l] :
      net_lock_on N n0 n1 ->
      lock_chain N n1 l n2 ->
      lock_chain N n0 (n1::l) n2.

    #[export] Hint Constructors lock_chain : LTS.


    (** Transitivity of lock_chain (single step, front) *)
    Lemma lock_chain_seq1 [N L n0 n1 n2] :
      net_lock_on N n0 n1 ->
      lock_chain N n1 L n2 ->
      lock_chain N n0 (n1 :: L) n2.

    Proof.
      intros HLc HL.
      eauto with LTS.
    Qed.


    (** Transitivity of lock_chain (single step, back) *)
    Lemma lock_chain_seq1' [N L n0 n1 n2] :
      lock_chain N n0 L n1 ->
      net_lock_on N n1 n2 ->
      lock_chain N n0 (L ++ [n1]) n2.

    Proof.
      intros HLc HL.

      generalize dependent n0 n1 n2.
      induction L; intros; simpl in *; kill HLc; attac.
    Qed.

    #[export] Hint Immediate lock_chain_seq1' : LTS.


    (** Transitivity of lock_chain *)
    Lemma lock_chain_seq [N L0 L1 n0 n1 n2] :
      lock_chain N n0 L0 n1 ->
      lock_chain N n1 L1 n2 ->
      lock_chain N n0 (L0 ++ n1::L1) n2.

    Proof.
      intros HLc0 HLc1.
      generalize dependent n0 n1 n2.
      induction L0; intros; simpl in *; kill HLc0; attac.
    Qed.

    #[export] Hint Resolve lock_chain_seq : LTS.


    (** Lock chain can be split if there is a known node in the middle *)
    Lemma lock_chain_split [N L0 L1 n0 n1 n2] :
      lock_chain N n0 (L0 ++ n1::L1) n2 ->
      lock_chain N n0 L0 n1 /\ lock_chain N n1 L1 n2.

    Proof with attac.
      intros HLc.
      generalize dependent n0 n1 n2 L1.
      induction L0; intros; simpl in *; kill HLc.
      - attac.
      - specialize (IHL0 L1 n2 n1 a) as (HLc0 & HLc1); attac.
    Qed.


    Lemma lock_chain_seq_inv N L0 L1 n0 n1 n2 :
      lock_chain N n0 (L0 ++ n1::L1) n2 <-> lock_chain N n0 L0 n1 /\ lock_chain N n1 L1 n2.
    Proof. split; attac. all: apply lock_chain_split in H; attac. Qed.

    #[export] Hint Rewrite -> @lock_chain_seq_inv using assumption : LTS.


    (** Lock chain can be split if there is a known node in the middle *)
    Lemma lock_chain_split_in [N L n0 n1 n2] :
      List.In n1 L ->
      lock_chain N n0 L n2 ->
      exists L0 L1,
        L = L0 ++ n1 :: L1
        /\ lock_chain N n0 L0 n1
        /\ lock_chain N n1 L1 n2.
    Proof with attac.
      intros HIn HLc.
      generalize dependent n0 n1 n2.
      induction L; intros; simpl in *; kill HLc; kill HIn.
      - exists [], L...
      - have (net_lock_on N n0 a).

        normalize IHL.
        specialize (IHL n2 n1 a ltac:(auto) ltac:(auto)).
        destruct IHL as (L0 & L1 & HEq & HLc0 & HLc1); eattac.
    Qed.


    (** If [n0] is indirectly locked on [n1], then we can obtain a lock chain *)
    Lemma dep_lock_chain [N n0 n1] :
      dep_on N n0 n1 ->
      exists L, lock_chain N n0 L n1 /\ not (List.In n1 L).

    Proof with auto.
      intros HL.
      induction HL.
      - exists []; split...
        constructor; auto.
      - destruct IHHL as [L [HLc HIn]].
        smash_eq n1 n2.
        + exists []; split...
          constructor; auto.
        + exists (n1::L); split...
          constructor; auto.
          unfold not; intros.
          kill H0; bullshit.
    Qed.


    (** Lock chain indicates an indirect lock *)
    Lemma lock_chain_dep [N n0 n1 L] :
      lock_chain N n0 L n1 ->
      dep_on N n0 n1.

    Proof.
      intros HLc.
      induction HLc.
      - constructor; auto.
      - eapply dep_on_seq1; eauto.
    Qed.

    #[export] Hint Immediate lock_chain_dep : LTS.


    (** Lock chain can be split to dependency relation on any intermediate node *)
    Lemma lock_chain_dep_in [N n0 n1 n2 L] :
      lock_chain N n0 L n2 ->
      List.In n1 L ->
      dep_on N n0 n1.

    Proof.
      intros HLc HIn.
      induction HLc; kill HIn.
      - constructor; auto.
      - specialize (IHHLc H0).
        eapply dep_on_seq1; eauto.
    Qed.

    #[export] Hint Immediate lock_chain_dep_in : LTS.


    (** Dep set of [n0] always a superset of all lock chains starting at [n0] *)
    Lemma lock_chain_dep_set_incl [N S L n0 n1] :
      dep_set N S n0 ->
      lock_chain N n0 L n1 ->
      incl L S.

    Proof.
      intros HI HLc n HIn.

      destruct (lock_chain_split_in HIn HLc) as (L0 & HLc' & HEq & HLc0 & _).
      apply lock_chain_dep in HLc0.
      apply HI in HLc0; auto.
    Qed.

    #[export] Hint Immediate lock_chain_dep_set_incl : LTS.


    (** Dep set of [n0] always a superset of all lock chains starting at [n0] *)
    Lemma lock_chain_dep_set_In [N S L n0 n1] :
      dep_set N S n0 ->
      lock_chain N n0 L n1 ->
      List.In n1 S.

    Proof.
      intros HI HLc.
      apply lock_chain_dep in HLc.
      apply HI; auto.
    Qed.

    #[export] Hint Immediate lock_chain_dep_set_In : LTS.


    Lemma dep_on_ind_right :
      forall P : PNet -> Name -> Name -> Prop,
        (forall N n0 n2, net_lock_on N n0 n2 -> P N n0 n2) ->
        (forall N n0 n1 n2, dep_on N n0 n1 -> net_lock_on N n1 n2 -> P N n1 n2 -> P N n0 n2) ->
        forall N n0 n2, dep_on N n0 n2 -> P N n0 n2.
    Proof.
      intros P Hbase Hind N n0 n2 H.
      apply dep_lock_chain in H as [L [? ?]].
      generalize dependent n0.
      induction L using rev_ind; intros.
      - attac. eapply Hbase. eattac.
      - apply lock_chain_split in H as [? ?].
        kill H1.
        eapply Hind; eauto with LTS.
    Qed.


    (* Reverse inversion of [dep_on] *)
    Theorem dep_on_inv_r [N n0 n1] :
      dep_on N n0 n1 ->
      net_lock_on N n0 n1 \/ exists n0', dep_on N n0 n0' /\ net_lock_on N n0' n1.

    Proof.
      intros.
      induction `(dep_on N n0 n1); eattac.
      destruct `(_ \/ _); attac.
    Qed.

    #[export] Hint Resolve dep_on_inv_r : LTS.


    Lemma net_lock_all_in [N L n0 n1] :
      net_lock N L n0 ->
      net_lock_on N n0 n1 ->
      In n1 L.

    Proof.
      intros.
      unfold net_lock_on in *.
      eattac.
    Qed.

    Lemma net_lock_only_in [N L n0 n1] :
      net_lock N L n0 ->
      In n1 L ->
      net_lock_on N n0 n1.

    Proof.
      intros.
      unfold net_lock_on in *.
      eattac.
    Qed.

    #[export] Hint Immediate net_lock_only_in net_lock_all_in : LTS.



    (** If [n0] is in a deadset, then ends of all lock chains starting at [n0] belong to the deadset
     *)
    Lemma lock_chain_deadset_in [N DS L n0 n1] :
      DeadSet DS N ->
      List.In n0 DS ->
      lock_chain N n0 L n1 ->
      List.In n1 DS.

    Proof with eattac.
      intros HDS HIn HLc.
      have (dep_on N n0 n1).
      eattac.
    Qed.

    #[export] Hint Immediate lock_chain_deadset_in : LTS.


    (** If [n0] is in a deadset, then the deadset is a superset of all lock chains starting at [n0]
     *)
    Lemma lock_chain_deadset_incl [N DS L n0 n1] :
      DeadSet DS N ->
      List.In n0 DS ->
      lock_chain N n0 L n1 ->
      incl L DS.

    Proof with eattac.
      intros HDS HIn HLc.
      intros n HIn'.
      destruct (lock_chain_split_in HIn' HLc) as (L0 & HLc' & HEq & HLc0 & _)...
    Qed.

    #[export] Hint Immediate lock_chain_deadset_incl : LTS.


    Open Scope nat_scope.

    Local Lemma deadset_dep_dec_nope_k' [N n0 n2 L_ref L_i L_x k] :
      ~ List.In n2 L_ref ->
      L_ref = L_x ++ L_i  ->
      (forall n1, net_lock_on N n0 n1 -> List.In n1 L_ref) ->
      (forall n1, List.In n1 L_ref -> net_lock_on N n0 n1) ->
      (forall n1 Lc, List.In n1 L_ref -> ~ (lock_chain N n1 Lc n2 /\ length Lc <= k)) ->
      (forall Lc, lock_chain N n0 Lc n2 -> length Lc <= S k -> exists n1 Lc1, List.In n1 L_x /\ lock_chain N n1 Lc1 n2).
    Proof with eattac.
      intros HNIn H_sum HLIn HInL HNL Lc H_x.

      generalize dependent L_x.
      generalize dependent n0.
      induction L_i; intros; simpl in *.
      - kill H_x; attac.
      - assert (L_ref = (L_x ++ [a]) ++ L_i) by attac.
        clear H_sum.

        edestruct IHL_i as (n1 & Lc1 & HIn1 & HLc1); eauto with LTS.
        apply in_app_or in HIn1 as [HIn | HIn]; subst.
        + exists n1, Lc1...
        + kill HIn; doubt.
          kill H_x.
          1: bullshit.
          apply HLIn in H0.
          eapply HNL in H0; doubt.
          destruct H0.
          eattac.
          simpl in *; lia.
    Qed.


    (* Dont export *)
    Hint Unfold net_lock_on : LTS.

    Local Lemma deadset_dep_dec_k [N DS n0] n1 k :
      DeadSet DS N ->
      List.In n0 DS ->
      (exists L, length L <= k /\ lock_chain N n0 L n1)%nat
      \/ not (exists L, (length L <= k /\ (lock_chain N n0 L n1)))%nat.

    Proof with attac.
      intros HDS HIn.

      generalize dependent n0.
      induction k; intros.
      - destruct (deadset_lock_on_dec HDS HIn n1).
        + left.
          exists [].
          split; eauto.
          constructor.
          auto.
        + right.
          intros Hx.
          destruct Hx as [L [HLen HL]].
          destruct L; kill HL...
      - rename n1 into n2.
        eapply deadset_net_lock in HIn as [L [HL Hincl]]; eauto.

        assert (
            forall n0 : Name,
              List.In n0 L ->
              (exists L : Names, (length L <= k)%nat /\ lock_chain N n0 L n2) \/
                ~ (exists L : Names, (length L <= k)%nat /\ lock_chain N n0 L n2)
          ) as IHk' by attac.

        clear IHk. rename IHk' into IHk.

        apply decide_any in IHk.
        destruct IHk.
        + destruct H as [a [HIna [L' [HLen HL']]]].
          left.
          exists (a::L'); eattac; simpl.
          auto using le_n_S.
        + destruct (in_dec NAME.eq_dec n2 L) as [?|HNIn].
          {
            left.
            exists []; eattac. simpl; lia.
          }
          assert (L = [] ++ L) as H_sum by auto.
          assert (forall n1, net_lock_on N n0 n1 -> List.In n1 L) as HLIn.
          {
            intros.
            destruct H0 as [L' [HIn' HL']].
            destruct (net_lock_equiv HL HL').
            apply H1.
            assumption.
          }
          assert (forall n1, List.In n1 L -> net_lock_on N n0 n1) as HInL.
          {
            intros.
            exists L; split; auto.
          }
          assert (forall n1 Lc, List.In n1 L -> ~ (lock_chain N n1 Lc n2 /\ (length Lc <= k))) as HNL.
          {
            intros.
            specialize (H n1 H0).
            intros HLc.
            destruct HLc as [HLc HLen].
            eapply H.
            exists Lc.
            split; auto.
          }

          specialize (deadset_dep_dec_nope_k' HNIn H_sum HLIn HInL HNL).

          right.
          intros Hx.
          destruct Hx as [L' [HLen' HL']].
          specialize (H0 L' HL') as (n1 & Lc1 & HIn1 & HLc1)...
    Qed.


    (** Any lock chain can be truncated not to contain any duplicates *)
    Lemma lock_chain_dedup [N L n0 n1] :
      lock_chain N n0 L n1 ->
      exists L',
        lock_chain N n0 L' n1
        /\ NoDup L'
        /\ not (List.In n0 L')
        /\ not (List.In n1 L').

    Proof with eattac.
      intros HLc.

      enough (exists L',
                 lock_chain N n0 L' n1
                 /\ NoDup L'
                 /\ not (List.In n0 L')
             ) as (L' & HLc' & HNoDup' & HNIn').
      {
        subst.
        destruct (partition_first (NAME.eqb n1) L') eqn:HEqn1.
        specialize (partition_first_Forall _ _ HEqn1) as Hl0.
        specialize (partition_first_eq _ _ HEqn1) as HEql. subst.
        destruct l0.
        - rewrite app_nil_r in *.
          exists l.
          repeat split; eauto.

          assert (forall x, List.In x l -> n1 <> x).
          apply Forall_forall.
          unshelve eapply (Forall_impl _ _ Hl0).
          + intros.
            simpl in H.
            apply NAME_H.eqb_neq_inv in H.
            auto.
          + intros HIn.
            apply H in HIn.
            bullshit.
        - specialize (partition_first_find _ _ HEqn1) as HEqn.
          apply NAME.eqb_eq in HEqn.
          subst.
          apply lock_chain_split in HLc' as [HLc' _].
          exists l.
          repeat split; eauto with datatypes.
          + apply NoDup_app_remove_r in HNoDup'; auto.
          + assert (forall x, List.In x l -> &t <> x).
            {
              apply Forall_forall.
              unshelve eapply (Forall_impl _ _ Hl0).
              intros.
              apply NAME_H.eqb_neq_inv in H.
              auto.
            }
            intros HIn.
            apply H in HIn.
            bullshit.
      }

      generalize dependent n1.
      generalize dependent n0.
      generalize dependent L.
      refine '(partition_last_eq_init_cons_ind NAME.eqb _ _ _ _).
      - split; intros.
        apply NAME.eqb_eq...
        attac.
      - intros n1 n0 HLc.
        exists []; split...
        constructor.
      - intros a L L0 Hpart HI n0 n1 HLc.
        kill HLc.

        specialize (partition_last_Forall (NAME.eqb a) L) as Hl0.
        specialize (partition_last_eq _ _ Hpart) as HEql. subst.
        rewrite Hpart in Hl0.

        rewrite app_nil_r in *.

        specialize (HI a n1) as [L (HLc & HNoDup)]; auto.

        destruct HNoDup as [HNoDup HNIn].
        smash_eq n0 a. exists L...

        destruct (partition_last (NAME.eqb n0) L) eqn:HEqn0.
        specialize (partition_last_Forall (NAME.eqb n0) L) as Hn0.
        specialize (partition_last_eq _ _ HEqn0) as HEqL. subst.
        rewrite HEqn0 in Hn0.

        destruct l0.
        + rewrite app_nil_r in *.
          exists (a::l).
          repeat split; auto with LTS datatypes.
          constructor; auto.
          intros HIn.
          kill HIn; doubt.
          eapply Forall_forall in Hn0.
          eapply NAME_H.eqb_neq_inv in Hn0.
          bullshit.
          auto.
        + specialize (partition_last_find _ _ HEqn0) as HEqL.
          apply NAME.eqb_eq in HEqL. subst.
          apply lock_chain_split in HLc as [_ HLc].
          exists l0.
          repeat split; auto with LTS datatypes.
          apply NoDup_app_remove_l in HNoDup.
          kill HNoDup; auto.
          intros HIn.
          eapply Forall_forall in Hn0.
          eapply NAME_H.eqb_neq_inv in Hn0.
          bullshit.
          auto.

      - intros a L L0 L1 Hpart HI n0 n1 HLc.
        kill HLc.

        specialize (partition_last_Forall (NAME.eqb a) L) as Hl0.
        specialize (partition_last_eq _ _ Hpart) as HEql. subst.
        rewrite Hpart in Hl0.

        ltac1:(autorewrite with LTS in * ). (* TODO bug *)
        attac.
    Qed.


    Lemma deadset_lock_chain_len [N DS n0 n1 L] :
      DeadSet DS N ->
      List.In n0 DS ->
      lock_chain N n0 L n1 ->
      exists L', length L' <= length DS /\ lock_chain N n0 L' n1.

    Proof.
      intros HDS HIn HLc.

      apply lock_chain_dedup in HLc as (L' & HLc' & HNoDup & HIn0' & HIn1'); subst.

      assert (incl L' DS) as Hincl by eauto with LTS.
      exists L'; split; auto.
      apply (NoDup_incl_length HNoDup Hincl).
    Qed.


    Lemma deadset_dep_dec [N DS n0] n1 :
      DeadSet DS N ->
      List.In n0 DS ->
      (exists L, lock_chain N n0 L n1)
      \/ forall L, ~ lock_chain N n0 L n1.

    Proof with eattac.
      intros HDS HIn.

      destruct (deadset_dep_dec_k n1 (length DS) HDS HIn).
      - left.
        destruct H as [L [_ HL]]...
      - right.
        intros L HL.
        apply H.
        eapply deadset_lock_chain_len...
    Qed.


    (** If you are a member of a deadset, then your depset is decidable *)
    Lemma deadset_dep_set [N DS n0] :
      DeadSet DS N ->
      List.In n0 DS ->
      exists L, dep_set N L n0.

    Proof with attac.
      intros HDS HIn.

      assert (exists Lin Lout,
                 (forall n, dep_on N n0 n -> List.In n (Lin ++ Lout))
                 /\ (forall n, List.In n Lout -> dep_on N n0 n)
                 /\ incl Lout DS
             ) as (Lin & Lout & HDepIn & HInDep & Hincl_out).
      {
        exists DS, [].
        rewrite app_nil_r.
        repeat split; intros; auto with datatypes.
        - eapply deadset_dep_in; eauto.
        - kill H.
        - intros x Hx.
          kill Hx.
      }

      generalize dependent n0.
      generalize dependent Lout.
      induction Lin; intros; simpl in *.
      - exists Lout...

      - destruct (deadset_dep_dec a HDS HIn).
        + destruct H as [L HL].
          apply lock_chain_dep in HL. clear L.
          assert (incl (a::Lout) DS) as Hincl_a_out by eauto with LTS datatypes.

          specialize (IHLin (a::Lout) Hincl_a_out n0 HIn).
          apply IHLin; intros.
          * apply HDepIn in H.
            destruct H; subst; eauto with datatypes.
            apply in_app_or in H.
            destruct H; eauto with datatypes.
          * kill H...
        + specialize (IHLin Lout Hincl_out n0 HIn).
          apply IHLin; intros; auto.
          specialize (dep_lock_chain H0) as [L [HL _]].
          apply HDepIn in H0.
          destruct H0; subst; eauto with datatypes.
          apply H in HL.
          bullshit.
    Qed.

    #[export] Hint Immediate deadset_dep_set : LTS.


    (** Non-empty dep sets of members of deadsets are are deadsets *)
    Lemma deadset_dep_set_deadset [DS N n L] :
      DeadSet DS N ->
      dep_set N L n ->
      L <> [] ->
      List.In n DS ->
      DeadSet L N.

    Proof with eauto with LTS.
      intros HDS HD HNnil HIn.
      constructor...

      rename n into n0.
      intros n1 HIn1.

      apply HD in HIn1 as HD1.

      specialize (deadset_dep_in HDS HIn HD1) as HIn1'.
      specialize (deadset_net_lock HDS HIn1') as [L1 [HL1' Hincl]].

      exists L1; split...
      intros n2 HIn2.
      apply HD...
      have (net_lock_on N n1 n2).
      eattac.
    Qed.

    #[export] Hint Immediate deadset_dep_set_deadset : LTS.


    Definition deadlocked n N := exists DS, List.In n DS /\ DeadSet DS N.


    Lemma deadlocked_invariant n : trans_invariant (deadlocked n) always.

    Proof.
      unfold trans_invariant, deadlocked; intros.
      hsimpl in *.
      exists DS.
      split; eauto with inv LTS.
    Qed.

    #[export] Hint Resolve deadlocked_invariant : inv.
    #[export] Hint Extern 10 (deadlocked _ _) => solve_invariant : LTS.


    Lemma deadlocked_lock_on [N : PNet] [n0 : Name] [n1 : Name] :
      deadlocked n0 N ->
      net_lock_on N n0 n1 ->
      deadlocked n1 N.

    Proof.
      unfold deadlocked.
      intros.
      hsimpl in *.
      exists DS.
      split; eauto with LTS.
    Qed.

    #[export] Hint Resolve deadlocked_lock_on : LTS.

    Lemma deadlocked_dep [N : PNet] [n0 : Name] [n1 : Name] :
      deadlocked n0 N ->
      dep_on N n0 n1 ->
      deadlocked n1 N.

    Proof.
      unfold deadlocked.
      intros.
      hsimpl in *.
      exists DS.
      split; eauto with LTS.
    Qed.

    #[export] Hint Resolve deadlocked_dep : LTS.


    Lemma deadlocked_lock' [N : PNet] [n0 : Name] [n1 : Name] :
      deadlocked n1 N ->
      net_lock N [n1] n0 ->
      deadlocked n0 N.

    Proof.
      unfold deadlocked.
      intros.
      hsimpl in *.
      exists (n0 :: DS).
      unfold net_lock_on in *.
      hsimpl in *.
      split; auto with LTS datatypes.
      constructor; attac.
      consider ((n0 = n \/ List.In n DS)); subst.
      - exists [n1].
        split. 1: attac.
        enough (incl [n1] DS) by attac.
        intros ? ?; attac.
      - consider (exists (L : list Name), net_lock N L n /\ incl L DS).
        eattac.
    Qed.

    #[export] Hint Resolve deadlocked_lock' : LTS.


    Lemma deadlocked_lock_invariant1 [N0 N1 : PNet] [n0 : Name] [L : Names] [a] :
      (N0 =(a)=> N1) ->
      deadlocked n0 N0 ->
      net_lock N0 L n0 ->
      net_lock N1 L n0.

    Proof.
      unfold deadlocked.
      intros.
      hsimpl in *.
      eauto using deadset_invariant_lock with datatypes.
    Qed.

    #[export] Hint Resolve deadlocked_lock_invariant1 | 0 : LTS.


    Lemma deadlocked_lock_on_invariant1 [N0 N1 : PNet] [n0 n1 : Name] [a] :
      (N0 =(a)=> N1) ->
      deadlocked n0 N0 ->
      net_lock_on N0 n0 n1 ->
      net_lock_on N1 n0 n1.

    Proof.
      unfold net_lock_on.
      intros.
      hsimpl in *.
      exists L; split; eauto using deadset_invariant_lock, deadlocked_lock_invariant1 with datatypes.
    Qed.

    #[export] Hint Resolve deadlocked_lock_on_invariant1 | 0 : LTS.


    Lemma lock_chain_nil_inv N n0 n1 : lock_chain N n0 [] n1 <-> net_lock_on N n0 n1.
    Proof. attac. Qed.

    #[export] Hint Rewrite -> lock_chain_nil_inv using assumption : LTS LTS_concl.


    Lemma lock_chain_cons_inv N n0 n1 n2 L : lock_chain N n0 (n1 :: L) n2 <-> net_lock_on N n0 n1 /\ lock_chain N n1 L n2.
    Proof. split; intros. kill H. attac. attac. Qed.

    #[export] Hint Rewrite -> lock_chain_cons_inv using assumption : LTS.


    Lemma lock_chain_split_inv N n0 n2 L0 n1 L1 : L0 <> [] -> lock_chain N n0 (L0 ++ n1 :: L1) n2 <-> lock_chain N n0 L0 n1 /\ lock_chain N n1 L1 n2.
    Proof. attac. Qed.

    #[export] Hint Rewrite -> lock_chain_split_inv using spank : LTS.


    Lemma deadlocked_dep_invariant1 [N0 N1 : PNet] [n0 n1 : Name] [a] :
      (N0 =(a)=> N1) ->
      deadlocked n0 N0 ->
      dep_on N0 n0 n1 ->
      dep_on N1 n0 n1.

    Proof.
      intros.
      have (deadlocked n0 N1).
      apply dep_lock_chain in H1.
      consider (exists L, lock_chain N0 n0 L n1 /\ ~ List.In n1 L).
      enough (lock_chain N1 n0 L n1) by attac.
      generalize dependent N0 N1 n0 n1.
      induction L; intros; hsimpl in *; eauto with LTS.

      constructor; eauto with LTS.

      have (deadlocked a0 N1).

      normalize_hyp @IHL.
      specialize (IHL n1 a0 N1 N0).
      apply IHL; eauto with LTS.
    Qed.

    #[export] Hint Resolve  deadlocked_dep_invariant1 | 0 : LTS.


    Lemma deadlocked_lock_on_invariant [N0 N1 : PNet] [n0 n1 : Name] [path] :
      (N0 =[path]=> N1) ->
      deadlocked n0 N0 ->
      net_lock_on N0 n0 n1 ->
      net_lock_on N1 n0 n1.

    Proof.
      generalize dependent N0.
      induction path; intros; hsimpl in *; attac.
    Qed.

    Hint Resolve deadlocked_lock_on_invariant | 0 : LTS.


    Lemma deadlocked_dep_invariant [N0 N1 : PNet] [n0 n1 : Name] [path] :
      (N0 =[path]=> N1) ->
      deadlocked n0 N0 ->
      dep_on N0 n0 n1 ->
      dep_on N1 n0 n1.

    Proof.
      generalize dependent N0.
      induction path; intros; hsimpl in *. 1: attac.
      Print HintDb LTS.
      assert (dep_on N2 n0 n1) by attac.
      eapply (IHpath N2); eauto with LTS.
    Qed.

    Hint Resolve deadlocked_dep_invariant | 0 : LTS.


    Module Type LOCKS_UNIQ.
      Definition lock_uniq_type N := forall n m0 m1,
          net_lock_on N n m0 ->
          net_lock_on N n m1 ->
          m0 = m1.

      Definition lock_neq_nil_type N := forall L n,
          net_lock N L n ->
          L <> [].

      Definition locks_dec_in N := forall n0 n1,
          net_lock_on N n0 n1 \/ ~ net_lock_on N n0 n1.

      Section Static.
        Variable (N : PNet).

        Hypothesis lock_uniq : lock_uniq_type N.
        Hypothesis lock_neq_nil : lock_neq_nil_type N.

        Hint Transparent lock_uniq_type lock_neq_nil_type locks_dec_in : core LTS.
        Hint Unfold lock_uniq_type lock_neq_nil_type locks_dec_in : core LTS.
        Hint Resolve lock_uniq lock_neq_nil : LTS.

        Local Lemma lock_nil_bs [n] : net_lock N [] n -> False.
        Proof. unfold lock_neq_nil_type in *. bullshit. Qed.

        Hint Immediate lock_nil_bs : bullshit.


        Lemma net_get_lock [L n0] :
          net_lock N L n0 ->
          exists n1, net_lock N [n1] n0.

        Proof with eattac.
          intros HL.
          destruct L as [|n1]; doubt.
          exists n1.
          unfold net_lock in *.
          enough (incl (n1::L) [n1]) by (enough (incl [n1] (n1::L)); attac).

          attac.
        Qed.

        Hint Resolve net_get_lock : LTS.


        Lemma net_get_lock_In [L n0 n1] :
          List.In n1 L ->
          net_lock N L n0 ->
          net_lock N [n1] n0.

        Proof with eattac.
          intros.

          consider (exists n2, net_lock N [n2] n0) by eauto using net_get_lock.
          assert (net_lock_on N n0 n1)...
          assert (net_lock_on N n0 n2)...
          assert (n1 = n2)...
        Qed.

        Hint Immediate net_get_lock_In : LTS.


        Lemma lock_singleton [n0 n1] :
          net_lock_on N n0 n1 ->
          net_lock N [n1] n0.

        Proof with eattac.
          intros.
          consider (net_lock_on N n0 n1).
          eattac.
        Qed.

        Hint Immediate lock_singleton : LTS.


        Lemma deadlocked_lock_on' [n0 : Name] [n1 : Name] :
          deadlocked n1 N ->
          net_lock_on N n0 n1 ->
          deadlocked n0 N.

        Proof.
          intros.
          eauto with LTS.
        Qed.

        Hint Immediate deadlocked_lock_on' : LTS.


        Lemma deadlocked_dep' [n0 : Name] [n1 : Name] :
          deadlocked n1 N ->
          dep_on N n0 n1 ->
          deadlocked n0 N.

        Proof.
          intros.
          induction H0; attac.
        Qed.

        Hint Resolve deadlocked_dep' : LTS.


        (** If you are dependent on yourself, then anything you are locked on is dependent on you
         *)
        Lemma dep_loop1 [n0 n1] :
          dep_on N n0 n0 ->
          net_lock_on N n0 n1 ->
          dep_on N n1 n0.

        Proof with eattac.
          intros.
          consider (dep_on _ _ _).
          - consider (n0 = n1); attac.
          - consider (n1 = n2); attac.
        Qed.

        Hint Resolve dep_loop1 : LTS.


        (** If you are dependent on yourself, then anything you are dependent on is dependent on
      you *)
        Theorem dep_loop [n0 n1] :
          dep_on N n0 n0 ->
          dep_on N n0 n1 ->
          dep_on N n1 n0.

        Proof with eattac.
          intros H0 H1.

          induction H1.
          apply dep_loop1; eauto.

          specialize (dep_loop1 H0 H) as HD1.

          enough (dep_on N n1 n1).

          apply IHdep_on in H2.
          eapply dep_on_seq; eauto.

          eapply dep_on_seq1'; eauto.
        Qed.

        Hint Resolve dep_loop : LTS.


        (** If you are dependent on yourself, then anything you are dependent on is dependent on
      itself. *)
        Lemma dep_reloop [n m] :
          dep_on N n n ->
          dep_on N n m ->
          dep_on N m m.

        Proof with eattac.
          intros HLnn HLnm.
          specialize (dep_loop HLnn HLnm) as HLmn.
          apply (dep_on_seq HLmn HLnm).
        Qed.

        Hint Resolve dep_reloop : LTS.


        (** If you are locked on yourself, then all members of your lock set are locked on themselves
         *)
        Lemma dep_set_reloop [L n m] :
          dep_set N L n ->
          dep_on N n n ->
          List.In m L ->
          dep_on N m m.

        Proof with eattac.
          intros HDS HLnn HIn.
          apply HDS in HIn.
          eapply dep_reloop...
        Qed.

        Hint Immediate dep_set_reloop : LTS.


        (** If you are directly locked on yourself then you are dependent only on yourself *)
        Lemma lock_self_dep_uniq [n m] :
          net_lock_on N n n ->
          dep_on N n m ->
          m = n.

        Proof with eattac.
          intros HLnn HLnm.

          induction HLnm.
          1: { attac. }

          consider (n0 = n1) by attac.
        Qed.

        Hint Resolve lock_self_dep_uniq : LTS.
        Hint Rewrite lock_self_dep_uniq using assumption : LTS.


        (** If you are directly locked on yourself and have a lock chain, then that chain consists of
      only you and ends at yourself *)
        Lemma lock_self_lock_chain_uniq [n0 n1 L] :
          net_lock_on N n0 n0 ->
          lock_chain N n0 L n1 ->
          Forall (eq n0) L /\ n1 = n0.

        Proof with eattac.
          intros HL HLc.
          induction HLc.
          - attac.
          - consider (n0 = n1) by attac.
            consider (Forall (eq n1) l /\ n2 = n1).
        Qed.


        (** Same lock chains with same starting points always end in the same node *)
        Lemma lock_chain_target [n0 n1 n2 L] :
          lock_chain N n0 L n1 ->
          lock_chain N n0 L n2 ->
          n1 = n2.

        Proof with eattac.
          intros HLc0 HLc1.

          generalize dependent n0.
          generalize dependent n1.
          generalize dependent n2.
          induction L; intros; kill HLc0; kill HLc1...
        Qed.


        (** If you can reach closer or further, then you can reach further from closer (?) *)
        Lemma lock_chain_break [n0 n1 n2 L0 L1] :
          lock_chain N n0 L0 n1 ->
          lock_chain N n0 (L0 ++ L1) n2 ->
          L1 = [] \/ exists L1', L1 = n1 :: L1' /\ lock_chain N n1 L1' n2.

        Proof with eattac.
          intros HLc0 HLc1.

          generalize dependent n0.
          generalize dependent n1.
          generalize dependent n2.
          generalize dependent L1.
          induction L0; intros; simpl in *.
          - kill HLc0.
            consider (lock_chain _ _ _ _).
            consider (n4 = n1) by attac.
            attac.
          - kill HLc0.
            kill HLc1...
        Qed.


        (** If two lock chains start in the same place, one must be a prefix of another *)
        Lemma lock_chain_prefix [n0 n1 n2 L0 L1] :
          lock_chain N n0 L0 n1 ->
          lock_chain N n0 L1 n2 ->
          exists L', L0 = L1 ++ L' \/ L1 = L0 ++ L'.

        Proof with eattac.
          intros HLc0 HLc1.

          generalize dependent n0.
          generalize dependent n1.
          generalize dependent n2.
          generalize dependent L1.
          induction L0; intros.
          - kill HLc1...
          - kill HLc0.
            kill HLc1. { exists (a::L0)... }

            assert (n4 = a) by attac. subst.
            edestruct IHL0 as [L' [HEq|HEq]]; eauto with LTS.
            + exists L'; subst...
            + exists L'; subst...
        Qed.


        (** If there is a looped lock chain, then any reachable node can reach you back *)
        Lemma lock_chain_reloop [n0 n1 L0 L1] :
          lock_chain N n0 L0 n0 ->
          lock_chain N n0 L1 n1 ->
          exists L2, lock_chain N n1 L2 n1.

        Proof with eauto.
          intros HLc0 HLc1.
          apply lock_chain_dep in HLc0.
          apply lock_chain_dep in HLc1.
          apply dep_reloop in HLc1...

          apply dep_lock_chain in HLc1 as [L2 [H _]]...
        Qed.


        (** If there is a looped chain, then any member of any chain with the same start is also a
      member of the loop *)
        Lemma lock_chain_loop_in [n0 n1 L0 L1] :
          lock_chain N n0 L0 n0 ->
          lock_chain N n0 L1 n1 ->
          List.In n1 L0 \/ n1 = n0.

        Proof with eattac.
          intros HLc0 HLc1.

          apply lock_chain_dedup in HLc1 as (L1' & HLc1 & _ & _ & HIn).
          clear L1.
          rename L1' into L1.

          smash_eq n0 n1; auto.
          left.

          kill HLc0.
          {
            apply HEq.
            eapply lock_self_lock_chain_uniq; eauto.
          }

          smash_eq n3 n1; attac.

          consider (lock_chain _ n0 L1 n1); attac.
          consider (n3 = n4) by attac.

          rename l into L0.
          rename l0 into L1.
          rename n0 into n2.
          rename n4 into n0.

          destruct (lock_chain_prefix H0 H2) as [L' [HEq'|HEq']]; subst.
          - apply in_or_app. right.
            clear H1.

            apply dep_on_Direct in H.

            generalize dependent L'.
            generalize dependent n0.
            generalize dependent n2.
            ltac1:(dependent induction L1); intros; simpl in *.
            + kill H2.
              consider (lock_chain _ n0 L' _); attac.
            + consider (lock_chain _ n0 (a :: L1) _).
              consider (lock_chain _ n0 (a :: L1 ++ L') _).
              hsimpl in *.
              eapply IHL1 with (n0:=a) (n2:=n2); auto.
              eauto with LTS.
          - exfalso.

            specialize (lock_chain_break H0 H2) as [HEq' | [L [HEq' HLc]]]; subst.
            { rewrite app_nil_r in *.
              rewrite (lock_chain_target H0 H2) in *.
              bullshit.
            }
            clear H2.

            apply lock_chain_dedup in HLc as (L1 & HLc1 & _ & HIn0' & HIn0''); subst.

            consider (lock_chain _ _ L1 n1); attac 2.
            consider (n4 = n0) by attac.

            rename l into L1.
            clear HEq0.
            clear H1.
            clear H2.

            specialize (lock_chain_prefix H0 `(_)) as [L'' [HEq'|HEq']]; subst.
            + apply dep_on_Direct in H.

              generalize dependent n0.
              generalize dependent n1.
              generalize dependent n2.

              induction L1; intros; simpl in *.
              * hsimpl in *.
                consider (lock_chain _ n0 L'' _) by attac.
                -- consider (n2 = n1) by attac.
                -- consider (n4 = n0) by attac.
                   attac.
              * consider (lock_chain _ _ (_ :: _) _).
                consider (lock_chain _ _ (_ :: _) _).
                hsimpl in *.
                eapply IHL1 with (n2:=n2)(n1:=n1)(n0:=a); auto.
                attac.
            + apply dep_on_Direct in H.

              generalize dependent n0.
              generalize dependent n1.
              generalize dependent n2.

              induction L0; intros; simpl in *.
              * kill H0.
                consider (lock_chain _ _ _ _); attac.
              * hsimpl in *.
                apply IHL0 with (n0:=a)(n1:=n1)(n2:=n2); auto.
                attac.
        Qed.


        (** If there is a loop, then any reachable node can finish the loop *)
        Corollary lock_chain_loop [n0 n1 L0 L1] :
          lock_chain N n0 L0 n0 ->
          lock_chain N n0 L1 n1 ->
          exists L2, lock_chain N n1 L2 n0.

        Proof.
          intros HLc0 HLc1.

          apply lock_chain_dedup in HLc1 as (L1' & HLc1 & _ & _ & HIn1''); subst.

          destruct (lock_chain_loop_in HLc0 HLc1); subst.
          2: eapply lock_chain_reloop in HLc1; eauto.

          destruct (lock_chain_prefix HLc0 HLc1) as [L' [HEq|HEq]]; subst.
          - destruct (lock_chain_break HLc1 HLc0) as [HEq| [L2 [HIn HL]]]; subst.
            + rewrite app_nil_r in *.
              rewrite (lock_chain_target HLc0 HLc1) in *.
              eapply lock_chain_reloop in HLc1; eauto.
            + exists L2; eauto.
          - exfalso.
            eauto with datatypes.
        Qed.


        (** If there is a loop, then the loop is a depset *)
        Corollary dep_loop_dep_set [n0 L] :
          lock_chain N n0 L n0 ->
          dep_set N (n0::L) n0.

        Proof with attac.
          intros HLc.

          constructor; intros.
          { kill HLc.
            - kill H...
            - repeat (destruct H).
              eauto using lock_chain_dep with LTS.
              eauto using lock_chain_dep with LTS.
              apply (lock_chain_split_in H) in H1 as (L0 & L1 & HEq & HLc1 & LCa).
              eauto using lock_chain_dep with LTS.
          }

          eapply (dep_lock_chain) in H as [L' [HLc' HIn']]; auto.

          destruct (lock_chain_loop_in HLc HLc'); subst; attac.
        Qed.

        Hint Resolve dep_loop_dep_set : LTS.


        (** If you depend on a loop, then the loop and the path form a depset *)
        Corollary dep_on_loop_dep_set [n0 n1 L0 L1] :
          lock_chain N n0 L0 n1 ->
          lock_chain N n1 L1 n1 ->
          dep_set N (L0 ++ n1::L1) n0.

        Proof with eattac.
          intros HLc0 HLc1.

          smash_eq n0 n1.
          {
            specialize (lock_chain_seq HLc0 HLc1) as HLc.
            eapply dep_loop_dep_set in HLc.
            constructor; intros.
            - unfold dep_set in *.
              apply HLc.
              auto 10 with datatypes.
            - apply HLc in H.
              destruct H; subst; eauto with datatypes.
          }

          constructor; intros.
          - apply in_app_or in H as [HIn|HIn].
            + destruct (lock_chain_split_in HIn HLc0) as (L0' & L1' & HEq' & HLc0' & HLc1').
              eapply lock_chain_dep; eauto.
            + kill HIn; auto.
              eapply lock_chain_dep; eauto.
              specialize (lock_chain_seq HLc0 HLc1) as HLc.
              assert (List.In m (L0 ++ n1 :: L1)) as HIn by eauto with datatypes.
              apply (lock_chain_split_in HIn) in HLc as (L0' & L1' & HEq' & HLc0' & HLc1').
              eapply lock_chain_dep; eauto.
          - generalize dependent L1.
            generalize dependent n1.
            generalize dependent n0.
            generalize dependent m.
            induction L0; intros; simpl in *.
            + smash_eq m n1; auto.
              kill HLc0.
              apply dep_lock_chain in H as [L' [HLc' HIn']].
              consider (lock_chain _ n0 _ _); attac.

              consider (n3 = n1) by attac.
              assert (In m L1 \/ m = n1) as [|] by eauto using lock_chain_loop_in; attac.

            + kill HLc0.
              smash_eq a m; auto.
              right.

              assert (dep_on N a m) as HD.
              {
                consider (dep_on _ n0 _).
                - bullshit (a = m) by attac.
                - bullshit (a = n2) by attac.
              }

              smash_eq a n1.
              {
                apply dep_lock_chain in HD as [L' [HLc' HIn']].
                destruct (lock_chain_loop_in HLc1 HLc'); subst; eauto with datatypes.
              }

              eapply IHL0; eauto.
        Qed.


        (** If you depend on a process with no lock, then the lock chain forms a depset *)
        Lemma dep_on_noloop_dep_set [n0 n1 L] :
          lock_chain N n0 L n1 ->
          (forall n2, ~ net_lock_on N n1 n2) ->
          dep_set N (n1::L) n0.

        Proof.
          intros HLc HNoL.

          constructor; intros.
          - destruct H as [HIn|HIn]; subst.
            + eapply lock_chain_dep; eauto.
            + apply (lock_chain_split_in HIn) in HLc as (L0' & L1' & HEq' & HLc0' & HLc1').
              eapply lock_chain_dep; eauto.
          - generalize dependent n1.
            generalize dependent n0.
            generalize dependent m.
            induction L; intros; simpl in *.
            + smash_eq m n1; auto.
              kill HLc.
              kill H.
              * consider (m = n1) by attac.
              * consider (n1 = n2) by attac.
                consider (dep_on _ n2 _); bullshit.
            + kill HLc.
              smash_eq a m; auto.

              assert (dep_on N a m) as HD.
              {
                consider (dep_on _ _ _).
                - bullshit (a = m).
                - consider (a = n2) by attac.
              }

              edestruct IHL; eauto.
        Qed.


        (** If a node is a member of its dep set, then this set is a deadset *)
        Lemma dep_set_deadset [DS n] :
          List.In n DS ->
          dep_set N DS n ->
          DeadSet DS N.

        Proof with attac.
          intros HIn HI.

          constructor.
          1: destruct DS...
          intros n' HIn'.

          apply HI in HIn as HL.
          apply HI in HIn' as HL'.

          apply dep_reloop in HL' as HLr; auto.

          ltac1:(dependent destruction HLr).
          - destruct H as [Lr' [HIn'r HLc'r]].

            apply (net_get_lock_In HIn'r) in HLc'r...
            exists [n']...

          - destruct H as [Lr' [HIn'r HLc'r]].

            apply (net_get_lock_In HIn'r) in HLc'r...
            exists [n1]...

            enough (dep_on N n' a).
            {
              assert (dep_on N n a) as Hx by eauto 2 with LTS.
              apply dep_lock_chain in Hx. hsimpl in Hx. eauto.
              eapply lock_chain_dep_set_In; eauto.
            }

            enough (net_lock_on N n' a) by attac.
            attac.
        Qed.

        Hint Resolve dep_set_deadset : LTS.


        (** If there is anyone dependent on itself, then it is a member of a deadset *)
        Corollary dep_self_deadset [n] :
          dep_on N n n ->
          exists DS, List.In n DS /\ DeadSet DS N.

        Proof with eattac.
          intros HL.

          destruct (dep_lock_chain HL) as [L [HLc HIn]]...
        Qed.


        Section Dec.
          Hypothesis net_lock_on_dec : locks_dec_in N.

          Lemma dep_set_lock_on_dec [m n D] :
            dep_set N D m ->
            List.In n D ->
            (exists n', net_lock_on N n n') \/ forall n', ~ net_lock_on N n n'.

          Proof.
            intros.

            remember ([] : list Name) as D_past.
            rename D into D_next.
            replace (D_next) with (D_past ++ D_next) in H by attac.

            assert (forall m', In m' D_next -> dep_on N m m') by (intros; apply `(dep_set _ _ _); attac).
            assert (forall m', dep_on N m m' -> In m' D_past \/ In m' D_next).
            {
              assert (forall m', dep_on N m m' -> In m' (D_past ++ D_next)) by (intros; apply `(dep_set _ _ _); attac).
              attac.
            }
            assert (forall n', In n' D_past -> ~ net_lock_on N n n') by attac.

            assert (dep_on N m n) by attac.

            clear HeqD_past H0.

            generalize dependent D_past.
            induction D_next; intros.
            1: { right; attac. }

            destruct (net_lock_on_dec n a).
            1: { attac. }

            specialize IHD_next with (D_past := D_past ++ [a]).
            destruct IHD_next; intros; auto with LTS.
            - attac.
            - rewrite <- app_assoc. simpl in *; auto.
            - assert (In m' D_past \/ In m' (a :: D_next)) as [|[|]] by auto; attac.
            - smash_eq a n'; attac.
          Qed.


          Lemma dep_set_lock_set_dec [n0 L0 n1] :
            dep_set N L0 n0 ->
            List.In n1 L0 ->
            (exists L1, net_lock N L1 n1) \/ (forall n2, ~ net_lock_on N n1 n2).

          Proof.
            intros HD HIn.
            destruct (dep_set_lock_on_dec HD HIn) as [[n2 HL]|HNL].
            - left; eattac.
            - right; eattac.
          Qed.


          (** For any depset, there is a lock chain that completely covers it *)
          Lemma longest_lock_chain [n0 D] :
            dep_set N D n0 ->
            D <> [] ->
            exists n1 L, lock_chain N n0 L n1 /\ incl D (n1::L).

          Proof.
            intros HD HDnil.

            enough (exists n1 L, lock_chain N n0 L n1 /\ forall n2, net_lock_on N n1 n2 -> List.In n2 (n0::n1::L))
              as (n1 & L & HL & HIn).
            {
              assert (List.In n1 D) as HIn1 by (apply HD; eattac).

              destruct (dep_set_lock_set_dec HD HIn1) as [[D1 HD1]|HNL].
              {
                apply net_get_lock in HD1 as [n2 HD1].
                specialize (HIn n2) as [HEq2 | [HEq2 | HIn2]]; eauto with LTS datatypes; subst.
                - exists n2, (L ++ [n1]).
                  assert (lock_chain N n2 (L ++ [n1]) n2) as HLc by eattac.
                  split; auto.
                  eapply dep_loop_dep_set in HLc.
                  eapply dep_set_incl; eauto.
                - assert (net_lock_on N n2 n2) as HD2 by eattac.
                  exists n2, L.
                  split; eauto.
                  assert (lock_chain N n2 [] n2) as HLc1 by eattac.
                  specialize (dep_on_loop_dep_set HL HLc1) as HD'.
                  assert (incl (L ++ [n2]) (n2::L)) by eauto with datatypes.
                  apply (dep_set_incl HD) in HD'.
                  eapply incl_tran; eauto.
                - assert (lock_chain N n1 [] n2) as HLc1 by eattac.
                  destruct (lock_chain_split_in HIn2 HL) as (L0 & L2 & HEq' & HLc0 & HLc2); subst.
                  assert (lock_chain N n1 (n2::L2) n1) as HLc1' by eattac.
                  subst.

                  specialize (dep_on_loop_dep_set HL HLc1') as HD'.
                  exists n1, (L0 ++ n2 :: L2).
                  split; auto.

                  repeat (rewrite <- app_assoc in * ).
                  repeat (rewrite <- app_comm_cons in * ).
                  assert (incl (L0 ++ n2 :: L2 ++ n1 :: n2 :: L2) (L0 ++ [n2] ++ L2 ++ [n1] ++ [n2] ++ L2)) by eauto with datatypes.
                  assert (incl (L0 ++ [n2] ++ L2 ++ [n1] ++ [n2] ++ L2) ([n1] ++ L0 ++ [n2] ++ L2)) by auto 8 with datatypes.
                  assert (incl  ([n1] ++ L0 ++ [n2] ++ L2) (n1 :: L0 ++ n2 :: L2)) by attac.
                  apply (dep_set_incl HD) in HD'.
                  eapply incl_tran; eauto.
              }

              specialize (dep_on_noloop_dep_set HL HNL) as HD'.
              exists n1, L.
              split; eauto with LTS.
            }

            assert (exists n1 L, lock_chain N n0 L n1) as [n1 [L HL]].
            {
              destruct D.
              1: bullshit.
              assert (List.In n (n :: D)) as HIn by attac.
              apply HD in HIn as HDep.
              exists n.
              apply dep_lock_chain in HDep as [L [HL _]].
              eattac.
            }
            assert (forall n2, dep_on N n0 n2 -> List.In n2 (n0::L ++ D)) as Hseen.
            {
              intros.
              right.
              apply in_or_app; right.
              apply HD; auto.
            }
            assert (forall n, List.In n D -> dep_on N n0 n) as HD' by apply HD.

            assert (forall n, List.In n D -> (exists n', net_lock_on N n n') \/ forall n', ~ net_lock_on N n n') as Hlock_dec
                by (intros; eapply dep_set_lock_on_dec; eauto).

            clear HD.
            clear HDnil.

            generalize dependent n1 L.
            ltac1:(dependent induction D); intros.
            {
              rewrite app_nil_r in *.
              destruct (Hseen n1 ltac:(eattac)); subst.
              - exists n1, L.
                split; attac.
              - exists n1, (L).
                split; auto.
                intros.
                specialize (Hseen n2 ltac:(eattac)).
                kill Hseen; attac.
            }

            specialize (IHD ltac:(eattac)).

            specialize (HD' a ltac:(attac)).
            apply dep_lock_chain in HD' as [La [HLa HNIn]].


            smash_eq n0 a.
            {
              exists n0, La.
              split; auto.
              intros.
              eapply dep_loop_dep_set in HLa.
              assert (List.In n2 (n0 :: La)) by (apply HLa; attac).
              attac.
            }
            rename HEq into HNeq.

            specialize (IHD ltac:(attac)).

            destruct (lock_chain_prefix HL HLa) as [[|a' L'] [HEq|HEq]]; subst; try (rewrite app_nil_r in * ).
            - specialize (lock_chain_target HL HLa) as HEq; subst.
              destruct (Hlock_dec a ltac:(attac)) as [[b Ha]|?].
              + smash_eq a b.
                * exists a, La.
                  split; auto.
                  intros.
                  consider (a = n2) by attac.
                  attac.
                * specialize (IHD (La ++ [a])).
                  repeat (rewrite <- app_assoc in * ).
                  simpl in *.
                  specialize (IHD Hseen).
                  specialize (IHD b).
                  apply IHD.
                  apply lock_chain_seq1'; auto.
              + exists a, La.
                split; eauto.
                intros; bullshit.
            - specialize (lock_chain_target HL HLa) as HEq; subst.
              destruct (Hlock_dec a ltac:(attac)) as [[b Ha]|?].
              + smash_eq a b.
                * exists a, L.
                  split; auto.
                  intros.
                  consider (n2 = a); attac.
                * specialize (IHD (L ++ [a])).
                  repeat (rewrite <- app_assoc in * ).
                  simpl in *.
                  specialize (IHD Hseen).
                  specialize (IHD b).
                  apply IHD.
                  apply lock_chain_seq1'; auto.
              + exists a, L.
                split; eauto.
                intros; bullshit.
            - apply lock_chain_split in HL as [HL0 HL1].
              rewrite (lock_chain_target HL0 HLa) in *; clear HL0.
              specialize (IHD (La ++ a :: L')).
              repeat (rewrite <- app_assoc in * ).
              simpl in *.

              assert (lock_chain N n0 (La ++ a :: L') n1) as HL0 by attac.
              unshelve eapply (IHD _ _ HL0).
              intros.
              apply Hseen in H as [?|?]; eauto with datatypes.
              right.
              apply in_app_or in H as [?|?] > [|]; attac.
              kill H; attac.
              destruct `(_ \/ _) as [|[]]; attac.
            - apply lock_chain_split in HLa as [HL0 HL1].
              rewrite (lock_chain_target HL0 HL) in *; clear HL0.

              destruct (Hlock_dec a ltac:(attac)) as [[b Ha]|?].
              + smash_eq a b.
                * exists a, (L ++ n1 :: L').
                  split; hsimpl; attac.
                * specialize (IHD (L ++ n1 :: L' ++ [a])).
                  repeat (rewrite <- app_assoc in * ).
                  simpl in *.

                  assert (lock_chain N n0 (L ++ n1 :: L' ++ [a]) b) as HL0 by attac.
                  unshelve (eapply (IHD _ _ HL0)).
                  intros n2 HD2.
                  specialize (Hseen _ HD2).
                  destruct Hseen; eauto.
                  right.
                  apply in_app_or in H as [?|?]; attac.
                  kill H; hsimpl; attac 10.
              + exists a, (L ++ n1 :: L').
                split; attac.
          Qed.


          (** In any deadset, someone is dependent on itself *)
          Corollary deadset_dep_self [DS] :
            DeadSet DS N ->
            exists n, List.In n DS /\ dep_on N n n.

          Proof with eattac.
            intros HDS.

            assert (exists n0, List.In n0 DS) as [n0 HIn]
                by (kill HDS; destruct DS; doubt; exists n; attac).

            destruct (deadset_dep_set HDS HIn) as [L HL].

            assert (L <> []) as HLnil.
            {
              destruct L; doubt.
              destruct (deadset_net_lock HDS HIn) as [L' [HL' _]].
              apply net_get_lock in HL' as [n' HL'].
              unfold dep_set in HL.
              assert (net_lock_on N n0 n') by attac.
              assert (dep_on N n0 n') as HD' by attac.
              apply HL in HD'.
              bullshit.
            }

            specialize (deadset_dep_set_deadset HDS HL HLnil HIn) as HDSL.

            destruct (longest_lock_chain HL) as (n2 & Lc & HLc & Hincl); eauto.

            enough (dep_on N n2 n2) by eauto with LTS.

            enough (exists n1, List.In n1 (n2::Lc) /\ dep_on N n2 n1) as [n1 [HIn1 HD1]].
            {
              kill HIn1.
              eapply (lock_chain_split_in H) in HLc
                  as (L0 & L1 & HEq & HLc0 & HLc1).
              apply lock_chain_dep in HLc1.
              eauto with LTS.
            }

            assert (List.In n2 L) as HIn2 by (apply HL; eapply lock_chain_dep; eauto).

            assert (exists n1, net_lock_on N n2 n1) as [n1 HL1].
            {
              apply (deadset_net_lock HDSL) in HIn2 as [L2 [HL2 _]].
              apply net_get_lock in HL2 as [n1 HL2].
              exists n1.
              eattac.
            }

            exists n1; split; auto with LTS.

            enough (List.In n1 L) by attac.

            eapply deadset_in; eauto.
          Qed.
        End Dec.
      End Static.


      Section Dynamic.
        Variable N0 N1 : PNet.

        Theorem net_lock_no_send [L n0 m0 m1 t v] :
          net_lock N0 L n0 ->
          (N0 =(NComm m0 m1 t v)=> N1) ->
          n0 <> m0.

        Proof.
          intros.
          intros ?; subst.
          consider (exists L, pq_lock L (NetMod.get m0 N0)) by (unfold net_lock in *; attac).
          consider (exists S, NetMod.get m0 N0 =(send (m1, &t) v)=> S) by (consider (_ =(_)=> _); eattac).
          destruct (NetMod.get m0 N0) as [I0 P0 O0] eqn:?.
          consider (pq_lock _ _).
          bullshit.
        Qed.


        Lemma net_lock_tau_preserve [L n0 n a] :
          (N0 =(NTau n a)=> N1) ->
          net_lock N0 L n0 ->
          net_lock N1 L n0.

        Proof.
          intros.
          unfold net_lock in *.
          smash_eq n0 n.
          - exfalso.
            hsimpl in *.
            eapply pq_lock_recv in H; eauto.
          - replace (NetMod.get n0 N1) with (NetMod.get n0 N0); eattac.
        Qed.


        Lemma net_lock_Q_preserve [L n0 m0 m1 v] :
          (N0 =(NComm m0 m1 Q v)=> N1) ->
          net_lock N0 L n0 ->
          net_lock N1 L n0.

        Proof.
          intros.
          unfold net_lock in *.

          assert (n0 <> m0) by eauto using net_lock_no_send.
          smash_eq n0 m1.
          - hsimpl in *.
            assert (not_unlocking_msg L (Recv (m0, Q) v)) by attac.
            solve_invariant (fun () => auto); auto.

          - replace (NetMod.get n0 N1) with (NetMod.get n0 N0); eattac.
        Qed.


        Lemma net_lock_bad_sender_preserve [L n0 m0 m1 t v] :
          ~ In m1 L ->
          (N0 =(NComm m1 m0 t v)=> N1) ->
          net_lock N0 L n0 ->
          net_lock N1 L n0.

        Proof.
          intros.
          assert (n0 <> m1) by eauto using net_lock_no_send.
          destruct t.
          1: { eauto using net_lock_Q_preserve. }

          unfold net_lock in *.

          smash_eq n0 m0.
          2: { replace (NetMod.get n0 N1) with (NetMod.get n0 N0); eattac. }

          consider (_ =(_)=> _); compat_hsimpl in *.

          eattac.
          consider (pq_lock _ _).
          hsimpl in *.
          constructor; auto.
          intros ? ? ? ?.
          assert (In (n, R, v) &I \/ In (n, R, v) [(m1, R, v0)]) as [|]; eattac.
        Qed.


        Lemma net_lock_bad_receiver_preserve [L n0 m0 m1 t v] :
          n0 <> m0 ->
          net_lock N0 L n0 ->
          (N0 =(NComm m1 m0 t v)=> N1) ->
          net_lock N1 L n0.

        Proof.
          intros.

          assert (n0 <> m1) by eauto using net_lock_no_send.
          unfold net_lock in *.
          hsimpl in *.
          replace (NetMod.get n0 N1) with (NetMod.get n0 N0); eattac.
        Qed.


        Lemma net_lock_reply_unlock [L L' n0 n1 v] :
          In n1 L' ->
          In n1 L ->
          net_lock N0 L n0 ->
          (N0 =(NComm n1 n0 R v)=> N1) ->
          ~ net_lock N1 L' n0.

        Proof.
          repeat (intros ?).
          assert (n0 <> n1) by eauto using net_lock_no_send.
          unfold net_lock in *.
          consider (_ =(_)=> _); hsimpl in *.

          compat_hsimpl in *.
          consider (pq_lock _ _).

          bullshit (In (n1, R, v0) (&I ++ [(n1, R, v0)])).
        Qed.


        Lemma net_unlock_send_inv [L n0 m0 m1 v] :
          net_lock N0 L n0 ->
          ~ net_lock N1 L n0 ->
          (N0 =(NComm m1 m0 R v)=> N1) ->
          In m1 L.

        Proof.
          intros.
          destruct (in_dec NAME.eq_dec m1 L); eauto.
          absurd (net_lock N1 L n0); eauto using eq_sym, net_lock_bad_sender_preserve.
        Qed.


        Lemma net_unlock_recv_inv [L n0 m0 m1 v] :
          net_lock N0 L n0 ->
          ~ net_lock N1 L n0 ->
          (N0 =(NComm m1 m0 R v)=> N1) ->
          m0 = n0.

        Proof.
          intros.
          smash_eq n0 m0.
          absurd (net_lock N1 L n0); eauto using eq_sym, net_lock_bad_receiver_preserve.
        Qed.


        Lemma net_unlock_tag_inv [L n0 m0 m1 t v] :
          net_lock N0 L n0 ->
          ~ net_lock N1 L n0 ->
          (N0 =(NComm m1 m0 t v)=> N1) ->
          t = R.

        Proof.
          intros.
          destruct t; auto.
          absurd (net_lock N1 L n0); eauto using net_lock_Q_preserve.
        Qed.


        Theorem net_unlock_reply [L n0 a] :
          net_lock N0 L n0 ->
          ~ net_lock N1 L n0 ->
          (N0 =(a)=> N1) ->
          exists n1 v, a = NComm n1 n0 R v /\ In n1 L.

        Proof.
          intros.
          destruct a.
          1: { absurd (net_lock N1 L n0); eauto using net_lock_tau_preserve. }

          destruct t.
          1: { absurd (net_lock N1 L n0); eauto using net_lock_Q_preserve. }

          exists n.

          consider (n1 = n0) by eauto using net_unlock_recv_inv.
          assert (In n L) by eauto using net_unlock_send_inv.

          eattac.
        Qed.


        Theorem net_lock_on_no_send [n0 n1 m0 m1 t v] :
          net_lock_on N0 n0 n1 ->
          (N0 =(NComm m0 m1 t v)=> N1) ->
          n0 <> m0.

        Proof.
          intros.
          unfold net_lock_on in *.
          hsimpl in * |-.
          eauto using net_lock_no_send with LTS.
        Qed.


        Lemma net_lock_on_tau_preserve [n0 n1 n a] :
          net_lock_on N0 n0 n1 ->
          (N0 =(NTau n a)=> N1) ->
          net_lock_on N1 n0 n1.

        Proof.
          intros.
          assert (exists L, In n1 L /\ net_lock N0 L n0) as [L [? ?]] by attac.
          exists L.
          eauto using net_lock_tau_preserve.
        Qed.


        Lemma net_lock_on_Q_preserve [n0 n1 m0 m1 v] :
          net_lock_on N0 n0 n1 ->
          (N0 =(NComm m0 m1 Q v)=> N1) ->
          net_lock_on N1 n0 n1.

        Proof.
          intros.
          assert (exists L, In n1 L /\ net_lock N0 L n0) as [L [? ?]] by attac.
          exists L.
          eauto using net_lock_Q_preserve.
        Qed.


        Lemma net_lock_on_bad_receiver_preserve [n0 n1 m0 m1 t v] :
          n0 <> m0 ->
          net_lock_on N0 n0 n1 ->
          (N0 =(NComm m1 m0 t v)=> N1) ->
          net_lock_on N1 n0 n1.

        Proof.
          intros.
          assert (exists L, In n1 L /\ net_lock N0 L n0) as [L [? ?]] by attac.
          exists L.
          eauto using  net_lock_bad_receiver_preserve.
        Qed.


        Lemma net_lock_on_reply_unlock [n0 n1 v] :
          net_lock_on N0 n0 n1 ->
          (N0 =(NComm n1 n0 R v)=> N1) ->
          ~ net_lock_on N1 n0 n1.

        Proof.
          intros.
          intros ?.
          assert (exists L, In n1 L /\ net_lock N0 L n0) as [L [? ?]] by attac.
          assert (exists L', In n1 L' /\ net_lock N1 L' n0) as [L' [? ?]] by attac.
          absurd (net_lock N1 L' n0); eauto using net_lock_reply_unlock with datatypes.
        Qed.


        Lemma net_unlock_on_recv_inv [n0 n1 m0 m1 v] :
          net_lock_on N0 n0 n1 ->
          ~ net_lock_on N1 n0 n1 ->
          (N0 =(NComm m1 m0 R v)=> N1) ->
          m0 = n0.

        Proof.
          intros.
          assert (exists L, In n1 L /\ net_lock N0 L n0) as [L [? ?]] by attac.
          (eapply net_unlock_recv_inv; eattac).
        Qed.


        Lemma net_unlock_on_tag_inv [n0 n1 m0 m1 t v] :
          net_lock_on N0 n0 n1 ->
          ~ net_lock_on N1 n0 n1 ->
          (N0 =(NComm m1 m0 t v)=> N1) ->
          t = R.

        Proof.
          intros.
          assert (exists L, In n1 L /\ net_lock N0 L n0) as [L [? ?]] by attac.
          (eapply net_unlock_tag_inv; eattac).
        Qed.


        Lemma net_dep_tau_preserve [n0 n1 n a] :
          dep_on N0 n0 n1 ->
          (N0 =(NTau n a)=> N1) ->
          dep_on N1 n0 n1.

        Proof.
          intros.
          induction `(dep_on _ _ _).
          - enough (net_lock_on N1 n0 n1) by attac.
            re_have eauto using net_lock_on_tau_preserve.
          - enough (net_lock_on N1 n0 n1 /\ dep_on N1 n1 n2) by attac.
            re_have eauto using net_lock_on_tau_preserve.
        Qed.


        Lemma net_dep_Q_preserve [n0 n1 m0 m1 v] :
          dep_on N0 n0 n1 ->
          (N0 =(NComm m1 m0 Q v)=> N1) ->
          dep_on N1 n0 n1.

        Proof.
          intros.
          induction `(dep_on _ _ _).
          - enough (net_lock_on N1 n0 n1) by attac.
            re_have eauto using net_lock_on_Q_preserve.
          - enough (net_lock_on N1 n0 n1 /\ dep_on N1 n1 n2) by attac.
            re_have eauto using net_lock_on_Q_preserve with LTS.
        Qed.


        (** Receiver is not us and we don't depend on it - we depend on what we depended *)
        Lemma net_dep_bad_receiver_dep_preserve [n0 n1 m0 m1 t v] :
          n0 <> m0 ->
          ~ dep_on N0 n0 m0 ->
          dep_on N0 n0 n1 ->
          (N0 =(NComm m1 m0 t v)=> N1) ->
          dep_on N1 n0 n1.

        Proof.
          intros.
          induction `(dep_on _ _ _).
          - enough (net_lock_on N1 n0 n1) by attac.
            re_have eauto using net_lock_on_bad_receiver_preserve.
          - assert (n1 <> m1) by (consider (dep_on _ n1 _); eauto using net_lock_on_no_send).
            smash_eq m0 n1.
            + eattac 2.
            + enough (net_lock_on N1 n0 n1 /\ dep_on N1 n1 n2) by attac.
              split; re_have eauto using net_lock_on_bad_receiver_preserve with LTS.
        Qed.


        Hypothesis lock_uniq0 : lock_uniq_type N0.
        Hypothesis lock_uniq1 : lock_uniq_type N1.

        Hint Resolve lock_uniq0 lock_uniq1 : LTS.


        Hypothesis lock_neq_nil0 : lock_neq_nil_type N0.
        Hypothesis lock_neq_nil1 : lock_neq_nil_type N1.

        Hint Resolve lock_neq_nil0 lock_neq_nil1 : LTS.


        Lemma net_unlock_on_send_inv [n0 n1 m0 m1 v] :
          net_lock_on N0 n0 n1 ->
          ~ net_lock_on N1 n0 n1 ->
          (N0 =(NComm m1 m0 R v)=> N1) ->
          m1 = n1.

        Proof.
          intros.
          assert (exists L, In n1 L /\ net_lock N0 L n0) as [L [? ?]] by attac.
          assert (In m1 L) by (eapply net_unlock_send_inv; eattac).
          eattac.
        Qed.


        Lemma net_lock_on_bad_sender_preserve [n0 n1 m0 m1 t v] :
          n1 <> m1 ->
          net_lock_on N0 n0 n1 ->
          (N0 =(NComm m1 m0 t v)=> N1) ->
          net_lock_on N1 n0 n1.

        Proof.
          intros.
          exists [n1]. split > [eattac|].
          assert (~ In m1 [n1]) by attac.
          eauto using net_lock_bad_sender_preserve, lock_singleton.
        Qed.


        Theorem net_unlock_on_reply [n0 n1 a] :
          net_lock_on N0 n0 n1 ->
          ~ net_lock_on N1 n0 n1 ->
          (N0 =(a)=> N1) ->
          exists v, a = NComm n1 n0 R v.

        Proof.
          intros.

          enough (exists n' v, a = NComm n' n0 R v /\ In n' [n1]) by eattac.

          enough (net_lock N0 [n1] n0) by (eapply net_unlock_reply; eattac).
          eauto using lock_singleton.
        Qed.


        (** Receiver is not locked on our dependency - we depend on what we depended *)
        Lemma net_dep_bad_receiver_lock_preserve [n0 n1 m0 m1 t v] :
          ~ net_lock_on N0 m0 n1 ->
          dep_on N0 n0 n1 ->
          (N0 =(NComm m1 m0 t v)=> N1) ->
          dep_on N1 n0 n1.

        Proof.
          intros.

          induction `(dep_on _ _ _).
          - smash_eq n0 m0.
            enough (net_lock_on N1 n0 n1) by attac.
            eauto using net_lock_on_bad_receiver_preserve.
          - assert (n1 <> m1) by (consider (dep_on _ n1 _); eauto using net_lock_on_no_send).
            enough (net_lock_on N1 n0 n1 /\ dep_on N1 n1 n2) by attac 2.
            re_have eauto using net_lock_on_bad_sender_preserve with LTS.
        Qed.


        Lemma net_dep_bad_sender_preserve [n0 n1 m0 m1 t v] :
          m1 <> n1 ->
          dep_on N0 n0 n1 ->
          (N0 =(NComm m1 m0 t v)=> N1) ->
          dep_on N1 n0 n1.

        Proof.
          intros.
          induction `(dep_on _ _ _).
          - enough (net_lock_on N1 n0 n1) by attac.
            re_have eauto using net_lock_on_bad_sender_preserve.
          - assert (n1 <> m1) by (consider (dep_on _ n1 _); eauto using net_lock_on_no_send).
            enough (net_lock_on N1 n0 n1 /\ dep_on N1 n1 n2) by attac.
            re_have eauto using net_lock_on_bad_sender_preserve with LTS.
        Qed.


        Lemma net_unlock_on_tip [n0 n1 n2 a] :
          net_lock_on N0 n0 n1 ->
          net_lock_on N0 n1 n2 ->
          (N0 =(a)=> N1) ->
          net_lock_on N1 n0 n1.

        Proof.
          intros.
          destruct a.
          1: { eauto using net_lock_on_tau_preserve. }

          smash_eq n1 n.
          2: { eauto using net_lock_on_bad_sender_preserve. }

          bullshit (n1 <> n1) by eauto using net_lock_on_no_send.
        Qed.


        Lemma net_unlock_on_dep_tip [n0 n1 n2 a] :
          net_lock_on N0 n0 n1 ->
          dep_on N0 n1 n2 ->
          (N0 =(a)=> N1) ->
          net_lock_on N1 n0 n1.

        Proof.
          intros.
          consider (dep_on N0 n1 n2); eauto using net_unlock_on_tip.
        Qed.


        Lemma net_undep_lock_on_tip [n0 n1 n2 a] :
          dep_on N0 n0 n1 ->
          net_lock_on N0 n1 n2 ->
          (N0 =(a)=> N1) ->
          dep_on N1 n0 n1.

        Proof.
          intros.
          induction `(dep_on _ _ _).
          - enough (net_lock_on N1 n0 n1) by attac.
            eauto using net_unlock_on_tip.
          - assert (net_lock_on N1 n0 n1) by eauto using net_unlock_on_dep_tip.
            eattac.
        Qed.


        Lemma net_undep_tip [n0 n1 n2 a] :
          dep_on N0 n0 n1 ->
          dep_on N0 n1 n2 ->
          (N0 =(a)=> N1) ->
          dep_on N1 n0 n1.

        Proof.
          intros.
          induction `(dep_on N0 n1 n2); eauto using net_undep_lock_on_tip.
        Qed.


        Lemma net_unlock_on_tip_right [n0 n1 n2 a] :
          net_lock_on N0 n0 n1 ->
          net_lock_on N0 n1 n2 ->
          ~ dep_on N1 n0 n2 ->
          (N0 =(a)=> N1) ->
          ~ net_lock_on N1 n1 n2.

        Proof.
          intros.

          assert (net_lock_on N1 n0 n1) by eauto using net_unlock_on_tip.
          intros ?; bullshit.
        Qed.


        Lemma net_unlock_on_dep_tip_right [n0 n1 n2 a] :
          net_lock_on N0 n0 n1 ->
          dep_on N0 n1 n2 ->
          ~ dep_on N1 n0 n2 ->
          (N0 =(a)=> N1) ->
          ~ dep_on N1 n1 n2.

        Proof.
          intros.

          assert (net_lock_on N1 n0 n1) by eauto using net_unlock_on_dep_tip.
          intros ?; bullshit.
        Qed.


        Lemma net_undep_lock_on_tip_right [n0 n1 n2 a] :
          dep_on N0 n0 n1 ->
          net_lock_on N0 n1 n2 ->
          ~ dep_on N1 n0 n2 ->
          (N0 =(a)=> N1) ->
          ~ net_lock_on N1 n1 n2.

        Proof.
          intros.

          assert (dep_on N1 n0 n1) by eauto using net_undep_lock_on_tip.
          intros ?; bullshit.
        Qed.


        Lemma net_undep_tip_right [n0 n1 n2 a] :
          dep_on N0 n0 n1 ->
          dep_on N0 n1 n2 ->
          ~ dep_on N1 n0 n2 ->
          (N0 =(a)=> N1) ->
          ~ dep_on N1 n1 n2.

        Proof.
          intros.

          assert (dep_on N1 n0 n1) by eauto using net_undep_tip.
          intros ?; bullshit.
        Qed.


        Lemma net_undep_tag_inv [n0 n1 m0 m1 t v] :
          dep_on N0 n0 n1 ->
          ~ dep_on N1 n0 n1 ->
          (N0 =(NComm m1 m0 t v)=> N1) ->
          t = R.

        Proof.
          intros.
          destruct t.
          1: { absurd (dep_on N1 n0 n1); eauto using net_dep_Q_preserve. }

          smash_eq n1 m1.
        Qed.


        Lemma net_undep_recv_inv [n0 n1 n2 m0 m1 t v] :
          dep_on N0 n0 n1 ->
          net_lock_on N0 n1 n2 ->
          ~ dep_on N1 n0 n2 ->
          (N0 =(NComm m1 m0 t v)=> N1) ->
          m0 = n1.

        Proof.
          intros.

          assert (dep_on N1 n0 n1) by eauto using net_undep_lock_on_tip.

          destruct t.
          1: { absurd (dep_on N1 n0 n2); eauto using net_dep_Q_preserve with LTS. }

          assert (~ net_lock_on N1 n1 n2) by (intros ?; bullshit).

          eauto using net_unlock_on_recv_inv.
        Qed.


        Lemma net_undep_send_inv [n0 n1 m0 m1 t v] :
          dep_on N0 n0 n1 ->
          ~ dep_on N1 n0 n1 ->
          (N0 =(NComm m1 m0 t v)=> N1) ->
          m1 = n1.

        Proof.
          intros.

          destruct t.
          1: { absurd (dep_on N1 n0 n1); eauto using net_dep_Q_preserve with LTS. }

          smash_eq n1 m1.
          absurd (dep_on N1 n0 n1); eauto using net_dep_bad_sender_preserve with LTS.
        Qed.


        Lemma net_dep_on_unlock [n0 n1 a] :
          dep_on N0 n0 n1 ->
          ~ dep_on N1 n0 n1 ->
          (N0 =(a)=> N1) ->
          exists n0' v, a = NComm n1 n0' R v /\ (n0' = n0 \/ dep_on N1 n0 n0').

        Proof.
          intros.
          induction `(dep_on N0 n0 n1).
          -  assert (~ net_lock_on N1 n0 n1) by (intros ?; bullshit).
             consider (exists v, a = NComm n1 n0 R v) by eauto using net_unlock_on_reply.
             eattac.
          - smash_eq n0 n1.
            + enough (n2 = n0) by attac.
              eauto 2 using lock_self_dep_uniq with LTS.
            + assert (net_lock_on N1 n0 n1).
              {
                destruct a.
                1: { eauto using net_lock_on_tau_preserve. }
                smash_eq n1 n.
                2: { eauto using net_lock_on_bad_sender_preserve. }

                absurd (n1 <> n1); consider (dep_on _ n1 _); eauto using net_lock_on_no_send.
              }
              assert (~ dep_on N1 n1 n2) by attac.

              consider (exists n0' v, a = NComm n2 n0' R v /\ (n0' = n1 \/ dep_on N1 n1 n0')) by eauto.
              destruct `(_ \/ _); attac.
        Qed.


      End Dynamic.

      #[export] Hint Resolve
        net_get_lock
        net_get_lock_In
        lock_singleton
        deadlocked_dep'
        lock_self_dep_uniq

        (* net_lock_no_send *)
        (* net_lock_tau_preserve *)
        (* net_lock_Q_preserve *)
        (* net_lock_bad_sender_preserve *)
        (* net_lock_bad_receiver_preserve *)

        (* net_lock_on_no_send *)
        (* net_lock_on_tau_preserve *)
        (* net_lock_on_Q_preserve *)
        (* net_lock_on_bad_sender_preserve *)
        (* net_lock_on_bad_receiver_preserve *)
        (* net_lock_on_reply_unlock *)

        (* net_dep_tau_preserve *)
        (* net_dep_Q_preserve *)
        (* net_dep_bad_sender_preserve *)
        (* net_dep_bad_receiver_dep_preserve *)
        (* net_dep_bad_receiver_lock_preserve *)

        (* net_unlock_on_tip *)
        (* net_unlock_on_dep_tip *)
        (* net_undep_lock_on_tip *)
        (* net_undep_tip *)
        (* net_unlock_on_tip_right *)
        (* net_unlock_on_dep_tip_right *)
        (* net_undep_lock_on_tip_right *)
        (* net_undep_tip_right *) (* TODO these cause loops or at least are turbo slow. Divide them smarter *)
        : LTS.

      #[export] Hint Immediate
        deadlocked_lock_on'
        dep_loop1
        dep_loop
        dep_reloop
        dep_set_reloop
        net_unlock_send_inv
        net_lock_reply_unlock (* TODO FIXME why the fuck this causes a loop *)
        : LTS.

      #[export] Hint Rewrite -> lock_self_dep_uniq using assumption : LTS.

      #[export] Hint Rewrite -> net_unlock_recv_inv
                                 net_unlock_tag_inv
                                 net_unlock_on_send_inv
                                 net_unlock_on_recv_inv
                                 net_unlock_on_tag_inv
                                 net_undep_send_inv
                                 net_undep_recv_inv
                                 net_undep_tag_inv
                                 using assumption : LTS LTS_concl.
    End LOCKS_UNIQ.
End NET_LOCKS.
