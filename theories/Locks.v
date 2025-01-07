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


Module Tag <: UsualDecidableSet.
  Inductive Tag_ := Q | R.

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


Module Type LOCKS(Name : UsualDecidableSet)(NetModF : NET).
  Parameter Inline Val : Set.
  Axiom Val_eq_dec : forall (v0 v1 : Val), {v0 = v1} + {v0 <> v1}.

  Module MD <: MODEL_DATA.
    Module NAME := Name.
    Module TAG := Tag.

    Record MProbe : Set := {init : NAME.t'; index : nat}.

    Record MState' :=
      { self : NAME.t'
      ; lock_id : nat
      ; lock : option NAME.t'
      ; waitees : list NAME.t'
      ; deadlock : bool
      }.

    Definition Val := Val.
    Definition MState := MState'.
    Definition Msg := MProbe.
  End MD.

  Notation Name := MD.NAME.t'.

  (** We need to assume that there are _some_ names and values... *)
  Parameter some_name : Name.
  Parameter some_val : Val.

  Notation Names := (list Name).

  Module NetMod := NetModF(MD.NAME).
  Module Net := Net(MD)(NetMod).

  Import Net.Model.

  Notation R := Tag.R.
  Notation Q := Tag.Q.

  Notation PNet := (NetMod.t PQued).

  Module Import LockDefs.

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

    Section Examples.
      Let CoFixpoint echo : Proc :=
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


    (** Service decisiveness *)
    Definition Decisive_q (S : PQued) :=
      match S with
      | pq _ P _ => Decisive P
      end.

    #[export] Hint Transparent Decisive_q : LTS.


    Lemma Decisive_q_inv I P O : Decisive_q (pq I P O) <-> Decisive P.
    Proof. split; intros; eattac. Qed.

    #[export] Hint Rewrite -> Decisive_q_inv using assumption : LTS LTS_concl.
    #[export] Hint Resolve <- Decisive_q_inv : LTS.
    #[export] Hint Immediate Decisive_q_inv : LTS.


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


    (** Process is locked on L when it's waiting for a Reply from some n in L *)
    Definition proc_lock (L : Names) (P : Proc) :=
      match P with
      | PRecv handle => forall n,
          (List.In n L <-> handle (n, R) <> None)
          /\ handle (n, Q) = None
      | _ => False
      end.

    #[export] Hint Transparent proc_lock : LTS.


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
      consider ((In n L <-> handle0 (n, R) <> None) /\ handle0 (n, Q) = None).
      destruct `(Tag).
      - cbv in *; bullshit.
      - enough (handle0 (n, R) <> None) by eattac.
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
      - assert (handle0 (n, R) <> None).
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
      proc_lock (nodup Name.eq_dec L) P.

    Proof.
      intros.
      assert (incl (nodup Name.eq_dec L) L) by (attac; eapply nodup_In; eauto).
      assert (incl L (nodup Name.eq_dec L)) by (attac; eapply nodup_In; eauto).
      eauto using proc_lock_equiv_inv.
    Qed.

    Lemma pq_lock_nodup [L S] :
      pq_lock L S ->
      pq_lock (nodup Name.eq_dec L) S.

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

  End LockDefs.


  Module Import NetLocks.
    Import Net.

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
      destruct (in_dec Name.eq_dec n1 L)...
    Qed.


    (** Remove duplicates from a deadset *)
    Theorem deadset_nodup [N DS] :
      DeadSet DS N ->
      DeadSet (nodup Name.eq_dec DS) N.

    Proof with (auto with datatypes).
      intros HDS.
      kill HDS.
      constructor.
      - destruct DS...
        assert (List.In n ((n::DS)))...
        apply (nodup_In Name.eq_dec) in H.
        destruct (nodup Name.eq_dec (n :: DS))...
      - intros n HIn.
        ltac1:(apply -> (nodup_In Name.eq_dec) in HIn).
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
      specialize (NoDup_nodup Name.eq_dec DS) as HNoDup.
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

      destruct (in_dec Name.eq_dec n (act_particip a)).
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

      destruct (in_dec Name.eq_dec n (act_particip a)).
      - destruct (deadset_recv HDL HInD T i) as (ns & t & v & HEq).
        subst.

        have (N0 =( NComm ns n &t v )=> N1).

        specialize (deadset_no_send' HDL HInD T) as HNeq.
        clear i.

        hsimpl in *.
        ltac1:(autorewrite with LTS in * ).

        unfold net_lock.
        hsimpl in *. hsimpl in |- *.

        consider (&O0 = []) by attac.

        constructor; attac.

        enough (~ List.In (n0, R, v) [(ns, &t, v0)]).
        {
          hsimpl in *.
          consider (List.In (n0, R, v0) I1 \/ List.In (n0, R, v0) [(ns, &t, v)]) by eattac.
          destruct `(_ \/ _); attac.
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
        + destruct (in_dec Name.eq_dec n2 L) as [?|HNIn].
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
        destruct (partition_first (Name.eqb n1) L') eqn:HEqn1.
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
          apply Name.eqb_eq in HEqn.
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
      refine '(partition_last_eq_init_cons_ind Name.eqb _ _ _ _).
      - split; intros.
        apply Name.eqb_eq...
        attac.
      - intros n1 n0 HLc.
        exists []; split...
        constructor.
      - intros a L L0 Hpart HI n0 n1 HLc.
        kill HLc.

        specialize (partition_last_Forall (Name.eqb a) L) as Hl0.
        specialize (partition_last_eq _ _ Hpart) as HEql. subst.
        rewrite Hpart in Hl0.

        rewrite app_nil_r in *.

        specialize (HI a n1) as [L (HLc & HNoDup)]; auto.

        destruct HNoDup as [HNoDup HNIn].
        smash_eq n0 a. exists L...

        destruct (partition_last (Name.eqb n0) L) eqn:HEqn0.
        specialize (partition_last_Forall (Name.eqb n0) L) as Hn0.
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
          apply Name.eqb_eq in HEqL. subst.
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

        specialize (partition_last_Forall (Name.eqb a) L) as Hl0.
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


    Lemma deadlocked_lock_on [N : PNet] [n0 : Channel.Name] [n1 : Name] :
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

    Lemma deadlocked_dep [N : PNet] [n0 : Channel.Name] [n1 : Name] :
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


    Lemma deadlocked_lock' [N : PNet] [n0 : Channel.Name] [n1 : Name] :
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
      consider (exists L : list Channel.Name, lock_chain N0 n0 L n1 /\ ~ List.In n1 L).
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

  End NetLocks.
End LOCKS.


Module Locks(Name : UsualDecidableSet)(NetModF : NET).
  Include LOCKS(Name)(NetModF).
End Locks.


Module Type LOCKS_UNIQ(Name : UsualDecidableSet)(NetModF : NET).
  Include LOCKS(Name)(NetModF).

  Import NetLocks.
  Import LockDefs.
  Import Net.


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
    Variable N1 : PNet.
    Variable npath : list (@NAct PAct _).

    Hypothesis lock_uniq : lock_uniq_type N1.
    Hypothesis lock_neq_nil : lock_neq_nil_type N1.

    Hint Transparent lock_uniq_type lock_neq_nil_type locks_dec_in : core LTS.
    Hint Unfold lock_uniq_type lock_neq_nil_type locks_dec_in : core LTS.
    Hint Resolve lock_uniq lock_neq_nil : LTS.


    Local Lemma lock_nil_bs [n] : net_lock N1 [] n -> False.
    Proof. unfold lock_neq_nil_type in *. bullshit. Qed.

    Hint Immediate lock_nil_bs : bullshit.


    Lemma net_get_lock [L n0] :
      net_lock N1 L n0 ->
      exists n1, net_lock N1 [n1] n0.

    Proof with eattac.
      intros HL.
      destruct L as [|n1]; doubt.
      exists n1.
      unfold net_lock in *.
      enough (incl (n1::L) [n1]) by (enough (incl [n1] (n1::L)); attac).

      attac.
      destruct `(n1 = a \/ In a L).
      1: { attac. }

      enough (n1 = a) by attac.

      assert (net_lock_on N1 n0 a) by eattac.
      assert (net_lock_on N1 n0 n1) by eattac.
      attac.
    Qed.

    Hint Resolve net_get_lock : LTS.


    (** In an SRPC network, any member of a lock set is the lock set *)
    Lemma net_get_lock_In [L n0 n1] :
      List.In n1 L ->
      net_lock N1 L n0 ->
      net_lock N1 [n1] n0.

    Proof with eattac.
      intros.

      consider (exists n2, net_lock N1 [n2] n0) by eauto using net_get_lock.
      assert (net_lock_on N1 n0 n1)...
      assert (net_lock_on N1 n0 n2)...
      assert (n1 = n2)...
    Qed.

    Hint Immediate net_get_lock_In : LTS.


    Lemma lock_singleton [n0 n1] :
      net_lock_on N1 n0 n1 ->
      net_lock N1 [n1] n0.

    Proof with eattac.
      intros.
      consider (net_lock_on N1 n0 n1).
      eattac.
    Qed.

    Hint Immediate lock_singleton : LTS.


    Lemma deadlocked_lock_on' [n0 : Channel.Name] [n1 : Name] :
      deadlocked n1 N1 ->
      net_lock_on N1 n0 n1 ->
      deadlocked n0 N1.

    Proof.
      intros.
      eauto with LTS.
    Qed.

    Hint Immediate deadlocked_lock_on' : LTS.


    Lemma deadlocked_dep' [n0 : Channel.Name] [n1 : Name] :
      deadlocked n1 N1 ->
      dep_on N1 n0 n1 ->
      deadlocked n0 N1.

    Proof.
      intros.
      induction H0; attac.
    Qed.

    Hint Resolve deadlocked_dep' : LTS.


    (** If you are dependent on yourself, then anything you are locked on is dependent on you
     *)
    Lemma dep_loop1 [n0 n1] :
      dep_on N1 n0 n0 ->
      net_lock_on N1 n0 n1 ->
      dep_on N1 n1 n0.

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
      dep_on N1 n0 n0 ->
      dep_on N1 n0 n1 ->
      dep_on N1 n1 n0.

    Proof with eattac.
      intros H0 H1.

      induction H1.
      apply dep_loop1; eauto.

      specialize (dep_loop1 H0 H) as HD1.

      enough (dep_on N1 n1 n1).

      apply IHdep_on in H2.
      eapply dep_on_seq; eauto.

      eapply dep_on_seq1'; eauto.
    Qed.

    Hint Resolve dep_loop : LTS.


    (** If you are dependent on yourself, then anything you are dependent on is dependent on
      itself. *)
    Lemma dep_reloop [n m] :
      dep_on N1 n n ->
      dep_on N1 n m ->
      dep_on N1 m m.

    Proof with eattac.
      intros HLnn HLnm.
      specialize (dep_loop HLnn HLnm) as HLmn.
      apply (dep_on_seq HLmn HLnm).
    Qed.

    Hint Resolve dep_reloop : LTS.


    (** If you are locked on yourself, then all members of your lock set are locked on themselves
     *)
    Lemma dep_set_reloop [L n m] :
      dep_set N1 L n ->
      dep_on N1 n n ->
      List.In m L ->
      dep_on N1 m m.

    Proof with eattac.
      intros HDS HLnn HIn.
      apply HDS in HIn.
      eapply dep_reloop...
    Qed.

    Hint Immediate dep_set_reloop : LTS.


    (** If you are directly locked on yourself then you are dependent only on yourself *)
    Lemma lock_self_dep_uniq [n m] :
      net_lock_on N1 n n ->
      dep_on N1 n m ->
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
      net_lock_on N1 n0 n0 ->
      lock_chain N1 n0 L n1 ->
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
      lock_chain N1 n0 L n1 ->
      lock_chain N1 n0 L n2 ->
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
      lock_chain N1 n0 L0 n1 ->
      lock_chain N1 n0 (L0 ++ L1) n2 ->
      L1 = [] \/ exists L1', L1 = n1 :: L1' /\ lock_chain N1 n1 L1' n2.

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
      lock_chain N1 n0 L0 n1 ->
      lock_chain N1 n0 L1 n2 ->
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
      lock_chain N1 n0 L0 n0 ->
      lock_chain N1 n0 L1 n1 ->
      exists L2, lock_chain N1 n1 L2 n1.

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
      lock_chain N1 n0 L0 n0 ->
      lock_chain N1 n0 L1 n1 ->
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
      lock_chain N1 n0 L0 n0 ->
      lock_chain N1 n0 L1 n1 ->
      exists L2, lock_chain N1 n1 L2 n0.

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
      lock_chain N1 n0 L n0 ->
      dep_set N1 (n0::L) n0.

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
      lock_chain N1 n0 L0 n1 ->
      lock_chain N1 n1 L1 n1 ->
      dep_set N1 (L0 ++ n1::L1) n0.

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

          assert (dep_on N1 a m) as HD.
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
      lock_chain N1 n0 L n1 ->
      (forall n2, ~ net_lock_on N1 n1 n2) ->
      dep_set N1 (n1::L) n0.

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

          assert (dep_on N1 a m) as HD.
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
      dep_set N1 DS n ->
      DeadSet DS N1.

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

        enough (dep_on N1 n' a).
        {
          assert (dep_on N1 n a) as Hx by eauto 2 with LTS.
          apply dep_lock_chain in Hx. hsimpl in Hx. eauto.
          eapply lock_chain_dep_set_In; eauto.
        }

        enough (net_lock_on N1 n' a) by attac.
        attac.
    Qed.

    Hint Resolve dep_set_deadset : LTS.


    (** If there is anyone dependent on itself, then it is a member of a deadset *)
    Corollary dep_self_deadset [n] :
      dep_on N1 n n ->
      exists DS, List.In n DS /\ DeadSet DS N1.

    Proof with eattac.
      intros HL.

      destruct (dep_lock_chain HL) as [L [HLc HIn]]...
    Qed.


    Section Dec.
      Hypothesis net_lock_on_dec : locks_dec_in N1.

      Lemma dep_set_lock_on_dec [m n D] :
        dep_set N1 D m ->
        List.In n D ->
        (exists n', net_lock_on N1 n n') \/ forall n', ~ net_lock_on N1 n n'.

      Proof.
        intros.

        remember ([] : list Name) as D_past.
        rename D into D_next.
        replace (D_next) with (D_past ++ D_next) in H by attac.

        assert (forall m', In m' D_next -> dep_on N1 m m') by (intros; apply `(dep_set _ _ _); attac).
        assert (forall m', dep_on N1 m m' -> In m' D_past \/ In m' D_next).
        {
          assert (forall m', dep_on N1 m m' -> In m' (D_past ++ D_next)) by (intros; apply `(dep_set _ _ _); attac).
          attac.
        }
        assert (forall n', In n' D_past -> ~ net_lock_on N1 n n') by attac.

        assert (dep_on N1 m n) by attac.

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
        dep_set N1 L0 n0 ->
        List.In n1 L0 ->
        (exists L1, net_lock N1 L1 n1) \/ (forall n2, ~ net_lock_on N1 n1 n2).

      Proof.
        intros HD HIn.
        destruct (dep_set_lock_on_dec HD HIn) as [[n2 HL]|HNL].
        - left; eattac.
        - right; eattac.
      Qed.


      (** For any depset, there is a lock chain that completely covers it *)
      Lemma longest_lock_chain [n0 D] :
        dep_set N1 D n0 ->
        D <> [] ->
        exists n1 L, lock_chain N1 n0 L n1 /\ incl D (n1::L).

      Proof.
        intros HD HDnil.

        enough (exists n1 L, lock_chain N1 n0 L n1 /\ forall n2, net_lock_on N1 n1 n2 -> List.In n2 (n0::n1::L))
          as (n1 & L & HL & HIn).
        {
          assert (List.In n1 D) as HIn1 by (apply HD; eattac).

          destruct (dep_set_lock_set_dec HD HIn1) as [[D1 HD1]|HNL].
          {
            apply net_get_lock in HD1 as [n2 HD1].
            specialize (HIn n2) as [HEq2 | [HEq2 | HIn2]]; eauto with LTS datatypes; subst.
            - exists n2, (L ++ [n1]).
              assert (lock_chain N1 n2 (L ++ [n1]) n2) as HLc by eattac.
              split; auto.
              eapply dep_loop_dep_set in HLc.
              eapply dep_set_incl; eauto.
            - assert (net_lock_on N1 n2 n2) as HD2 by eattac.
              exists n2, L.
              split; eauto.
              assert (lock_chain N1 n2 [] n2) as HLc1 by eattac.
              specialize (dep_on_loop_dep_set HL HLc1) as HD'.
              assert (incl (L ++ [n2]) (n2::L)) by eauto with datatypes.
              apply (dep_set_incl HD) in HD'.
              eapply incl_tran; eauto.
            - assert (lock_chain N1 n1 [] n2) as HLc1 by eattac.
              destruct (lock_chain_split_in HIn2 HL) as (L0 & L2 & HEq' & HLc0 & HLc2); subst.
              assert (lock_chain N1 n1 (n2::L2) n1) as HLc1' by eattac.
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

        assert (exists n1 L, lock_chain N1 n0 L n1) as [n1 [L HL]].
        {
          destruct D.
          1: bullshit.
          assert (List.In n (n :: D)) as HIn by attac.
          apply HD in HIn as HDep.
          exists n.
          apply dep_lock_chain in HDep as [L [HL _]].
          eattac.
        }
        assert (forall n2, dep_on N1 n0 n2 -> List.In n2 (n0::L ++ D)) as Hseen.
        {
          intros.
          right.
          apply in_or_app; right.
          apply HD; auto.
        }
        assert (forall n, List.In n D -> dep_on N1 n0 n) as HD' by apply HD.

        assert (forall n, List.In n D -> (exists n', net_lock_on N1 n n') \/ forall n', ~ net_lock_on N1 n n') as Hlock_dec
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

          assert (lock_chain N1 n0 (La ++ a :: L') n1) as HL0 by attac.
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
              consider (n2 = a) by attac.
              attac.
            * specialize (IHD (L ++ n1 :: L' ++ [a])).
              repeat (rewrite <- app_assoc in * ).
              simpl in *.

              assert (lock_chain N1 n0 (L ++ n1 :: L' ++ [a]) b) as HL0 by attac.
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
        DeadSet DS N1 ->
        exists n, List.In n DS /\ dep_on N1 n n.

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
          assert (net_lock_on N1 n0 n') by attac.
          assert (dep_on N1 n0 n') as HD' by attac.
          apply HL in HD'.
          bullshit.
        }

        specialize (deadset_dep_set_deadset HDS HL HLnil HIn) as HDSL.

        destruct (longest_lock_chain HL) as (n2 & Lc & HLc & Hincl); eauto.

        enough (dep_on N1 n2 n2) by eauto with LTS.

        enough (exists n1, List.In n1 (n2::Lc) /\ dep_on N1 n2 n1) as [n1 [HIn1 HD1]].
        {
          kill HIn1.
          eapply (lock_chain_split_in H) in HLc
              as (L0 & L1 & HEq & HLc0 & HLc1).
          apply lock_chain_dep in HLc1.
          eauto with LTS.
        }

        assert (List.In n2 L) as HIn2 by (apply HL; eapply lock_chain_dep; eauto).

        assert (exists n1, net_lock_on N1 n2 n1) as [n1 HL1].
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
        assert (forall v, ~ In n0 (act_particip (NComm m0 m1 Q v))) by attac.
        eapply (@act_particip_stay PQued PAct); eattac.
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
      2: {
        replace (NetMod.get n0 N1) with (NetMod.get n0 N0); eattac.
        eapply (@act_particip_stay PQued PAct); eattac.
      }

      consider (_ =(_)=> _); compat_hsimpl in *.

      eattac.
      consider (pq_lock _ _).
      hsimpl in *.
      constructor; auto.
      intros ? ? ? ?.
      assert (In (n, R, v0) I0 \/ In (n, R, v0) [(m1, R, v)]) as [|]; eattac.
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
      eapply (@act_particip_stay PQued PAct); eattac.
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

      bullshit (In (n1, R, v) (I0 ++ [(n1, R, v)])).
    Qed.


    Lemma net_unlock_send_inv [L n0 m0 m1 v] :
      net_lock N0 L n0 ->
      ~ net_lock N1 L n0 ->
      (N0 =(NComm m1 m0 R v)=> N1) ->
      In m1 L.

    Proof.
      intros.
      destruct (in_dec Name.eq_dec m1 L); eauto.
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
  (* Lemma SRPC_net_lock_neq_nil [N] : *)
  (*   SRPC_net N -> *)
  (*   lock_neq_nil_type N. *)
  (* Proof. *)
  (*   unfold lock_neq_nil_type, NetLocks.net_lock. *)
  (*   intros. *)
  (*   consider (exists s, pq_lock [s] (NetMod.get n N)) by eauto using SRPC_pq_get_lock. *)
  (*   destruct L. *)
  (*   2: attac. *)
  (*   clear H0. *)
  (*   absurd (pq_lock [s] (NetMod.get n N)); auto. *)
  (*   ltac1:(debug eauto with datatypes LTS). THIS SHIT LOOPS WITH net_lock_reply_unlock in Resolve *)

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

Module LocksUniq(Name:UsualDecidableSet)(NetModF:NET).
  Include LOCKS_UNIQ(Name)(NetModF).
End LocksUniq.


Module Srpc(Name : UsualDecidableSet)(NetModF : NET).
  Module Import LocksUniq := LocksUniq(Name)(NetModF).

  Import Net.
  Import Model.
  Import Que.


  (** SRPC process handling a request from the client [c] *)
    Inductive SRPC_Handle_State (c : Name) :=
    | HWork : SRPC_Handle_State c
    | HLock (s : Name) : SRPC_Handle_State c
    .

    #[export] Hint Constructors SRPC_Handle_State : LTS.

    (** Behavioral description of an Single-threaded RPC process *)
    Inductive SRPC_Handling [c] : SRPC_Handle_State c -> Proc -> Prop :=
    | HSRPC_Work [P0]
        (* If sends a reply, then to the client. *)
        (HReply : forall c' v P1, (P0 =(Send (c', R) v)=> P1) -> c = c')

        (* If sends a query, then locked. *)
        (HQuery : forall s v P1, (P0 =(Send (s, Q) v)=> P1) -> SRPC_Handling (HLock c s) P1)
        (* If taus, then still working *)
        (HTau : forall P1, (P0 =(Tau)=> P1) -> SRPC_Handling (HWork c) P1)
        (* Is not a receiving process. Note that the below does not work: *)
        (* (forall n v P1, P0 =(Recv n v)=> P1 -> False) -> *)
        (* Because that would allow the process to get stuck in a state in which it receives but
      doesn't accept anything. That would be considered a lock on empty set and we don't want
      that. *)
        (HNoRecv : forall h, P0 <> PRecv h)
        (HNoEnd : P0 <> PEnd)
      : SRPC_Handling (HWork c) P0

    | HSRPC_Lock [s P0]
        (* Accepts ALL replies from server *)
        (HReplyAll : forall v, exists P1, (P0 =(Recv (s, R) v)=> P1))
        (* Accepts ONLY replies and ONLY from server *)
        (HReplyOnly : forall a P1, P0 =(a)=> P1 -> exists v, a = Recv (s, R) v)
        (* If recvs a reply, moves to busy *)
        (HRecvR : forall a P1, P0 =(a)=> P1 -> SRPC_Handling (HWork c) P1)
      : SRPC_Handling (HLock c s) P0
    .


    (** SRPC state of any service *)
    Inductive SRPC_State :=
    | Free : SRPC_State
    | Busy [c] : SRPC_Handle_State c -> SRPC_State
    .

    #[export] Hint Constructors SRPC_State : LTS.


    Notation "'Work'" := (fun c => Busy (HWork c)) (at level 30).
    Notation "'Lock'" := (fun c s => Busy (HLock c s)) (at level 30).

    Notation "'Work' c" := (Busy (HWork c)) (at level 200) : type_scope.
    Notation "'Lock' c s" := (Busy (HLock c s)) (at level 200) : type_scope.


    (** Behavioral description of an Single-threaded RPC process *)
    CoInductive SRPC : SRPC_State -> Proc -> Prop :=
    | SRPC_Free [P0]
      (* Accepts ALL queries *)
      (HQueryAll : forall c v, exists P1, (P0 =(Recv (c, Q) v)=> P1))
      (* Accepts ONLY queries *)
      (HQueryOnly : forall a P1, (P0 =(a)=> P1) ->
                            exists c v,
                              a = Recv (c, Q) v
                              /\ SRPC (Work c) P1
      )
      : SRPC Free P0

    | SRPC_Busy [P0 c]
        (srpc : SRPC_Handle_State c)
        (HBusy : SRPC_Handling srpc P0)
        (HReply : forall v P1, P0 =(Send (c, R) v)=> P1 -> SRPC Free P1)
        (HQuery : forall s v P1, P0 =(Send (s, Q) v)=> P1 -> SRPC (Lock c s ) P1)
        (HRecv : forall s v P1, P0 =(Recv (s, R) v)=> P1 -> SRPC (Work c) P1)
        (HTau : forall P1, P0 =(Tau)=> P1 -> SRPC (Work c) P1)
      : SRPC (Busy srpc) P0
    .


    Definition SRPC_pq srpc S := match S with pq _ P _ => SRPC srpc P end.

    Definition AnySRPC_pq S := exists s, SRPC_pq s S.

    Definition AnySRPC P := exists s, SRPC s P.

    #[export] Hint Transparent SRPC_pq AnySRPC AnySRPC_pq : LTS.


    (* This is to prevent stupid unfolding, but preserve inference from SRPC *)
    Lemma SRPC_SRPC_pq : forall [s S I P O], S = pq I P O -> SRPC s P <-> SRPC_pq s S.
    Proof. split; intros; subst; eauto. Qed.

    Lemma AnySRPC_AnySRPC_pq : forall [S I P O], S = pq I P O -> AnySRPC P <-> AnySRPC_pq S.
    Proof. unfold AnySRPC_pq. split; intros; subst; eauto. Qed.

    Lemma SRPC_AnySRPC : forall [s P], SRPC s P -> AnySRPC P.
    Proof. unfold AnySRPC. eauto. Qed.

    Lemma SRPC_pq_AnySRPC_pq : forall [s P], SRPC_pq s P -> AnySRPC_pq P.
    Proof. unfold AnySRPC_pq. eauto. Qed.


    #[export] Hint Immediate SRPC_SRPC_pq AnySRPC_AnySRPC_pq : LTS.
    #[export] Hint Resolve -> SRPC_SRPC_pq AnySRPC_AnySRPC_pq 10 : LTS.
    #[export] Hint Rewrite <- SRPC_SRPC_pq AnySRPC_AnySRPC_pq using spank : LTS.

    #[export] Hint Resolve SRPC_AnySRPC SRPC_pq_AnySRPC_pq : LTS.


    Ltac2 rec destruct_SRPC (hs : ident) (htr : ident option) :=
      let hs_h := hyp hs in
      match! (Constr.type hs_h) with
      | AnySRPC_pq ?p =>
          let srpc := Fresh.in_goal @srpc in
          destruct $hs_h as [$srpc $hs];
          destruct_SRPC hs htr
      | AnySRPC ?p =>
          let srpc := Fresh.in_goal @srpc in
          destruct $hs_h as [$srpc $hs];
          destruct_SRPC hs htr
      | SRPC_pq ?srpc (pq _ _ _) =>
          simpl in $hs;
          destruct_SRPC hs htr
      | SRPC_pq ?srpc ?p =>
          let i := Fresh.in_goal @I in
          let p := Fresh.in_goal @P in
          let o := Fresh.in_goal @O in
          destruct p as [$i $p $o];
          destruct_SRPC hs htr
      | SRPC ?srpc ?p =>
          let p1 := Fresh.in_goal @P in
          let hqa := Fresh.in_goal @HQueryAll in
          let hqo := Fresh.in_goal @HQueryOnly in
          let c := Fresh.in_goal @c in
          let v := Fresh.in_goal @v in
          let srpcb := Fresh.in_goal @srpc in
          let hb := Fresh.in_goal @HBusy in
          let hr := Fresh.in_goal @HReply in
          let hrc := Fresh.in_goal @HRecv in
          let hq := Fresh.in_goal @HQuery in
          let ht := Fresh.in_goal @HTau in
          let he1 := Fresh.in_goal @HEq1 in
          let he2 := Fresh.in_goal @HEq2 in
          inversion_stable $hs_h
            as [ $p1 $hqa $hqo $he1 $he2 | $p1 $c $srpcb $hb $hr $hq $hrc $ht $he1 $he2]
               >
                 [ ssubst;
                   first
                     [ bullshit
                     | match htr with
                       | None => ()
                       | Some htr =>
                           let hqo_h := hyp hqo in
                           let htr_h := hyp htr in
                           destruct ($hqo_h _ _ $htr_h) as ($c & $v & $he1 & $hs);
                           clear $hqo
                       end;
                       ssubst
                     ]

                 | ssubst;
                   first
                     [ bullshit
                     | destruct_SRPC hb htr;
                       Control.enter
                         (fun () =>
                            ssubst;
                            match htr with
                            | None => ()
                            | Some htr =>
                                let htr_h := hyp htr in
                                let hr_h := hyp hr in
                                let hrc_h := hyp hrc in
                                let hq_h := hyp hq in
                                let ht_h := hyp ht in
                                first
                                  [ specialize ($hr_h _ _ $htr_h); clear $hq $ht $hrc
                                  | specialize ($hq_h _ _ _ $htr_h); clear $hr $ht $hrc
                                  | specialize ($ht_h _ $htr_h); clear $hr $hq $hrc
                                  | specialize ($hrc_h _ _ _ $htr_h); clear $hr $hq $ht
                                  | ()
                                  ]
                            end
                         )
                     ]
                 ]
      | SRPC_Handling ?srpc ?p =>
          let p1 := Fresh.in_goal @P in
          let s := Fresh.in_goal @s in
          let hrr := Fresh.in_goal @HRecvR in
          let hsr := Fresh.in_goal @HSendR in
          let hsq := Fresh.in_goal @HSendQ in
          let ht := Fresh.in_goal @HTau in
          let hnr := Fresh.in_goal @HNoRecv in
          let hne := Fresh.in_goal @HNoEnd in
          let hra := Fresh.in_goal @HReplyAll in
          let hro := Fresh.in_goal @HReplyOnly in
          let he1 := Fresh.in_goal @HEq1 in
          let he2 := Fresh.in_goal @HEq2 in
          inversion_stable $hs_h
            as [$p1 $hsr $hsq $ht $hnr $hne $he1 $he2 | $s $p1 $hra $hro $hrr $he1 $he2]
               >
                 [ ssubst;

                   first
                     [ bullshit
                     | let n := Fresh.in_goal @n in
                       let s := Fresh.in_goal @s in
                       let t := Fresh.in_goal @t in
                       let v := Fresh.in_goal @v in
                       match htr with
                       | None => ()
                       | Some htr =>
                           let htr_h := hyp htr in
                           let a := match! Constr.type htr_h with
                                    | (_ =(?a)=> _) =>
                                        if Constr.is_var a then a
                                        else
                                          let av := Fresh.in_goal @a in
                                          remember $a as $av;
                                          hyp av
                                    end in
                           let hq_h := hyp hsq in
                           let hr_h := hyp hsr in
                           let ht_h := hyp ht in
                           destruct $a
                             as [ [$n [|]] $v | [$n $t] $v |];
                           ssubst;
                           try (specialize ($hq_h _ _ _ $htr_h); rename n into s);
                           try (specialize ($hr_h _ _ _ $htr_h); subst $n);
                           try (specialize ($ht_h _ $htr_h));
                           try (inversion $htr_h; bullshit)
                       end
                     ]

                 | ssubst;
                   first
                     [ bullshit
                     | let v := Fresh.in_goal @v in
                       let htr_h := match htr with
                                    | None =>
                                        let t := Fresh.in_goal @T in
                                        let p := Fresh.in_goal @P in
                                        let hra_h := hyp hra in
                                        destruct ($hra_h some_val) as [$p $t];
                                        hyp t
                                    | Some htr => hyp htr
                                    end in
                       let hro_h := hyp hro in
                       let hrr_h := hyp hrr in
                       destruct ($hro_h _ _ $htr_h)
                         as [$v $he1];
                       ssubst
                     ]
                 ]
      end.

    Ltac2 Notation "destruct" "SRPC" hs(ident) ht(opt(ident)) :=
      Control.enter (fun () => destruct_SRPC hs ht).


    (** SRPC is preserved for processes *)
    Lemma trans_invariant_AnySRPC : trans_invariant AnySRPC always.

    Proof with eattac.
      intros N0 N1 a T Hsrpc _.
      destruct Hsrpc as [srpc Hsrpc].
      destruct SRPC Hsrpc T...
      Qed.

    #[export] Hint Resolve trans_invariant_AnySRPC : inv.
    #[export] Hint Extern 10 (AnySRPC _) => solve_invariant : LTS.


    (** SRPC is preserved for services *)
    Lemma trans_invariant_AnySRPC_pq : trans_invariant AnySRPC_pq always.

    Proof.
      intros N0 N1 a T Hsrpc _.
      kill T; auto.
      all: destruct SRPC Hsrpc H; eattac.
    Qed.

    #[export] Hint Resolve trans_invariant_AnySRPC_pq : inv.
    #[export] Hint Extern 10 (AnySRPC_pq _) => solve_invariant : LTS.


    Lemma SRPC_recv_Q [P0 P1] [c v] :
      (P0 =(Recv (c, Q) v)=> P1) ->
      AnySRPC P0 ->
      SRPC Free P0 /\ SRPC (Work c) P1.

    Proof.
      intros T Hsrpc.

      destruct Hsrpc as [srpc Hsrpc].
      remember Hsrpc as Hsrpc'.
      destruct SRPC Hsrpc T; attac.
    Qed.


    Lemma SRPC_recv_R [P0 P1] [s v] :
      (P0 =(Recv (s, R) v)=> P1) ->
      AnySRPC P0 ->
      exists c, SRPC (Lock c s) P0 /\ SRPC (Work c) P1.
    Proof.
      intros T Hsrpc.

      destruct Hsrpc as [srpc Hsrpc].
      remember Hsrpc as Hsrpc'.
      destruct SRPC Hsrpc T; eattac.
    Qed.


    Lemma SRPC_recv_R' [P0 P1] [c s v] :
      (P0 =(Recv (s, R) v)=> P1) ->
      SRPC (Lock c s) P0 -> SRPC (Work c) P1.
    Proof.
      intros T Hsrpc.
      destruct SRPC Hsrpc T; eattac.
    Qed.


    Lemma SRPC_send_Q [P0 P1] [s v] :
      (P0 =(Send (s, Q) v)=> P1) ->
      AnySRPC P0 ->
      exists c, (SRPC (Work c) P0 /\ SRPC (Lock c s) P1).

    Proof.
      intros T Hsrpc.

      destruct Hsrpc as [srpc Hsrpc].
      remember Hsrpc as Hsrpc'.
      destruct SRPC Hsrpc T; attac.
    Qed.


    Lemma SRPC_send_Q' [P0 P1] [c s v] :
      (P0 =(Send (s, Q) v)=> P1) ->
      SRPC (Work c) P0 ->
      SRPC (Lock c s) P1.

    Proof.
      intros T Hsrpc.
      destruct SRPC Hsrpc T; eattac.
    Qed.


    Lemma SRPC_send_R [P0 P1] [c v] :
      (P0 =(Send (c, R) v)=> P1) ->
      AnySRPC P0 ->
      SRPC (Work c) P0 /\ SRPC Free P1.

    Proof.
      intros T Hsrpc.

      destruct Hsrpc as [srpc Hsrpc].
      remember Hsrpc as Hsrpc'.
      destruct SRPC Hsrpc T; doubt.
      assert (c0 = c) by eauto; subst.
      eattac.
    Qed.


    Lemma SRPC_tau [P0 P1] :
      (P0 =(Tau)=> P1) ->
      AnySRPC P0 ->
      exists c, SRPC (Work c) P0 /\ SRPC (Work c) P1.

    Proof.
      intros T Hsrpc.

      destruct Hsrpc as [srpc Hsrpc].
      remember Hsrpc as Hsrpc'.
      destruct SRPC Hsrpc T; eattac.
    Qed.


    Lemma SRPC_tau' [P0 P1 c] :
      (P0 =(Tau)=> P1) ->
      SRPC (Work c) P0 ->
      SRPC (Work c) P1.

    Proof.
      intros T Hsrpc.
      destruct SRPC Hsrpc T; eattac.
    Qed.


    Lemma AnySRPC_PTau_inv P :
      AnySRPC (PTau P) <-> exists c, SRPC (Work c) (PTau P).

    Proof.
      split; intros.
      - kill H.
        assert (PTau P =(Tau)=> P ) as T by attac.
        kill H0.
        1: apply HQueryOnly in T; eattac.
        exists c.
        have (SRPC_Handling srpc (PTau P)).
        kill HBusy.
        1: constructor; attac.
        apply HReplyOnly in T; attac.
      - eattac.
    Qed.


    Lemma AnySRPC_PSend_inv n v P :
      AnySRPC (PSend n v P) <-> exists c, SRPC (Work c) (PSend n v P).

    Proof.
      split; intros.
      - kill H.
        assert (PSend n v P =(Send n v)=> P ) as T by attac.
        kill H0.
        1: apply HQueryOnly in T; eattac.
        exists c.
        have (SRPC_Handling srpc (PSend n v P)).
        kill HBusy.
        1: constructor; attac.
        apply HReplyOnly in T; attac.
      - eattac.
    Qed.


    Lemma SRPC_Handling_work_act [P0 : Proc] [c] :
      SRPC_Handling (HWork c) P0 ->
      exists P1, (exists v, P0 =(Send (c, R) v)=> P1) \/ (P0 =(Tau)=> P1) \/ (exists s v, P0 =(Send (s, Q) v)=> P1).

    Proof.
      intros Hsrpc.
      destruct P0; destruct SRPC Hsrpc; ssubst; subst. (* TODO wtf this double subst *)
      - exists P0.
        destruct n as [n [|]].
        + right.
          right.
          exists n, v.
          constructor.
        + left.
          exists v.
          erewrite HSendR.
          constructor.
          constructor.
      - exists P0.
        right.
        left.
        constructor.
    Qed.


    Lemma SRPC_busy_reply [P0 P1 P2 path] [c c' v] [s : SRPC_Handle_State c] :
      SRPC (Busy s) P0 ->
      (P0 =[path]=> P1) ->
      (P1 =(Send (c', R) v)=> P2) ->
      Forall (fun a => match a with
                    | Send (_, t) _ => t = Q
                    | _ => True
                    end

        ) path ->
      c = c'.

    Proof.
      intros Hsrpc T0 T1 HF.
      generalize dependent P0 c c' v.
      induction path; intros.
      {
        kill T0.
        destruct SRPC Hsrpc T1; eattac.
      }

      kill T0.

      destruct SRPC Hsrpc T2; eattac.
    Qed.


    Lemma SRPC_busy_reply_exists [P0] [c] [s : SRPC_Handle_State c] :
      SRPC (Busy s) P0 ->
      exists path P1 P2 v,
      (P0 =[path]=> P1)
      /\ (P1 =(Send (c, R) v)=> P2)
      /\ Forall (fun a => match a with
                    | Send (_, t) _ => t = Q
                    | _ => True
                      end) path.

    Proof with eattac.
      intros Hsrpc.
      assert (forall a P', P0 =(a)=> P' -> AnySRPC P') as HPres by eattac.

      kill Hsrpc.
      ltac1:(dependent destruction H0).

      ltac1:(dependent induction HBusy); intros.
      - assert (SRPC_Handling (HWork c) P0) as Hsrpc by (constructor; eattac).
        specialize (SRPC_Handling_work_act Hsrpc) as [P1 [[v T]|[T|[s [v T]]]]].
        + exists [], P0, P1, v...
        + specialize (H0 P1 T).
          specialize (HTau0 _ T).
          specialize (HTau _ T).
          kill HTau0.
          destruct H0  as (path & P2 & P3 & v & T1 & T2 & HF); eauto with LTS.
          exists (Tau :: path), P2, P3, v; eauto with LTS.
        + specialize (H s v P1 T).
          specialize (HQuery _ _ _ T).
          specialize (HQuery0 _ _ _ T).
          kill HQuery0.
          destruct H as (path & P2 & P3 & v' & T1 & T2 & HF); eauto with LTS.
          exists (Send (s, Q) v :: path), P2, P3, v'.
          eattac.

      - specialize (HReplyAll some_val) as [P1 T].
        have (AnySRPC P1).
        specialize (H _ _ T).
        specialize (HRecvR _ _ T).
        kill HRecvR.
        specialize (HPres _ _ T).
        destruct HPres as [srpc Hsrpc].
        specialize (HRecv _ _ _ T).
        kill Hsrpc.
        {
          enough (exists a P2, P1 =(a)=> P2) as (a & P2 & T').
          {
            specialize (HQueryOnly _ _ T') as (c' & v' & HEq & _).
            kill HRecv.
            kill HBusy.
            - kill T'.
            - specialize (HReplyOnly0 _ _ T') as (v'' & HEq).
              kill HEq.
          }

          kill T.
          unshelve attac.
          apply some_val.
        }

        kill HRecv.
        destruct H as (path & P2 & P3 & v & T1 & T2 & HF); intros; eauto 10 with LTS.
        attac.
    Qed.


    Lemma SRPC_work_inv [P : Proc] [c0 c1] [s0 : SRPC_Handle_State c0] [s1 : SRPC_Handle_State c1] :
      SRPC (Busy s0) P ->
      SRPC (Busy s1) P ->
      c0 = c1.

    Proof.
      intros Hsrpc0 Hsrpc1.
      specialize (SRPC_busy_reply_exists Hsrpc0) as (path & P2 & P3 & v & T1 & T2 & HF).
      specialize (SRPC_busy_reply Hsrpc1 T1 T2 HF) as HEq'.
      eauto.
    Qed.

    #[export] Hint Immediate SRPC_work_inv : LTS.


    Lemma SRPC_pq_work_inv [S : PQued] [c0 c1] [s0 : SRPC_Handle_State c0] [s1 : SRPC_Handle_State c1] :
      SRPC_pq (Busy s0) S ->
      SRPC_pq (Busy s1) S ->
      c0 = c1.
    Proof. destruct S; attac. Qed.

    #[export] Hint Immediate SRPC_pq_work_inv : LTS.


    Lemma SRPC_inv [P srpc0 srpc1] :
      SRPC srpc0 P ->
      SRPC srpc1 P ->
      srpc0 = srpc1.

    Proof.
      intros Hsrpc0 Hsrpc1.
      kill Hsrpc0.
      - specialize (HQueryAll some_name some_val) as [P1 T].
        kill Hsrpc1; auto.
        kill HBusy.
        + kill T.
        + specialize (HReplyOnly _ _ T) as [v HEq].
          bullshit.
      - kill Hsrpc1.
        + specialize (HQueryAll some_name some_val) as [P1 T].
          kill HBusy.
          1: kill T.
          apply HReplyOnly in T.
          destruct T.
          bullshit.

        + assert (c = c0).
          {
            eapply SRPC_work_inv; constructor; eattac.
          }
          subst.
          enough (srpc = srpc0) by (subst; auto).
          kill HBusy; kill HBusy0; eauto.
          * specialize (HReplyAll some_val) as [P1 T].
            kill T.
          * specialize (HReplyAll some_val) as [P1 T].
            kill T.
          * specialize (HReplyAll some_val) as [P1 T].
            apply HReplyOnly0 in T as [v E].
            kill E.
    Qed.

    #[export] Hint Immediate SRPC_inv : LTS.


    Lemma SRPC_pq_inv [S srpc0 srpc1] :
      SRPC_pq srpc0 S ->
      SRPC_pq srpc1 S ->
      srpc0 = srpc1.

    Proof. destruct S; attac. Qed.

    #[export] Hint Immediate SRPC_pq_inv : LTS.


    Lemma SRPC_inv_tau_l [P0 P1] :
      AnySRPC P0 ->
      (P0 =(Tau)=> P1) ->
      exists c, SRPC (Work c) P0.
    Proof.
      intros.
      consider (exists c, SRPC (Work c) P0 /\ SRPC (Work c) P1) by (eapply SRPC_tau; eattac).
      attac.
    Qed.

    Lemma SRPC_inv_tau_r [P0 P1] :
      AnySRPC P0 ->
      (P0 =(Tau)=> P1) ->
      exists c, SRPC (Work c) P1.
    Proof.
      intros.
      consider (exists c, SRPC (Work c) P0 /\ SRPC (Work c) P1) by (eapply SRPC_tau; eattac).
      attac.
    Qed.

    Lemma SRPC_inv_send_R_l [P0 c v P1] :
      AnySRPC P0 ->
      (P0 =(Send (c, R) v)=> P1) ->
      SRPC (Work c) P0.
    Proof. intros. assert (SRPC (Work c) P0 /\ SRPC Free P1) by eauto using SRPC_send_R. attac. Qed.

    Lemma SRPC_inv_send_R_r [P0 c v P1] :
      AnySRPC P0 ->
      (P0 =(Send (c, R) v)=> P1) ->
      SRPC Free P1.
    Proof. intros. assert (SRPC (Work c) P0 /\ SRPC Free P1) by eauto using SRPC_send_R. attac. Qed.

    Lemma SRPC_inv_send_Q_l [P0 s v P1] :
      AnySRPC P0 ->
      (P0 =(Send (s, Q) v)=> P1) ->
      exists c, SRPC (Work c) P0.
    Proof. intros. consider (exists c, SRPC (Work c) P0 /\ SRPC (Lock c s) P1) by eauto using SRPC_send_Q. attac. Qed.

    Lemma SRPC_inv_send_Q_r [P0 s v P1] :
      AnySRPC P0 ->
      (P0 =(Send (s, Q) v)=> P1) ->
      exists c, SRPC (Lock c s) P1.
    Proof. intros. consider (exists c, SRPC (Work c) P0 /\ SRPC (Lock c s) P1) by eauto using SRPC_send_Q. attac. Qed.

    Lemma SRPC_inv_recv_Q_l [P0 P1] [c v] :
      (P0 =(Recv (c, Q) v)=> P1) ->
      AnySRPC P0 ->
      SRPC Free P0.
    Proof. intros. assert (SRPC Free P0 /\ SRPC (Work c) P1) by eauto using SRPC_recv_Q. attac. Qed.

    Lemma SRPC_inv_recv_Q_r [P0 P1] [c v] :
      (P0 =(Recv (c, Q) v)=> P1) ->
      AnySRPC P0 ->
      SRPC (Work c) P1.
    Proof. intros. assert (SRPC Free P0 /\ SRPC (Work c) P1) by eauto using SRPC_recv_Q. attac. Qed.

    Lemma SRPC_inv_recv_R_l [P0 P1] [s v] :
      (P0 =(Recv (s, R) v)=> P1) ->
      AnySRPC P0 ->
      exists c, SRPC (Lock c s) P0.
    Proof. intros. consider (exists c, SRPC (Lock c s) P0 /\ SRPC (Work c) P1) by eauto using SRPC_recv_R. attac. Qed.

    Lemma SRPC_inv_recv_R_r [P0 P1] [s v] :
      (P0 =(Recv (s, R) v)=> P1) ->
      AnySRPC P0 ->
      exists c, SRPC (Work c) P1.
    Proof. intros. consider (exists c, SRPC (Lock c s) P0 /\ SRPC (Work c) P1) by eauto using SRPC_recv_R. attac. Qed.

    #[export] Hint Resolve
      SRPC_inv_tau_l
      SRPC_inv_tau_r
      SRPC_inv_send_R_l
      SRPC_inv_send_R_r
      SRPC_inv_send_Q_l
      SRPC_inv_send_Q_r
      SRPC_inv_recv_Q_l
      SRPC_inv_recv_Q_r
      SRPC_inv_recv_R_l
      SRPC_inv_recv_R_r
      : LTS.

    Lemma SRPC_Free_recv_t_inv [P0 P1] [c t v] :
      (P0 =(Recv (c, t) v)=> P1) ->
      SRPC Free P0 ->
      t = Q.
    Proof. intros. consider (SRPC _ _). specialize (HQueryOnly (Recv (c, &t) v) P1) as [? ?]; eattac. Qed.
    Lemma SRPC_Lock_recv_t_inv [P0 P1] [c s s' t v] :
      (P0 =(Recv (s, t) v)=> P1) ->
      SRPC (Lock c s') P0 ->
      t = R.
    Proof. intros. consider (SRPC _ _). kill HBusy. attac. specialize (HReplyOnly (Recv (s, &t) v) P1) as [? ?]; eattac. Qed.

    #[export] Hint Rewrite -> SRPC_Free_recv_t_inv SRPC_Lock_recv_t_inv using spank : LTS.


    Lemma SRPC_recv_Q_c_inv [P0 P1] [c c' t v] :
      (P0 =(Recv (c, t) v)=> P1) ->
      SRPC Free P0 ->
      SRPC (Work c') P1 ->
      c' = c.
    Proof. intros. assert (AnySRPC P0) by eauto with LTS.
           hsimpl in *; assert (SRPC (Work c) (cont v)); eattac.
    Qed.
    Lemma SRPC_recv_R_s_inv [P0 P1] [c s' s t' v] :
      (P0 =(Recv (s', t') v)=> P1) ->
      SRPC (Lock c s) P0 ->
      s' = s.
    Proof. intros. hsimpl in *.
           enough (exists v', Recv (s', R) v = Recv (s, R) v') by eattac.
           kill H0. kill HBusy. eattac. hsimpl in H2. eapply HReplyOnly. eattac.
    Qed.
    Lemma SRPC_recv_R_c_inv [P0 P1] [c c' s' s t v] :
      (P0 =(Recv (s', t) v)=> P1) ->
      SRPC (Lock c s) P0 ->
      SRPC (Work c') P1 ->
      c' = c.
    Proof.
      intros. enough (SRPC (Work c) P1) by eattac.
      hsimpl in *. consider (SRPC _ (PRecv _)); eattac.
    Qed.

    #[export] Hint Rewrite -> SRPC_recv_Q_c_inv SRPC_recv_R_s_inv SRPC_recv_R_c_inv using spank : LTS.


    Lemma SRPC_Work_PRecv_bs [h c] :
      SRPC (Work c) (PRecv h) -> False.
    Proof. intros. consider (SRPC _ _). consider (SRPC_Handling _ _). bullshit. Qed.

    Lemma SRPC_Free_PSend_bs [n v P1] :
      SRPC Free (PSend n v P1) -> False.
    Proof. intros. consider (SRPC _ _). destruct n. specialize (HQueryAll n v). eattac. Qed.

    Lemma SRPC_Free_PTau_bs [P1] :
      SRPC Free (PTau P1) -> False.
    Proof. intros. consider (SRPC _ _). specialize (HQueryAll some_name some_val). eattac. Qed.

    Lemma SRPC_Lock_PSend_bs [n v P1 c s] :
      SRPC (Lock c s) (PSend n v P1) -> False.
    Proof. intros. consider (SRPC _ _). destruct n.  consider (SRPC_Handling _ _); doubt. specialize (HReplyAll v); attac. Qed.

    Lemma SRPC_Lock_PTau_bs [P1 c s] :
      SRPC (Lock c s) (PTau P1) -> False.
    Proof. intros. consider (SRPC _ _). consider (SRPC_Handling _ _); doubt. specialize (HReplyAll some_val); attac. Qed.

    #[export] Hint Resolve
      SRPC_Work_PRecv_bs
      SRPC_Free_PSend_bs
      SRPC_Free_PTau_bs
      SRPC_Lock_PSend_bs
      SRPC_Lock_PTau_bs
      : bullshit.

    Lemma SRPC_Work_recv_bs [P0 P1 n v c] :
      (P0 =(Recv n v)=> P1) ->
      SRPC (Work c) P0 ->
      False.
    Proof. attac. Qed.

    Lemma SRPC_Free_send_bs [n v P1] :
      SRPC Free (PSend n v P1) -> False.
    Proof. intros. consider (SRPC _ _). destruct n. specialize (HQueryAll n v). eattac. Qed.
    Lemma SRPC_Free_tau_bs [P1] :
      SRPC Free (PTau P1) -> False.
    Proof. intros. consider (SRPC _ _). specialize (HQueryAll some_name some_val). eattac. Qed.
    Lemma SRPC_Free_recv_R_bs [h n] :
      SRPC Free (PRecv h) -> h (n, R) <> None -> False.
    Proof. intros. consider (SRPC _ _). destruct (h (n, R)) eqn:P1v; doubt; specialize (HQueryOnly (Recv (n, R) some_val) (p some_val)) as [? ?]; eattac. Qed.

    Lemma SRPC_Lock_send_bs [n v c s P1] :
      SRPC (Lock c s) (PSend n v P1) -> False.
    Proof. intros. consider (SRPC _ _). destruct n. kill HBusy. specialize (HReply0 n v). eattac. destruct (HReplyAll v). attac. Qed.
    Lemma SRPC_Lock_tau_bs [c s P1] :
      SRPC (Lock c s) (PTau P1) -> False.
    Proof. intros. consider (SRPC _ _). kill HBusy. specialize (HReply0 some_name some_val). eattac. destruct (HReplyAll some_val). attac. Qed.
    Lemma SRPC_Lock_recv_Q_bs [h n c s] :
      SRPC (Lock c s) (PRecv h) -> h (n, Q) <> None -> False.
    Proof. intros. consider (SRPC _ _). destruct (h (n, Q)) eqn:P1v; doubt; kill HBusy; doubt; specialize (HReplyOnly (Recv (n, Q) some_val) (p some_val)) as [? ?]; eattac. Qed.
    Lemma SRPC_Lock_recv_other_bs [h n c s t] :
      SRPC (Lock c s) (PRecv h) ->  h (n, t) <> None -> n <> s -> False.
    Proof. intros. destruct t. eapply SRPC_Lock_recv_Q_bs; eauto. apply H.
           consider (SRPC _ _). destruct (h (n, R)) eqn:P1v; doubt.
           kill HBusy; doubt. specialize (HReplyOnly (Recv (n, R) some_val) (p some_val)) as [? ?]; eattac.
    Qed.

    #[export] Hint Resolve
      SRPC_Work_recv_bs
      SRPC_Free_send_bs
      SRPC_Free_tau_bs
      SRPC_Free_recv_R_bs
      SRPC_Lock_send_bs
      SRPC_Lock_tau_bs
      SRPC_Lock_recv_Q_bs
      SRPC_Lock_recv_other_bs
      : bullshit.


    Import LockDefs.


    (** SRPC process can be locked only on one thing *)
    Lemma SRPC_one_lock [P : Proc] [L] :
      AnySRPC P ->
      proc_lock L P ->
      length (nodup Name.eq_dec L) = 1%nat.

    Proof.
      intros Hsrpc HL.

      destruct SRPC Hsrpc.
      - destruct P0; doubt.

        specialize (HL some_name) as [[HNoQ HNoIn] HYesR].
        specialize (HQueryAll some_name some_val) as [P1 T].
        kill T.
        cbv in *.
        bullshit.

      - destruct P; bullshit.
      - destruct P; try (kill HL).

        enough (Forall (eq s) L) as HAll.
        {
          eapply all_same_nodup_one in HAll as [HEq | HEq]; rewrite HEq in *; auto.

          specialize (HL s) as [[_ HYesR] _].
          hsimpl in *.
          exfalso.
          apply HYesR.
          cbv in *; bullshit.
        }

        apply (Forall_forall (eq s) L).
        intros.

        destruct (handle0 (x, R)) eqn:Hx.
        + specialize (HReplyOnly (Recv (x, R) some_val) (p some_val)) as [v' HEq]; ssubst; attac.
        + specialize (HL x) as [[HL _] _].
          bullshit.
    Qed.


    (** SRPC service can be locked only on one thing *)
    Lemma SRPC_pq_one_lock [S : PQued] [L] :
      AnySRPC_pq S ->
      pq_lock L S ->
      length (nodup Name.eq_dec L) = 1%nat.

    Proof.
      intros Hsrpc HL.

      destruct Hsrpc as [srpc Hsrpc].
      destruct S as [I P O].
      apply (@SRPC_one_lock P); eauto with LTS.
    Qed.


    (** If SRPC process is locked, then it is known on who *)
    Lemma SRPC_get_lock [P : Proc] [L] :
      AnySRPC P ->
      proc_lock L P ->
      exists n, proc_lock [n] P.

    Proof.
      intros Hsrpc HL.

      pose (SRPC_one_lock Hsrpc HL) as Hlen.
      pose (NoDup_nodup Name.eq_dec L) as HNodup.
      destruct (nodup_one _ HNodup Hlen ) as [n HEq].
      exists n.

      (* TODO fix this cbv *)
      cbv in HEq. rewrite <- HEq.

      apply (proc_lock_equiv_inv HL).
      apply nodup_incl; auto with datatypes.
      unfold incl.
      intros.
      apply (nodup_In Name.eq_dec); auto.
    Qed.


    (** If SRPC service is locked, then it is known on who *)
    Lemma SRPC_pq_get_lock [S : PQued] [L] :
      AnySRPC_pq S ->
      pq_lock L S ->
      exists n, pq_lock [n] S.

    Proof.
      intros Hsrpc HL.

      pose (SRPC_pq_one_lock Hsrpc HL) as Hlen.
      pose (NoDup_nodup Name.eq_dec L) as HNodup.
      destruct (nodup_one _ HNodup Hlen ) as [n HEq].
      exists n.

      (* TODO fix this cbv *)
      cbv in HEq. rewrite <- HEq.

      apply (pq_lock_equiv_inv HL).
      apply nodup_incl; auto with datatypes.
      unfold incl.
      intros.
      apply (nodup_In Name.eq_dec); auto.
    Qed.

    (** SRPC-locked state is correct for processes *)
    Lemma SRPC_Lock_lock [P : Proc] [s c] :
      SRPC (Lock c s) P -> proc_lock [s] P.

    Proof.
      intros Hsrpc.
      unfold proc_lock.

      destruct SRPC Hsrpc; doubt.

      destruct P; try (now kill T).

      intros.
      repeat split; intros.
      - kill H; cbv in *; doubt.
      - left.
        destruct (Name.eq_dec n s); subst; auto.
        destruct (handle0 (n, R)) eqn:HEq; doubt.
        assert (PRecv handle0 =(Recv (n, R) some_val)=> p some_val) as T'.
        constructor; auto.

        apply HReplyOnly in T' as [v HEq'].
        kill HEq'; auto.

      - destruct (handle0 (n, Q)) eqn:HEq; auto.
        assert (PRecv handle0 =(Recv (n, Q) some_val)=> p some_val) as T'.
        constructor; auto.

        apply HReplyOnly in T' as [v HEq'].
        kill HEq'.
    Qed.

    #[export] Hint Immediate SRPC_Lock_lock : LTS.


    (** SRPC-lock state is complete for all SRPC processes *)
    Lemma lock_SRPC_Lock [P : Proc] [s] :
      AnySRPC P ->
      proc_lock [s] P -> (exists c, SRPC (Lock c s) P).

    Proof.
      intros Hsrpc HL.
      unfold proc_lock in HL.

      destruct SRPC Hsrpc.
      - destruct P0; doubt.
        destruct (handle0 (s, R)) eqn:HEq; doubt.
        edestruct (HQueryOnly (Recv (s, R) some_val)) as (P1 & v & HEq' & Hsrpc).
        constructor.
        eapply HEq.
        kill HEq'.
        rewrite <- HEq in HL.
        specialize (HL s).
        kill HL.
        assert (List.In s [s]) by attac.
        apply H in H1.
        bullshit.
      - destruct P; doubt.
      - exists c.
        destruct P; doubt.
        destruct (Name.eq_dec s0 s); subst.
        {
          constructor; eauto with LTS.
          constructor; eauto.
        }

        kill T.

        destruct (handle0 (s, R)) eqn:HEq; doubt.
        edestruct (HReplyOnly (Recv (s, R) some_val)) as [P1' HEq'].
        constructor. apply HEq.

        kill HEq'.

        specialize (HL s).
        attac.
    Qed.


    (** You can't judge locks of a service based on its SRPC-state, because the code may be in a
    locked state, but there are messages to be sent *)
    Example SRPC_Lock_pq_lock [S : PQued] [s c] :
      SRPC_pq (Lock c s) S -> pq_lock [s] S.
    Abort.


    (** SRPC-lock state is complete for all SRPC services *)
    Lemma lock_SRPC_Lock_pq [S : PQued] [s] :
      AnySRPC_pq S ->
      pq_lock [s] S -> (exists c, SRPC_pq (Lock c s) S).

    Proof.
      intros Hsrpc HL.

      destruct HL as [I P HD HL Ho].

      destruct (lock_SRPC_Lock Hsrpc HL) as [c Hsrpc_L].
      exists c; eauto with LTS.
    Qed.


    (** You need at least a tau to change the lock *)
    Lemma SRPC_no_relock [P0 P1 a n0 n1] :
      AnySRPC P0 ->
      proc_lock [n0] P0 ->
      proc_lock [n1] P1 ->
      (P0 =(a)=> P1) ->
      n0 = n1.

    Proof.
      intros.
      destruct SRPC H H2.
      - absurd (exists c', SRPC (Lock c' n1) P1).
        + intros Hx; hsimpl in Hx.
          bullshit (Lock c' n1 = Work c) by attac.
        + eapply lock_SRPC_Lock; eattac.
      - absurd (exists c', SRPC (Lock c' n1) P1).
        + intros Hx; hsimpl in Hx.
          bullshit (Lock c' n1 = Work c) by attac.
        + eapply lock_SRPC_Lock; eattac.
    Qed.


    (** You need at least a tau to change the lock *)
    Lemma SRPC_pq_no_relock [S0 S1 a n0 n1] :
      AnySRPC_pq S0 ->
      pq_lock [n0] S0 ->
      pq_lock [n1] S1 ->
      (S0 =(a)=> S1) ->
      n0 = n1.

    Proof.
      intros.
      consider (exists c0, SRPC_pq (Lock c0 n0) S0) by eauto using lock_SRPC_Lock_pq with LTS.
      consider (exists c1, SRPC_pq (Lock c1 n1) S1) by eauto using lock_SRPC_Lock_pq with LTS.
      destruct S0, S1; simpl in *.
      consider (_ =(a)=> _);
        try (consider (Lock c0 n0 = Lock c1 n1) by eattac).
      eauto using SRPC_no_relock with LTS.
    Qed.


    (** The last thing an SRPC process does before locking is to send a query  *)
    Lemma SRPC_send_lock [L a P0 P1] :
      AnySRPC P0 ->
      proc_lock L P1 ->
      (P0 =(a)=> P1) ->
      match a with Send (_, t) _ => t = Q | _ => False end.

    Proof with (eauto with LTS).
      intros Hsrpc0 HL1 T.

      assert (AnySRPC P1) as Hsrpc1 by attac.

      specialize (SRPC_get_lock Hsrpc1 HL1) as [s HL1s].

      apply (lock_SRPC_Lock Hsrpc1) in HL1s as [c Hsrpc1_L].

      destruct Hsrpc0 as [srpc0 Hsrpc0].
      clear Hsrpc1.

      kill Hsrpc0 > [|kill HBusy ].
      - (* It was Free and became locked --- can't be locked and busy at once *)
        apply HQueryOnly in T as (c' & v & HEq & Hsrpc1_B). subst.
        kill Hsrpc1_L.
        kill Hsrpc1_B.
        ltac1:(dependent destruction H0).
        ltac1:(dependent destruction H1).
        kill HBusy.
        kill HBusy0.

        specialize (HReplyAll v) as [P2 T].
        kill T.

      - (* It was busy. So far so good. *)
        kill T.
        + (* Sent. *)
          destruct n as [n t].

          destruct t; auto.

          (* ...a reply! *)
          erewrite (HReply0 n) in *...

          assert (SRPC Free P1) as Hsrpc by eattac.

          kill Hsrpc1_L.
          ltac1:(dependent destruction H0).
          kill HBusy.

          kill Hsrpc.
          specialize (HQueryAll c v) as [P' T].
          eapply HReplyOnly in T as [v' E].
          bullshit.

        + (* Tau *)
          specialize (HTau0 _ (ltac:(constructor))) as Hsrpc1_B.

          kill Hsrpc1_L.
          kill Hsrpc1_B.
          ltac1:(dependent destruction H0).
          kill HBusy.

          specialize (HReplyAll some_val) as [P2 T].
          kill T.

      - (* It was locked and did an action which didn't unlock it *)
        specialize (HReplyOnly _ _ T) as (v & HEq). clear H0. subst.
        specialize (HRecvR _ _ T) as Hsrpc1_B.
        kill Hsrpc1_L.
        kill Hsrpc1_B.
        ltac1:(dependent destruction H0).
        kill HBusy.

        specialize (HReplyAll0 v) as [P2 T'].
        kill T'.
    Qed.


    Lemma SRPC_Decisive [P] :
      AnySRPC P ->
      Decisive P.

    Proof.
      generalize dependent P.
      ltac1:(cofix C).
      intros P Hsrpc_p.

      destruct P.
      - destruct Hsrpc_p as [srpc Hsrpc_p];
          ltac1:(dependent destruction Hsrpc_p) >
                  [|ltac1:(dependent destruction HBusy)].
        + specialize (HQueryAll some_name some_val) as [P1 T].
          kill T.
        + bullshit.
        + specialize (HReplyAll some_val) as [P1 T].
          kill T.
      - constructor; eattac.

      - constructor; intros;
          destruct Hsrpc_p as [srpc Hsrpc_p];
          ltac1:(dependent destruction Hsrpc_p) >
                  [|ltac1:(dependent destruction HBusy)].
        + split; intros.
          * destruct (handle0 (m, R)) eqn:HH; auto.
            assert (PRecv handle0 =(Recv (m, R) some_val)=> p some_val) as T by attac.
            apply HQueryOnly in T as (c & v & HEq & _).
            bullshit.
          * assert (PRecv handle0 =(Recv (n, Q) v)=> P v) as T by attac.
            apply HQueryOnly in T as (c & _ & _ & Hsrpc_n).
            apply C; eattac.
        + assert (PRecv handle0 =(Recv (n, Q) some_val)=> P some_val) as T by attac.
          kill T.
        + assert (PRecv handle0 =(Recv (n, Q) some_val)=> P some_val) as T by attac.
          apply HReplyOnly in T as (v & HEq).
          bullshit.
        + assert (PRecv handle0 =(Recv (n, R) some_val)=> P some_val) as T by attac.
          apply HQueryOnly in T as (c & v & HEq & _).
          bullshit.
        + assert (PRecv handle0 =(Recv (n, R) some_val)=> P some_val) as T by attac.
          kill T.
        + split; intros.
          * destruct (handle0 (m, Q)) eqn:HH; auto.
            assert (PRecv handle0 =(Recv (m, Q) some_val)=> p some_val) as T by attac.
            apply HReplyOnly in T as (v & HEq).
            bullshit.
          * assert (PRecv handle0 =(Recv (n, R) v)=> P v) as T by attac.
            apply HRecv in T as Hsrpc_n.
            apply C; eattac.
      - constructor.
        assert (PTau P =(Tau)=> P) as T by attac.
        assert (AnySRPC P) by eattac.
        attac.
    Qed.

    #[export] Hint Resolve SRPC_Decisive : LTS.


    Lemma SRPC_Decisive_q [S] :
      AnySRPC_pq S ->
      Decisive_q S.
    Proof. intros. destruct S; eattac. Qed.

    #[export] Hint Resolve SRPC_Decisive_q : LTS.


    Definition SRPC_net N := forall n, AnySRPC_pq (NetMod.get n N).

    Lemma SRPC_net_get [N n] : SRPC_net N -> AnySRPC_pq (NetMod.get n N).
    Proof. attac. Qed.

    #[export] Hint Resolve SRPC_net_get : LTS.


    Lemma SRPC_net_lock [N n0 n1] :
      SRPC_net N ->
      NetLocks.net_lock_on N n0 n1 ->
      exists c, SRPC_pq (Lock c n1) (NetMod.get n0 N).

    Proof.
      unfold NetLocks.net_lock_on, NetLocks.net_lock.
      intros; hsimpl in *.

      consider (exists s, pq_lock [s] (NetMod.get n0 N)) by eauto using SRPC_pq_get_lock.
      enough (n1 = s) by (subst; eauto using lock_SRPC_Lock_pq with LTS).

      enough (In n1 [s]) by attac.
      enough (incl L [s]) by attac.
      eauto using pq_lock_incl.
    Qed.


    Lemma trans_invariant_SRPC_net : trans_invariant SRPC_net always.

    Proof.
      unfold trans_invariant, SRPC_net.
      intros.

      consider (exists path, Path_of n [a] path) by eauto using path_of_exists.
      enough (NetMod.get n N0 =[path]=> NetMod.get n N1) by attac.
      eauto using path_of_ptrans with LTS.
    Qed.

    #[export] Hint Resolve trans_invariant_SRPC_net : inv.
    #[export] Hint Extern 10 (SRPC_net _) => solve_invariant : LTS.


    Lemma SRPC_net_lock_uniq [N] :
      SRPC_net N ->
      lock_uniq_type N.

    Proof.
      unfold SRPC_net, lock_uniq_type.
      intros.
      assert (AnySRPC_pq (NetMod.get n N)) by eauto with LTS.
      consider (exists c0, SRPC_pq (Lock c0 m0) (NetMod.get n N)) by eauto using SRPC_net_lock.
      consider (exists c1, SRPC_pq (Lock c1 m1) (NetMod.get n N)) by eauto using SRPC_net_lock.
      enough (Lock c0 m0 = Lock c1 m1) by attac.
      eauto with LTS.
    Qed.

    #[export] Hint Resolve SRPC_net_lock_uniq : LTS.


    Lemma SRPC_net_lock_neq_nil [N] :
      SRPC_net N ->
      lock_neq_nil_type N.

    Proof.
      unfold lock_neq_nil_type, NetLocks.net_lock.
      intros.

      consider (exists s, pq_lock [s] (NetMod.get n N)) by eauto using SRPC_pq_get_lock.
      destruct L; doubt.

      assert (incl [s] []) by eauto using pq_lock_incl.
      bullshit (In s []).
    Qed.

    #[export] Hint Resolve SRPC_net_lock_neq_nil : LTS.


    (* Lemma prop_transport_r__SRPC_net__lock_uniq : prop_transport_r SRPC_net lock_uniq_type (fun x => x). *)

    (* Proof. unfold prop_transport_r; simpl; intros; subst; now apply SRPC_net_lock_uniq. Qed. *)

    (* Lemma prop_transport_l__SRPC_net__lock_uniq : prop_transport_l lock_uniq_type SRPC_net (fun x => x). *)

    (* Proof. unfold prop_transport_l; simpl; intros; subst; now apply SRPC_net_lock_uniq. Qed. *)

    (* #[export] Hint Resolve prop_transport_r__SRPC_net__lock_uniq prop_transport_l__SRPC_net__lock_uniq : inv. *)
    (* #[export] Hint Extern 10 (lock_uniq_type _) => solve_invariant : LTS. *)


    Import NetLocks.


    (** [c] is the client of this process *)
    Definition proc_client (c : Name) (P : Proc) : Prop :=
      exists (srpcb : SRPC_Handle_State c), SRPC (Busy srpcb) P.


    Lemma mk_proc_client [c P] [srpcb : SRPC_Handle_State c] :
      SRPC (Busy srpcb) P -> proc_client c P.
    Proof. unfold proc_client. intros; eauto. Qed.
    #[export] Hint Immediate mk_proc_client : LTS.


    Lemma proc_client_uniq [c0 c1 : Name] [P : Proc] :
      proc_client c0 P ->
      proc_client c1 P ->
      c0 = c1.

    Proof.
      intros H0 H1.
      kill H0.
      kill H1.
      assert (Busy x = Busy x0) by (eapply SRPC_inv; eattac).
      kill H1.
    Qed.

    #[export] Hint Immediate proc_client_uniq : LTS.


    (** [c] is the client of this service (not necessarily handled at the moment) *)
    Inductive pq_client (c : Name) : PQued -> Prop  :=
    | PQH_in [I P O v] :
      List.In (c, Q, v) I ->
      pq_client c (pq I P O)

    | PQH_proc [I P O] :
      proc_client c P  ->
      pq_client c (pq I P O)

    | PQH_out [I P O v] :
      List.In (c, R, v) O ->
      pq_client c (pq I P O)
    .

    #[export] Hint Constructors pq_client : LTS.


    Fact pq_client_app_I_r [c I P O] I' :
      pq_client c (pq I P O) -> pq_client c (pq (I ++ I') P O).
    Proof. intros. kill H; eattac. Qed.

    Fact pq_client_app_I_l [c I P O] I' :
      pq_client c (pq I P O) -> pq_client c (pq (I' ++ I) P O).
    Proof. intros. kill H; eattac. Qed.

    Fact pq_client_app_O_r [c I P O] O' :
      pq_client c (pq I P O) -> pq_client c (pq I P (O ++ O')).
    Proof. intros. kill H; eattac. Qed.

    Fact pq_client_app_O_l [c I P O] O' :
      pq_client c (pq I P O) -> pq_client c (pq I P (O' ++ O)).
    Proof. intros. kill H; eattac. Qed.

    #[export] Hint Resolve pq_client_app_I_l pq_client_app_I_r pq_client_app_O_l pq_client_app_O_r : LTS.


    Definition mq_MQ MS := match MS with mq MQ _ _ => MQ end.
    Definition mq_M MS := match MS with mq _ M _ => M end.
    Definition mq_S MS := match MS with mq _ _ S' => S' end.
    Definition pq_I S := match S with pq I' _ _ => I' end.
    Definition pq_P S := match S with pq _ P _ => P end.
    Definition pq_O S := match S with pq _ _ O' => O' end.
    Definition mq_I MS := pq_I (mq_S MS).
    Definition mq_P MS := pq_P (mq_S MS).
    Definition mq_O MS := pq_O (mq_S MS).
    Definition mq_dI MS := pq_I (mq_S MS) ++ MQ_r (mq_MQ MS).
    Definition mq_dP MS := pq_P (mq_S MS).
    Definition mq_dO MS := MQ_s (mq_MQ MS) ++ pq_O (mq_S MS).

    #[export] Hint Transparent mq_MQ mq_M mq_S pq_I pq_P pq_O mq_I mq_P mq_O mq_dI mq_dP mq_dO : LTS.


    Definition SRPC_sane_Q_in (S : PQued) := forall c v v' I', Deq (c, Q) v (pq_I S) I' -> ~ List.In (c, Q, v') I'.
    Definition SRPC_sane_R_in (S : PQued) := forall s s' v v' I', Deq (s, R) v (pq_I S) I' -> ~ List.In (s', R, v') I'.
    Definition SRPC_sane_R_in_lock (S : PQued) := forall s v, List.In (s, R, v) (pq_I S) -> exists c, SRPC_pq (Lock c s) S.
    Definition SRPC_sane_Q_out_lock (S : PQued) := forall s v, List.In (s, Q, v) (pq_O S) -> exists c, SRPC_pq (Lock c s) S.
    Definition SRPC_sane_Q_out_last (S : PQued) := forall s v, ~ List.In (s, Q, v) (List.removelast (pq_O S)).
    Definition SRPC_sane_R_out_uniq (S : PQued) := forall c v v' O', Deq (c, R) v (pq_O S) O' -> ~ List.In (c, R, v') O'.
    Definition SRPC_sane_R_Q (S : PQued) := forall s v v', List.In (s, R, v) (pq_I S) -> ~ List.In (s, Q, v') (pq_O S).
    Definition SRPC_sane_Q_R (S : PQued) := forall s v v', List.In (s, Q, v) (pq_O S) -> ~ List.In (s, R, v') (pq_I S).
    Definition SRPC_sane_lock_Q (S : PQued) := forall c s, SRPC_pq (Lock c s) S -> pq_O S <> [] -> exists v, List.In (s, Q, v) (pq_O S).

    Definition SRPC_sane_in_Q_no_client (S : PQued) := forall c v, List.In (c, Q, v) (pq_I S) -> ~ proc_client c (pq_P S).
    Definition SRPC_sane_in_Q_no_out_R (S : PQued) := forall c v v', List.In (c, Q, v) (pq_I S) -> ~ List.In (c, R, v') (pq_O S).
    Definition SRPC_sane_client_no_out_R (S : PQued) := forall c v, proc_client c (pq_P S) -> ~ List.In (c, R, v) (pq_O S).


    #[export] Hint Transparent SRPC_sane_Q_in SRPC_sane_R_in SRPC_sane_R_in_lock SRPC_sane_Q_out_lock SRPC_sane_Q_out_last SRPC_sane_R_out_uniq SRPC_sane_R_Q SRPC_sane_Q_R SRPC_sane_lock_Q SRPC_sane_in_Q_no_client SRPC_sane_in_Q_no_out_R SRPC_sane_client_no_out_R : LTS.

    #[export] Hint Unfold SRPC_sane_Q_in SRPC_sane_R_in SRPC_sane_R_in_lock SRPC_sane_Q_out_lock SRPC_sane_Q_out_last SRPC_sane_R_out_uniq SRPC_sane_R_Q SRPC_sane_Q_R SRPC_sane_lock_Q SRPC_sane_in_Q_no_client SRPC_sane_in_Q_no_out_R SRPC_sane_client_no_out_R : SRPC.


    (** A much stronger version of SRPC_pq which holds in any network with the same premises *)
    Inductive SRPC_sane (srpc : SRPC_State) (S : PQued) : Prop :=
      SPRC_pq_net_

        (Hsrpc : SRPC_pq srpc S)

        (H_Q_in : SRPC_sane_Q_in S)

        (H_R_in : SRPC_sane_R_in S)

        (H_R_in_lock : SRPC_sane_R_in_lock S)

        (H_Q_out_lock : SRPC_sane_Q_out_lock S)

        (H_Q_out_last : SRPC_sane_Q_out_last S)

        (H_R_out_uniq : SRPC_sane_R_out_uniq S)

        (H_R_Q : SRPC_sane_R_Q S)

        (H_Q_R : SRPC_sane_Q_R S)

        (H_lock_Q : SRPC_sane_lock_Q S)

        (H_in_Q_no_client : SRPC_sane_in_Q_no_client S)

        (H_in_Q_no_out_R : SRPC_sane_in_Q_no_out_R S)

        (H_client_no_out_R : SRPC_sane_client_no_out_R S)

        : SRPC_sane srpc S.


    Lemma SRPC_sane_SRPC_inv [srpc : SRPC_State] [S] :
      SRPC_sane srpc S -> SRPC_pq srpc S.

    Proof. intros. kill H. Qed.

    Lemma SRPC_sane_Q_in_inv [srpc : SRPC_State] [c v v' I I' P O] :
      SRPC_sane srpc (pq I P O) ->
      Deq (c, Q) v I I' ->
      not (List.In (c, Q, v') I').
    Proof. intros. kill H. attac 1. Qed.

    Lemma SRPC_sane_R_in_inv [srpc : SRPC_State] [s s' v v' I I' P O] :
      SRPC_sane srpc (pq I P O) ->
      Deq (s, R) v I I' ->
      not (List.In (s', R, v') I').
    Proof. intros. kill H. attac 1. Qed.

    Lemma SRPC_sane_R_in_lock_inv [srpc : SRPC_State] [s v I P O] :
      SRPC_sane srpc (pq I P O) ->
      List.In (s, R, v) I ->
      exists c, srpc = Lock c s.
    Proof. intros. kill H. assert (exists c, SRPC_pq (Lock c s) (pq &I P &O)); eattac 1. Qed.

    Lemma SRPC_sane_Q_out_lock_inv [srpc : SRPC_State] [s v I P O] :
      SRPC_sane srpc (pq I P O) ->
      List.In (s, Q, v) O ->
      exists c, srpc = Lock c s.
    Proof. intros. kill H. assert (exists c, SRPC_pq (Lock c s) (pq &I P &O)); eattac 1. Qed.

    Lemma SRPC_sane_Q_out_last_inv [srpc : SRPC_State] [s v I P O] :
      SRPC_sane srpc (pq I P O) ->
       ~ (List.In (s, Q, v) (List.removelast O)).
    Proof. intros. kill H. eattac 1. Qed.

    Lemma SRPC_sane_Q_out_uniq_inv [srpc : SRPC_State] [c v v' I P O O'] :
      SRPC_sane srpc (pq I P O) ->
      Deq (c, R) v O O' ->
      ~ (List.In (c, R, v') O').
    Proof. intros. kill H. eattac 1. Qed.

    Lemma SRPC_sane_R_Q_inv [srpc : SRPC_State] [s v v' I P O] :
      SRPC_sane srpc (pq I P O) ->
      List.In (s, R, v) I -> not (List.In (s, Q, v') O).
    Proof. intros. kill H. eattac 1. Qed.

    Lemma SRPC_sane_Q_R_inv [srpc : SRPC_State] [s v v' I P O] :
      SRPC_sane srpc (pq I P O) ->
      List.In (s, Q, v) O -> not (List.In (s, R, v') I).
    Proof. intros. kill H. eattac 1. Qed.

    Lemma SRPC_sane_lock_Q_inv [c s I P O] :
      SRPC_sane (Lock c s) (pq I P O) ->
      O <> [] ->
      exists v, List.In (s, Q, v) O.
    Proof. intros. kill H. eattac 1. Qed.

    Lemma SRPC_sane_Q_excl_R_inv [srpc : SRPC_State] [c v v' I P O] :
      SRPC_sane srpc (pq I P O) ->
      List.In (c, Q, v) I ->
      ~ List.In (c, R, v') O.
    Proof. intros. kill H. eattac 1. Qed.

    Lemma SRPC_sane_Q_excl_c_inv [srpc : SRPC_State] [c v I P O] :
      SRPC_sane srpc (pq I P O) ->
      List.In (c, Q, v) I ->
      ~ proc_client c P.
    Proof. intros. kill H. eattac 1. Qed.

    Lemma SRPC_sane_R_excl_Q_inv [srpc : SRPC_State] [c v v' I P O] :
      SRPC_sane srpc (pq I P O) ->
      List.In (c, R, v) O ->
      ~ List.In (c, Q, v') I.
    Proof. intros. kill H. eattac 1. Qed.

    Lemma SRPC_sane_R_excl_c_inv [srpc : SRPC_State] [c v I P O] :
      SRPC_sane srpc (pq I P O) ->
      List.In (c, Q, v) I ->
      ~ proc_client c P.
    Proof. intros. kill H. eattac 1. Qed.

    Lemma SRPC_sane_c_excl_Q_inv [srpc : SRPC_State] [c v I P O] :
      SRPC_sane srpc (pq I P O) ->
      proc_client c P ->
      ~ List.In (c, Q, v) I.
    Proof. intros. kill H. eattac 1. Qed.

    Lemma SRPC_sane_c_excl_R_inv [srpc : SRPC_State] [c v I P O] :
      SRPC_sane srpc (pq I P O) ->
      proc_client c P ->
      ~ List.In (c, R, v) O.
    Proof. intros. kill H. eattac 1. Qed.


    #[export] Hint Resolve
      SRPC_sane_SRPC_inv
      SRPC_sane_Q_in_inv
      SRPC_sane_R_in_inv
      SRPC_sane_R_in_lock_inv
      SRPC_sane_Q_out_lock_inv
      SRPC_sane_Q_out_last_inv
      SRPC_sane_Q_out_uniq_inv
      SRPC_sane_R_Q_inv
      SRPC_sane_Q_R_inv
      SRPC_sane_lock_Q_inv
      SRPC_sane_Q_excl_R_inv
      SRPC_sane_Q_excl_c_inv
      SRPC_sane_R_excl_Q_inv
      SRPC_sane_R_excl_c_inv
      SRPC_sane_c_excl_Q_inv
      SRPC_sane_c_excl_R_inv
      : LTS.



    (* TODO why... *)
    Lemma eq_some_neq_none [T] : forall (x : T) a, a = Some x -> a <> None. Proof. eattac. Qed.
    Hint Resolve eq_some_neq_none : LTS.


    Lemma SRPC_sane__Q_in_inv_l [srpc] [S] [I0 I1 c v v'] :
      SRPC_sane srpc S ->
      pq_I S = I0 ++ I1 ->
      List.In (c, Q, v) I0 ->
      ~ List.In (c, Q, v') I1.
    Proof. intros; destruct S as [I P O].
           consider (exists v'' I', Deq (c, Q) v'' (I0 ++ I1) I')
             by (enough (List.In (c, Q, v) (I0 ++ I1)); eattac).
           consider (exists v''' I0', Deq (c, Q) v''' I0 I0') by eattac.
           assert (~ List.In (c, Q, v') I') by eattac.
           consider (I' = I0' ++ I1 /\ v'' = v''') by eauto using Deq_app_and_l.
           attac.
    Qed.

    Lemma SRPC_sane__Q_in_inv_r [srpc] [S] [I0 I1 c v v'] :
      SRPC_sane srpc S ->
      pq_I S = I0 ++ I1 ->
      List.In (c, Q, v) I1 ->
      ~ List.In (c, Q, v') I0.
    Proof. intros; destruct S as [I P O].
           consider (exists v'' I', Deq (c, Q) v'' (I0 ++ I1) I')
             by (enough (List.In (c, Q, v) (I0 ++ I1)); eattac).
           intros ?.
           consider (exists v''' I0', Deq (c, Q) v''' I0 I0') by eattac.
           assert (~ List.In (c, Q, v) I') by eattac.
           consider (I' = I0' ++ I1 /\ v'' = v''') by eauto using Deq_app_and_l.
           attac.
    Qed.

    Lemma SRPC_sane__Q_in_inv_eq [srpc] [S] [I0 c v v'] :
      SRPC_sane srpc S ->
      pq_I S = I0 ->
      List.In (c, Q, v) I0 ->
      List.In (c, Q, v') I0 ->
      v' = v.
    Proof.
      intros; destruct S as [I P O].
      consider (exists v'' I1, Deq (c, Q) v'' I0 I1) by eattac.
      consider (exists I00 I01, I0 = I00 ++ (c, Q, v'') :: I01
                                /\ I1 = I00 ++ I01
                                /\ forall v''', ~ List.In (c, Q, v''') I00) by eauto using Deq_split.
      hsimpl in *.
      repeat (destruct `(_ \/ _); doubt); eattac.
      - bullshit (List.In (c, Q, v) (I00 ++ I01)) by eattac.
      - bullshit (List.In (c, Q, v') (I00 ++ I01)) by eattac.
      - bullshit (List.In (c, Q, v') (I00 ++ I01)) by eattac.
    Qed.

    Lemma SRPC_sane__R_in_inv_l [srpc] [S] [I0 I1 s s' v v'] :
      SRPC_sane srpc S ->
      pq_I S = I0 ++ I1 ->
      List.In (s, R, v) I0 ->
      ~ List.In (s', R, v') I1.
    Proof. intros; destruct S as [I P O].
           consider (exists v'' I', Deq (s, R) v'' (I0 ++ I1) I')
             by (enough (List.In (s, R, v) (I0 ++ I1)); eattac).
           consider (exists v''' I0', Deq (s, R) v''' I0 I0') by eattac.
           assert (~ List.In (s', R, v') I') by eattac.
           consider (I' = I0' ++ I1 /\ v'' = v''') by eauto using Deq_app_and_l.
           attac.
    Qed.

    Lemma SRPC_sane__R_in_inv_r [srpc] [S] [I0 I1 s s' v v'] :
      SRPC_sane srpc S ->
      pq_I S = I0 ++ I1 ->
      List.In (s, R, v) I1 ->
      ~ List.In (s', R, v') I0.
    Proof. intros; destruct S as [I P O].
           consider (exists v'' I', Deq (s, R) v'' (I0 ++ I1) I')
             by (enough (List.In (s, R, v) (I0 ++ I1)); eattac).
           intros ?.
           consider (exists v''' I0', Deq (s', R) v''' I0 I0') by eattac.
           assert (~ List.In (s', R, v') I') by eattac.
           assert (~ List.In (s, R, v) I') by eattac.
           smash_eq s s'.
           - consider (I' = I0' ++ I1 /\ v'' = v''') by eauto using Deq_app_and_l; attac.
           - assert ((s, R) <> (s', R)) by eattac.
             absurd (List.In (s', R, v') I'); auto.
             assert (List.In (s', R, v') (I0 ++ I1)) by eattac.
             ltac1:(apply ->Deq_neq_In).
             apply H8.
             consider (exists v'''' I0'', Deq (s, R) v'''' (I0 ++ I1) I0'') by eattac.
             2: attac.
             eauto.
    Qed.

    Lemma SRPC_sane__R_in_inv_eq_v [srpc] [S] [I0 s s' v v'] :
      SRPC_sane srpc S ->
      pq_I S = I0 ->
      List.In (s, R, v) I0 ->
      List.In (s', R, v') I0 ->
      v' = v.
    Proof.
      intros; destruct S as [I P O].
      consider (exists v'' I1, Deq (s, R) v'' I0 I1) by eattac.
      consider (exists I00 I01, I0 = I00 ++ (s, R, v'') :: I01
                                /\ I1 = I00 ++ I01
                                /\ forall v''', ~ List.In (s, R, v''') I00) by eauto using Deq_split.
      hsimpl in *.
      repeat (destruct `(_ \/ _); doubt); eattac.
      - bullshit (List.In (s', R, v') (I00 ++ I01)) by eattac.
      - smash_eq s s'; attac.
        bullshit (List.In (s, R, v) (I00 ++ I01)) by eattac.
      - bullshit (List.In (s', R, v) (I00 ++ I01)) by eattac.
      - bullshit (List.In (s', R, v') (I00 ++ I01)) by eattac.
      - bullshit (List.In (s', R, v') (I00 ++ I01)) by eattac.
    Qed.

    Lemma SRPC_sane__R_in_inv_eq_s [srpc] [S] [I0 s s' v v'] :
      SRPC_sane srpc S ->
      pq_I S = I0 ->
      List.In (s, R, v) I0 ->
      List.In (s', R, v') I0 ->
      s' = s.
    Proof.
      intros; destruct S as [I P O].
      smash_eq s' s.
      consider (exists v'' I1, Deq (s, R) v'' I0 I1) by eattac.
      consider (exists I00 I01, I0 = I00 ++ (s, R, v'') :: I01
                                /\ I1 = I00 ++ I01
                                /\ forall v''', ~ List.In (s, R, v''') I00) by eauto using Deq_split.
      hsimpl in *.
      repeat (destruct `(_ \/ _); doubt); eattac.
      - bullshit (List.In (s', R, v') (I00 ++ I01)) by eattac.
      - bullshit (List.In (s, R, v) (I00 ++ I01)) by eattac.
      - bullshit (List.In (s', R, v') (I00 ++ I01)) by eattac.
      - bullshit (List.In (s', R, v') (I00 ++ I01)) by eattac.
    Qed.

    Lemma SRPC_sane__R_in_lock_inv [c s s'] [S] [I0] [v] :
      SRPC_sane (Lock c s) S ->
      pq_I S = I0 ->
      List.In (s', R, v) I0 ->
      s' = s.
    Proof.
      intros.
      destruct S.
      consider (exists c', (Lock c s) = (Lock c' s')) by eattac.
    Qed.

    Lemma SRPC_sane__Q_out_lock_inv [c s s'] [S] [O0] [v] :
      SRPC_sane (Lock c s) S ->
      pq_O S = O0 ->
      List.In (s', Q, v) O0 ->
      s' = s.
    Proof.
      intros.
      destruct S.
      consider (exists c', (Lock c s) = (Lock c' s')) by eattac.
    Qed.

    Lemma SRPC_sane__Q_out_last_inv [srpc] [S] [O0 O1 s v] :
      SRPC_sane srpc S ->
      O1 <> [] ->
      pq_O S = O0 ++ O1 ->
      List.In (s, Q, v) (O0 ++ O1) ->
      List.In (s, Q, v) O1.
    Proof.
      intros.
      destruct S as [I0 P0 O'].
      assert (~ List.In (s, Q, v) (List.removelast O')) by eattac.
      hsimpl in *.
      assert (List.In (s, Q, v) O0 \/ List.In (s, Q, v) O1) as [|] by eattac; attac.
      enough (~ List.In (s, Q, v) (O0 ++ List.removelast O1)) by eattac.
      rewrite removelast_app in *; attac.
    Qed.

    Lemma SRPC_sane__Q_out_last_nil_inv [srpc] [S] [O0 O1 s v] :
      SRPC_sane srpc S ->
      pq_O S = O0 ++ (s, Q, v) :: O1 ->
      O1 = [].
    Proof.
      intros.
      destruct S as [I0 P0 O'].
      assert (~ List.In (s, Q, v) (List.removelast O')) by eattac.
      hsimpl in *.
      clear - H1.
      induction O1 using rev_ind; attac.
      replace (O0 ++ (s, Q, v) :: O1 ++ [x]) with ((O0 ++ (s, Q, v) :: O1) ++ [x]) by eattac.
      simpl in *.
      rewrite removelast_last in *.
      bullshit.
    Qed.


    Lemma SRPC_sane__R_out_inv_l [srpc] [S] [O0 O1 c v v'] :
      SRPC_sane srpc S ->
      pq_O S = O0 ++ O1 ->
      List.In (c, R, v) O0 ->
      ~ List.In (c, R, v') O1.
    Proof. intros; destruct S as [I P O].
           consider (exists v'' O', Deq (c, R) v'' (O0 ++ O1) O')
             by (enough (List.In (c, R, v) (O0 ++ O1)); eattac).
           consider (exists v''' O0', Deq (c, R) v''' O0 O0') by eattac.
           assert (~ List.In (c, R, v') O') by eattac.
           consider (O' = O0' ++ O1 /\ v'' = v''') by eauto using Deq_app_and_l.
           attac.
    Qed.

    Lemma SRPC_sane__R_out_inv_r [srpc] [S] [O0 O1 c v v'] :
      SRPC_sane srpc S ->
      pq_O S = O0 ++ O1 ->
      List.In (c, R, v) O1 ->
      ~ List.In (c, R, v') O0.
    Proof. intros; destruct S as [I P O].
           consider (exists v'' O', Deq (c, R) v'' (O0 ++ O1) O')
             by (enough (List.In (c, R, v) (O0 ++ O1)); eattac).
           intros ?.
           consider (exists v''' O0', Deq (c, R) v''' O0 O0') by eattac.
           assert (~ List.In (c, R, v') O') by eattac.
           assert (~ List.In (c, R, v) O') by eattac.
           consider (O' = O0' ++ O1 /\ v'' = v''') by eauto using Deq_app_and_l; attac.
    Qed.

    Lemma SRPC_sane__R_out_inv_eq_v [srpc] [S] [O0 c v v'] :
      SRPC_sane srpc S ->
      pq_O S = O0 ->
      List.In (c, R, v) O0 ->
      List.In (c, R, v') O0 ->
      v' = v.
    Proof.
      intros; destruct S as [I P O].
      consider (exists v'' O1, Deq (c, R) v'' O0 O1) by eattac.
      consider (exists O00 O01, O0 = O00 ++ (c, R, v'') :: O01
                                /\ O1 = O00 ++ O01
                                /\ forall v''', ~ List.In (c, R, v''') O00) by eauto using Deq_split.
      hsimpl in *.
      repeat (destruct `(_ \/ _); doubt); eattac.
      - bullshit (List.In (c, R, v) (O00 ++ O01)) by eattac.
      - bullshit (List.In (c, R, v') (O00 ++ O01)) by eattac.
      - bullshit (List.In (c, R, v') (O00 ++ O01)) by eattac.
    Qed.

    #[export] Hint Resolve SRPC_sane__Q_in_inv_l SRPC_sane__Q_in_inv_r SRPC_sane__R_in_inv_l SRPC_sane__R_in_inv_r SRPC_sane__R_out_inv_l SRPC_sane__R_out_inv_r : LTS.

    #[export] Hint Rewrite -> SRPC_sane__Q_in_inv_eq SRPC_sane__R_in_inv_eq_v SRPC_sane__R_in_inv_eq_s SRPC_sane__R_in_lock_inv SRPC_sane__Q_out_lock_inv SRPC_sane__Q_out_last_nil_inv SRPC_sane__Q_out_last_inv SRPC_sane__R_out_inv_eq_v using spank : LTS LTS_concl.


    (** If an SRPC service is locked after an action, then it's either a send (todo: from its output
    queue) or a non-unlocking message *)
    Lemma SRPC_sane_send_lock [srpc n a S0 S1] :
      SRPC_sane srpc S0 -> (*  TODO : to net and remove n'<>n *)
      pq_lock [n] S1 ->
      (S0 =(a)=> S1) ->
      match a with
      | Send (_, t) _ => t = Q
      | Recv (n', t) _ => t = Q \/ n' <> n
      | _ => False
      end.

    Proof with (eauto with LTS).
      intros Hsrpc0 HL1 T.

      destruct S0 as [I0 P0 O0].
      destruct S1 as [I1 P1 O1].


      kill HL1.
      inversion T; subst.
      - destruct n0 as [n' t].
        destruct t; auto.

        destruct (Name.eq_dec n' n); subst; auto.
        destruct P1; doubt.
        kill HEnq.

        absurd (~ List.In (n, R, v) (I0 ++ [(n, R, v)])); attac.
      - kill Hsrpc0.
        assert (AnySRPC_pq (pq I0 P0 [])) as Hsrpc0' by attac.
        apply (SRPC_send_lock `(AnySRPC P0) `(proc_lock [n] P1) `(P0 =( Recv n0 v )=> P1)).
      - apply (Enq_nil HEnq).

      - destruct n0 as [n' t].

        destruct t; auto.
        exfalso.

        kill Hsrpc0.

        assert (AnySRPC_pq (pq I1 P1 [(n', R, v)])) as Hsrpc0' by attac.

        specialize (lock_SRPC_Lock `(AnySRPC P1) `(proc_lock [n] P1)) as [c Hsrpc_L].

        apply (SRPC_inv Hsrpc) in Hsrpc_L. subst.
        edestruct H_lock_Q; eauto; doubt.

      - assert (AnySRPC P0) as Hsrpc by (kill Hsrpc0; eattac).
        apply (SRPC_send_lock Hsrpc  `(proc_lock [n] P1) `(P0 =( Tau )=> P1)).
    Qed.


    Lemma SRPC_net_get_lock [N n0 n1] :
      SRPC_net N ->
      net_lock_on N n0 n1 ->
      pq_lock [n1] (NetMod.get n0 N).

    Proof.
      intros.
      enough (net_lock N [n1] n0) by eauto with LTS.
      eauto using lock_singleton with LTS.
    Qed.

    #[export] Hint Resolve SRPC_net_get_lock : LTS.


    Lemma SRPC_net_no_relock [N0 N1 a n n0 n1] :
      SRPC_net N0 ->
      net_lock_on N0 n n0 ->
      net_lock_on N1 n n1 ->
      (N0 =(a)=> N1) ->
      n0 = n1.

    Proof.
      intros.
      assert (AnySRPC_pq (NetMod.get n N0)) by attac.
      assert (AnySRPC_pq (NetMod.get n N1)) by attac.
      assert (pq_lock [n0] (NetMod.get n N0)) by attac.
      assert (pq_lock [n1] (NetMod.get n N1)) by attac.

      destruct a.
      - smash_eq n n2; compat_hsimpl in * |-; hsimpl in * |-.
        + bullshit.
        + enough (In n0 [n1]) by attac.
          enough (incl [n0] [n1]) by attac.
          attac.
      - assert (n <> n2) by eauto using net_lock_on_no_send.
        smash_eq n n3.
        + hsimpl in * |-; hsimpl in * |-.
          eauto using SRPC_pq_no_relock.
        + replace (NetMod.get n N1) with (NetMod.get n N0).
          * enough (In n0 [n1]) by attac.
            enough (incl [n0] [n1]) by attac.
            attac.
          * eapply (@act_particip_stay PQued PAct); attac.
    Qed.


    (* Every process is individually sane *)
    Definition SRPC_sane_net N := forall n, exists srpc, SRPC_sane srpc (NetMod.get n N).


    (* If n0 is locked on n1, then n1 handles the query of n0 *)
    Definition locks_sound N := forall n0 n1,
        net_lock_on N n0 n1 ->
        pq_client n0 (NetMod.get n1 N).


    (* If n1 handles a query from n0, then n0 is locked on n1   *)
    Definition locks_complete N := forall n0 n1,
        pq_client n0 (NetMod.get n1 N) -> net_lock_on N n0 n1.


    Inductive net_sane (N : PNet) : Prop :=
    | NetSane
        (H_Sane_SRPC : SRPC_sane_net N)
        (H_lock_sound : locks_sound N)
        (H_lock_complete : locks_complete N)
      : net_sane N.


    Lemma net_sane_SRPC_sane [N : PNet] : net_sane N -> SRPC_sane_net N.
    Proof. intros. kill H. intros ?. eauto with LTS. Qed.

    Lemma net_sane_SRPC [N : PNet] : net_sane N -> SRPC_net N.
    Proof. intros. kill H. intros ?. destruct (H_Sane_SRPC n). eauto with LTS. Qed.

    Lemma net_sane_lock_client [N S n0 n1] : net_sane N -> NetMod.get n1 N = S -> net_lock_on N n0 n1 -> pq_client n0 S.
    Proof. intros. kill H. auto. Qed.

    Lemma net_sane_client_lock [N S n0 n1] : net_sane N -> NetMod.get n1 N = S -> pq_client n0 S -> net_lock_on N n0 n1.
    Proof. intros. kill H. auto. Qed.


    #[export] Hint Resolve net_sane_SRPC  net_sane_SRPC_sane net_sane_lock_client net_sane_client_lock : LTS.


    Section Inversions.
      (* These hints should not quadrate with SRPC_pq variants because net_sane does not expose
      SRPC_sane *)

      Lemma net_sane_SRPC_sane_ [N S n] :
        net_sane N ->
        NetMod.get n N = S ->
        exists srpc, SRPC_sane srpc S.
      Proof.
        intros. kill H. specialize (H_Sane_SRPC n) as [srpc H]. eauto with LTS.
      Qed.

      Lemma net_sane_AnySrpc [N S n] :
        net_sane N ->
        NetMod.get n N = S ->
        AnySRPC_pq S.
      Proof.
        intros. kill H. specialize (H_Sane_SRPC n) as [srpc H]. eauto with LTS.
      Qed.

      Lemma net_sane_in_net_Q_in [N n c v v' I I' P O] :
        net_sane N ->
        NetMod.get n N = pq I P O ->
        Deq (c, Q) v I I' ->
        not (List.In (c, Q, v') I').
      Proof. intros. kill H. specialize (H_Sane_SRPC n) as [srpc [*]]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma net_sane_in_net_R_in [N n s s' v v' I I' P O] :
        net_sane N ->
        NetMod.get n N = pq I P O ->
        Deq (s, R) v I I' ->
        not (List.In (s', R, v') I').
      Proof. intros. kill H; specialize (H_Sane_SRPC n) as [srpc [*]]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma net_sane_in_net_R_in_lock [N n s v I P O] :
        net_sane N ->
        NetMod.get n N = pq I P O ->
        List.In (s, R, v) I ->
        exists c, SRPC_pq (Lock c s) (NetMod.get n N).
      Proof. intros. kill H; specialize (H_Sane_SRPC n) as [srpc H]. rewrite H0 in *. consider (exists c, srpc = Lock c s); eattac.
      Qed.

      Lemma net_sane_in_net_Q_out_lock [N n s v I P O] :
        net_sane N ->
        NetMod.get n N = pq I P O ->
        List.In (s, Q, v) O ->
        exists c, SRPC_pq (Lock c s) (NetMod.get n N).
      Proof.
        intros. kill H; specialize (H_Sane_SRPC n) as [srpc H]. rewrite H0 in *. consider (exists c, srpc = Lock c s); eattac.
      Qed.

      Lemma net_sane_in_net_Q_out_last [N n s v I P O] :
        net_sane N ->
        NetMod.get n N = pq I P O ->
        ~ (List.In (s, Q, v) (List.removelast O)).
      Proof. intros. kill H; specialize (H_Sane_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma net_sane_in_net_Q_out_uniq [N n c v v' I P O O'] :
        net_sane N ->
        NetMod.get n N = pq I P O ->
        Deq (c, R) v O O' ->
        ~ (List.In (c, R, v') O').
      Proof. intros. kill H; specialize (H_Sane_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma net_sane_in_net_R_Q [N n s v v' I P O] :
        net_sane N ->
        NetMod.get n N = pq I P O ->
        List.In (s, R, v) I -> not (List.In (s, Q, v') O).
      Proof. intros. kill H; specialize (H_Sane_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma net_sane_in_net_Q_R [N n s v v' I P O] :
        net_sane N ->
        NetMod.get n N = pq I P O ->
        List.In (s, Q, v) O -> not (List.In (s, R, v') I).
      Proof. intros. kill H; specialize (H_Sane_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma net_sane_in_net_Q_excl_R [N n c v v' I P O] :
        net_sane N ->
        NetMod.get n N = pq I P O ->
        List.In (c, Q, v) I ->
        ~ List.In (c, R, v') O.
      Proof. intros. kill H; specialize (H_Sane_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma net_sane_in_net_Q_excl_c [N n c v I P O] :
        net_sane N ->
        NetMod.get n N = pq I P O ->
        List.In (c, Q, v) I ->
        ~ proc_client c P.
      Proof. intros. kill H; specialize (H_Sane_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma net_sane_in_net_R_excl_Q [N n c v v' I P O] :
        net_sane N ->
        NetMod.get n N = pq I P O ->
        List.In (c, R, v) O ->
        ~ List.In (c, Q, v') I.
      Proof. intros. kill H; specialize (H_Sane_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma net_sane_in_net_R_excl_c [N n c v I P O] :
        net_sane N ->
        NetMod.get n N = pq I P O ->
        List.In (c, Q, v) I ->
        ~ proc_client c P.
      Proof. intros. kill H; specialize (H_Sane_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma net_sane_in_net_c_excl_Q [N n c v I P O] :
        net_sane N ->
        NetMod.get n N = pq I P O ->
        proc_client c P ->
        ~ List.In (c, Q, v) I.
      Proof. intros. kill H; specialize (H_Sane_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma net_sane_in_net_c_excl_R [N n c v I P O] :
        net_sane N ->
        NetMod.get n N = pq I P O ->
        proc_client c P ->
        ~ List.In (c, R, v) O.
      Proof. intros. kill H; specialize (H_Sane_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.
    End Inversions.


    #[export] Hint Resolve
      net_sane_SRPC_sane_
      net_sane_AnySrpc
      net_sane_in_net_Q_in
      net_sane_in_net_R_in
      net_sane_in_net_R_in_lock
      net_sane_in_net_Q_out_lock
      net_sane_in_net_Q_out_last
      net_sane_in_net_Q_out_uniq
      net_sane_in_net_R_Q
      net_sane_in_net_Q_R
      net_sane_in_net_Q_excl_R
      net_sane_in_net_Q_excl_c
      net_sane_in_net_R_excl_Q
      net_sane_in_net_R_excl_c
      net_sane_in_net_c_excl_Q
      net_sane_in_net_c_excl_R
      : LTS.


    Lemma pq_tau_no_lock_l [S0 S1 L] :
      (S0 =(Tau)=> S1) ->
      ~ pq_lock L S0.

    Proof.
      intros; intros ?.
      consider (_ =(_)=> _); doubt.
    Qed.


    Lemma SRPC_tau_no_lock_r [S0 S1 L] :
      AnySRPC_pq S0 ->
      (S0 =(Tau)=> S1) ->
      ~ pq_lock L S1.

    Proof.
      intros; intros ?.
      consider (exists s, pq_lock [s] S1) by eauto using SRPC_pq_get_lock with LTS.
      consider (exists c, SRPC_pq (Lock c s) S1) by eauto using lock_SRPC_Lock_pq with LTS.
      consider (_ =(_)=> _); consider (pq_lock _ _); doubt; simpl in *.
      - destruct n as [n [|]].
        + assert (SRPC (Work n) P1) by eauto using SRPC_inv_recv_Q_r.
          bullshit (Work n = Lock c s) by attac.
        + consider (exists c', SRPC (Work c') P1) by eauto using SRPC_inv_recv_R_r.
          bullshit (Work c' = Lock c s) by attac.
      - consider (exists c', SRPC (Work c') P1) by eauto using SRPC_inv_tau_r.
        bullshit (Work c' = Lock c s) by attac.
    Qed.


    Lemma pq_send_no_lock_l [S0 S1 nc v L] :
      (S0 =(Send nc v)=> S1) ->
      ~ pq_lock L S0.

    Proof.
      intros; intros ?.
      consider (_ =(_)=> _).
    Qed.


    Lemma SRPC_sane_send_R_no_lock_r [srpc S0 S1 n v L] :
      SRPC_sane srpc S0 ->
      (S0 =(Send (n, R) v)=> S1) ->
      ~ pq_lock L S1.

    Proof.
      intros; intros ?.
      consider (exists s, pq_lock [s] S1) by eauto using SRPC_pq_get_lock with LTS.
      consider (exists c, SRPC_pq (Lock c s) S1) by eauto using lock_SRPC_Lock_pq with LTS.
      consider (_ =(_)=> _); simpl in *.
      consider (pq_lock _ _).
      assert (SRPC_pq srpc (pq I0 P0 [(n, R, v)])) by eattac; simpl in *.
      consider (srpc = Lock c s) by eauto using SRPC_inv.
      consider (exists v', In (s, Q, v') [(n, R, v)]) by eattac.
    Qed.

    Lemma SRPC_sane_send_Q_lock [srpc S0 S1 n v] :
      SRPC_sane srpc S0 ->
      (S0 =(Send (n, Q) v)=> S1) ->
      pq_lock [n] S1.

    Proof.
      intros.
      assert (SRPC_pq srpc S0) by attac.
      consider (_ =(_)=> _).
      assert (SRPC_sane srpc (pq I0 P0 ([] ++ (n, Q, v) :: O1))) by auto.
      consider (O1 = []) by (eapply SRPC_sane__Q_out_last_nil_inv with (O0:=[]); unfold pq_O; eauto).
      consider (exists c, srpc = Lock c n) by eauto with LTS.
      simpl in *.
      eattac.
    Qed.

    Lemma SRPC_sane_send_Q_SRPC_lock [srpc S0 S1 s v] :
      SRPC_sane srpc S0 ->
      (S0 =(Send (s, Q) v)=> S1) ->
      exists c, srpc = Lock c s.

    Proof.
      intros.
      assert (AnySRPC_pq S1) by eattac.
      assert (pq_lock [s] S1) by eauto using SRPC_sane_send_Q_lock.
      consider (exists c, SRPC_pq (Lock c s) S1) by eauto using lock_SRPC_Lock_pq.
      attac.
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


    Lemma SRPC_sane_new_lock_send_Q [srpc S0 S1 a L] :
      SRPC_sane srpc S0 ->
      ~ pq_lock L S0 ->
      pq_lock L S1 ->
      (S0 =(a)=> S1) ->
      exists n v, a = Send (n, Q) v /\ In n L.

    Proof.
      intros.
      destruct a.
      - destruct n as [n [|]].
        + assert (pq_lock [n] S1) by eauto using SRPC_sane_send_Q_lock.
          exists n, v.
          split; auto.
          enough (incl [n] L) by attac.
          eauto with LTS.
        + absurd (pq_lock L S1); eauto using SRPC_sane_send_R_no_lock_r.
      - absurd (pq_lock L S1); eauto using pq_recv_no_new_lock.
      - absurd (pq_lock L S1); eauto using SRPC_tau_no_lock_r with LTS.
    Qed.


    Lemma net_ind_of (n : Name) : forall [Node Act : Set] {gen_Act_Act : gen_Act Act} {LTS_node : LTS Act Node}
                                         (P : NAct (Act:=Act) -> NetMod.t Node -> NetMod.t Node -> Prop),

        (forall (N0 N1 : NetMod.t Node) a, ia a -> @trans Act Node LTS_node a (NetMod.get n N0) (NetMod.get n N1) -> P (NTau n a) N0 N1) ->
        (forall (N0 N1 : NetMod.t Node) a m, m <> n -> ia a -> (NetMod.get n N0 = NetMod.get n N1) -> P (NTau m a) N0 N1) ->
        (forall (N0 N1 : NetMod.t Node) t v S0, @trans Act Node LTS_node (send (n, t) v) (NetMod.get n N0) S0 -> @trans Act Node LTS_node (recv (n, t) v) S0 (NetMod.get n N1) -> P (NComm n n t v) N0 N1) ->
        (forall (N0 N1 : NetMod.t Node) t v m, m <> n -> @trans Act Node LTS_node (send (m, t) v) (NetMod.get n N0) (NetMod.get n N1) -> P (NComm n m t v) N0 N1) ->
        (forall (N0 N1 : NetMod.t Node) t v m, m <> n -> @trans Act Node LTS_node (recv (m, t) v) (NetMod.get n N0) (NetMod.get n N1) -> P (NComm m n t v) N0 N1) ->
        (forall (N0 N1 : NetMod.t Node) t v m0 m1, m0 <> n -> m1 <> n -> (NetMod.get n N0 = NetMod.get n N1) -> P (NComm m0 m1 t v) N0 N1) ->
        (forall (a : NAct(Act:=Act)) (N0 N1 : NetMod.t Node), NTrans a N0 N1 -> P a N0 N1).

    Proof.
        intros.
        repeat (match! goal with [h : _ |- _] => let hh := hyp h in specialize ($hh N0 N1) end).

        consider (_ =(_)=> _); compat_hsimpl in *.
        - repeat (match! goal with [h : _ |- _] => let hh := hyp h in specialize ($hh a0) end).
          smash_eq n n0.
          + eapply H; hsimpl; auto.
          + eapply H0; hsimpl; auto.
        - repeat (match! goal with [h : _ |- _] => let hh := hyp h in specialize ($hh &t &v) end).
          smash_eq n n0; try (smash_eq n n').
          + eapply H1; compat_hsimpl in *; eauto.
          + eapply H2; compat_hsimpl; eauto.
          + eapply H3; compat_hsimpl in *; eauto.
          + eapply H4; compat_hsimpl; eauto.
      Qed.


    (* Lemma net_ind_off (n : Name) : forall [Node Act : Set] {gen_Act_Act : gen_Act Act} {LTS_node : LTS Act Node} *)
    (*                                      (P : NAct (Act:=Act) -> NetMod.t Node -> NetMod.t Node -> Name -> Prop), *)

    (*     (forall (N0 N1 : NetMod.t Node) a, ia a -> @trans Act Node LTS_node a (NetMod.get n N0) (NetMod.get n N1) -> P (NTau n a) N0 N1 n) -> *)
    (*     (forall (N0 N1 : NetMod.t Node) a m, m <> n -> ia a -> (NetMod.get n N0 = NetMod.get n N1) -> P (NTau m a) N0 N1 n) -> *)
    (*     (forall (N0 N1 : NetMod.t Node) t v S0, @trans Act Node LTS_node (send (n, t) v) (NetMod.get n N0) S0 -> @trans Act Node LTS_node (recv (n, t) v) S0 (NetMod.get n N1) -> P (NComm n n t v) N0 N1 n) -> *)
    (*     (forall (N0 N1 : NetMod.t Node) t v m, m <> n -> @trans Act Node LTS_node (send (m, t) v) (NetMod.get n N0) (NetMod.get n N1) -> P (NComm n m t v) N0 N1 n) -> *)
    (*     (forall (N0 N1 : NetMod.t Node) t v m, m <> n -> @trans Act Node LTS_node (recv (m, t) v) (NetMod.get n N0) (NetMod.get n N1) -> P (NComm m n t v) N0 N1 n) -> *)
    (*     (forall (N0 N1 : NetMod.t Node) t v m0 m1, m0 <> n -> m1 <> n -> (NetMod.get n N0 = NetMod.get n N1) -> P (NComm m0 m1 t v) N0 N1 n) -> *)
    (*     (forall (a : NAct(Act:=Act)) (N0 N1 : NetMod.t Node), NTrans a N0 N1 -> P a N0 N1 n). *)
    (* Admitted. *)


    Lemma SRPC_net_tau_no_lock [N0 N1 n0 n1 a] :
      SRPC_net N0 ->
      (N0 =(NTau n0 a)=> N1) ->
      ~ net_lock_on N1 n0 n1.

    Proof.
      intros.
      enough (forall L, ~ pq_lock L (NetMod.get n0 N1)) by (unfold net_lock_on, net_lock in *; eattac); intros.

      remember (NTau n0 a) as na.
      induction H0 using (net_ind_of n0); hsimpl in *; doubt.
      eauto using SRPC_tau_no_lock_r with LTS.
    Qed.


    Lemma SRPC_net_no_lock_tau_preserve [N0 N1 n0 n1 n a] :
      SRPC_net N0 ->
      ~ net_lock_on N0 n0 n1 ->
      (N0 =(NTau n a)=> N1) ->
      ~ net_lock_on N1 n0 n1.

    Proof.
      intros.

      remember (NTau n a) as na.
      induction H1 using (net_ind_of n0); hsimpl in *; doubt.
      - enough (forall L, ~ pq_lock L (NetMod.get n N1)) by (unfold net_lock_on, net_lock in *; eattac); intros.
        eauto using SRPC_tau_no_lock_r with LTS.
      - unfold net_lock_on, net_lock in *.
        now rewrite `(NetMod.get n0 N0 = _) in *.
    Qed.


    Lemma SRPC_sane_send_invariant [srpc S0 S1 nc v] :
      SRPC_sane srpc S0 ->
      (S0 =(send nc v)=> S1) ->
      SRPC_sane srpc S1.

    Proof.
      intros.
      destruct S0 as [I0 P0 O0]; compat_hsimpl in *.
      destruct nc as [c t].
      consider (SRPC_sane _ _).
      constructor; ltac1:(autounfold with SRPC in * ); simpl; intros; try (solve [simpl in *; eauto]).
      - clear - H_Q_out_last.
        intros ?.
        apply `(~ In (s, Q, v0) (removelast (pq_O (pq I0 P0 ((c, &t, v) :: O1))))).
        clear - H.
        induction O1 using rev_ind; eauto.
        simpl; rewrite removelast_app in *; eattac.
        rewrite app_nil_r in *.
        destruct O1; attac.
      - simpl in *.
        smash_eq c c0.
        + destruct t.
          * assert ((c, R) <> (c, Q)) by attac.
            enough (~ In (c, R, v') ((c, Q, v) :: O')) by eattac.
            eapply H_R_out_uniq; eattac.
          * enough (~ In (c, R, v') O1) by eattac.
            eapply H_R_out_uniq; eattac.
        + assert ((c0, R) <> (c, &t)) by attac.
          enough (~ In (c0, R, v') ((c, &t, v) :: O')) by eattac.
          eapply H_R_out_uniq; eattac.
      - simpl in *.
        assert (~ ((c, &t, v) = (s, Q, v') \/ In (s, Q, v') O1)) by eauto.
        consider (~ ((c, &t, v) = (s, Q, v')) /\ (~ In (s, Q, v') O1)) by eattac.
      - simpl in *.
        consider (exists v0, (c, &t, v) = (s, Q, v0) \/ In (s, Q, v0) O1) by eattac.
        destruct `(_ \/ _); eattac.
        destruct O1; doubt.
      - eattac.
      - simpl in *.
        consider ( ~ ((c, &t, v) = (c0, R, v0) \/ In (c0, R, v0) O1)).
    Qed.


    Lemma SRPC_sane_net_send_R_sender_no_lock [N0 N1 n0 n1 n v] :
      SRPC_sane_net N0 ->
      (N0 =(NComm n0 n1 R v)=> N1) ->
      ~ net_lock_on N1 n0 n.

    Proof.
      intros.
      remember (NComm n0 n1 R v) as na.
      induction `(N0 =(na)=> N1) using (net_ind_of n0); hsimpl in *; doubt.
      - enough (forall L, ~ pq_lock L (NetMod.get n1 N1)) by (unfold net_lock_on, net_lock in *; eattac); intros.
        enough (~ pq_lock L S0) by eauto using pq_recv_no_new_lock.
        consider (exists srpc, SRPC_sane srpc (NetMod.get n1 N0)) by eauto with LTS.
        eauto using SRPC_sane_send_R_no_lock_r with LTS.
      - enough (forall L, ~ pq_lock L (NetMod.get n0 N1)) by (unfold net_lock_on, net_lock in *; eattac); intros.
        consider (exists srpc, SRPC_sane srpc (NetMod.get n0 N0)) by eauto with LTS.
        eauto using SRPC_sane_send_R_no_lock_r with LTS.
    Qed.


    Lemma net_sane_send_R_lock_l [N0 N1 n0 n1 v] :
      net_sane N0 ->
      (N0 =(NComm n1 n0 R v)=> N1) ->
      net_lock_on N0 n0 n1.

    Proof.
      intros.
      enough (pq_client n0 (NetMod.get n1 N0)) by attac.
      consider (_ =(_)=> _); hsimpl in *.
      destruct (NetMod.get n1 N0) as [I0 P0 O0] eqn:?.
      compat_hsimpl in *.
      eattac.
    Qed.


    Lemma net_sane_send_R_receiver_no_lock [N0 N1 n0 n1 n v] :
      net_sane N0 ->
      (N0 =(NComm n1 n0 R v)=> N1) ->
      ~ net_lock_on N1 n0 n.

    Proof.
      intros.

      assert (net_lock_on N0 n0 n1) by eauto using net_sane_send_R_lock_l.

      smash_eq n1 n.
      - eauto using net_lock_on_reply_unlock with LTS.
      - intros ?.
        absurd (n1 = n); eauto using SRPC_net_no_relock with LTS.
    Qed.


    Lemma net_sane_send_R_no_unlock [N0 N1 n0 n1 m0 m1 v] :
      net_sane N0 ->
      ~ net_lock_on N0 m0 m1 ->
      (N0 =(NComm n1 n0 R v)=> N1) ->
      ~ net_lock_on N1 m0 m1.

    Proof.
      intros.

      smash_eq m0 n0.
      1: { eauto using net_sane_send_R_receiver_no_lock. }

      smash_eq m0 n1.
      1: { eauto using SRPC_sane_net_send_R_sender_no_lock with LTS. }

      remember (NComm n1 n0 R v) as na.
      induction `(N0 =(_)=> _) using (net_ind_of m0); hsimpl in *; doubt.

      unfold net_lock_on, net_lock in *.
      now rewrite `(NetMod.get m0 N0 = _) in *.
    Qed.


    Theorem net_sane_no_self_reply [N0 N1 : PNet] [n0 n1 v] :
      net_sane N0 ->
      (N0 =(NComm n0 n1 R v)=> N1) ->
      n0 <> n1.

    Proof.
      intros.
      intros ?; subst.
      rename n1 into n.

      enough (net_lock_on N0 n n) by bullshit (n <> n) by eauto using net_lock_on_no_send.

      enough (pq_client n (NetMod.get n N0)) by attac.

      consider (_ =(NComm n n R v)=> _); compat_hsimpl in *; attac.
    Qed.


    (* This is to allow the condition from LocksStatic be used in Immediate hints. *)
    Lemma net_sane_AnySRPC' (N : PNet) : net_sane N -> forall n, AnySRPC_pq (NetMod.get n N).
    Proof. intros. kill H. specialize (H_Sane_SRPC n) as [? H]. kill H. attac. Qed.
    #[export] Hint Extern 0 (forall n, AnySRPC_pq (NetMod.get n _)) => simple apply net_sane_AnySRPC'; eassumption : LTS.


    (* Ltac2 rec solve_mut_exclusive (full : bool) := *)
    (*   lazy_match! goal with *)
    (*   | [|- mut_exclusive _ []] => constructor *)
    (*   | [|- mut_exclusive _ (_::_)] => *)
    (*       constructor > *)
    (*         [ let h := Fresh.in_goal @H in *)
    (*           intros $h; *)
    (*           simpl app; *)
    (*           if full then solve_mut_exclusive full else () *)
    (*         | solve_mut_exclusive full *)
    (*         ] *)
    (*   | [|- Forall _ []] => constructor *)
    (*   | [|- Forall not (_::_)] => *)
    (*       constructor > *)
    (*         [ let h := Fresh.in_goal @H in *)
    (*           intros $h *)
    (*         | solve_mut_exclusive full *)
    (*         ] *)
    (*   end. *)


    Lemma proc_client_inv [P c0 c1] :
      proc_client c0 P ->
      proc_client c1 P ->
      c0 = c1.

    Proof.
      intros PC0 PC1.
      kill PC0.
      kill PC1.
      eapply (SRPC_inv H) in H0.
      kill H0.
    Qed.

    #[export] Hint Immediate proc_client_inv : LTS.


    (* Ltac2 rec strip_exists h := *)
    (*   lazy_match! (Constr.type (hyp h)) with *)
    (*   | ex ?body => *)
    (*       match (Constr.Unsafe.kind body) with *)
    (*       | Constr.Unsafe.Lambda arg val => *)
    (*           let hh := hyp h in *)
    (*           let arg_n := match Constr.Binder.name arg with *)
    (*                        | None => Fresh.in_goal @x *)
    (*                        | Some n => Fresh.in_goal n *)
    (*                        end in *)
    (*           destruct $hh as [$arg_n $h]; *)
    (*           strip_exists h *)
    (*       | _ => Control.throw Init.Assertion_failure *)
    (*       end *)
    (*   | ?t => *)
    (*       t *)
    (*   end. *)


    Lemma trans_invariant_net_sane_tau__Q_in [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      net_sane N0 ->
      SRPC_sane_Q_in (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, SRPC_sane srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      destruct S as [I1 P1 O1]; compat_hsimpl in *.
      consider (_ =(Tau)=> _); destruct `(NChan) as [? [|]]; compat_hsimpl in *; simpl in *; doubt.
      - smash_eq n0 c; attac.
        consider (exists I1', Deq (c, Q) v I0 I1' /\ Deq (n0, Q) v0 I1' I') by (eauto using Deq_Deq_swap with LTS).
        bullshit.

      - consider (exists I1', Deq (c, Q) v I0 I1' /\ Deq (n0, R) v0 I1' I') by (eauto using Deq_Deq_swap with LTS).
        bullshit.
    Qed.

    Lemma trans_invariant_net_sane_tau__R_in [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      net_sane N0 ->
      SRPC_sane_R_in (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, SRPC_sane srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      destruct S as [I1 P1 O1]; compat_hsimpl in *.
      consider (_ =(Tau)=> _); destruct `(NChan) as [? [|]]; compat_hsimpl in *; simpl in *; doubt.
      - consider (exists I1', Deq (s, R) v I0 I1' /\ Deq (n0, Q) v0 I1' I') by (eauto using Deq_Deq_swap with LTS).
        bullshit.

      - consider (exists c, SRPC (Work c) (PTau P1) /\ SRPC (Work c) P1)
          by (eapply SRPC_tau; eattac; consider (SRPC_sane _ _); eattac).
        assert (List.In (s', R, v') I1) by (eapply Deq_neq_In; eattac).
        consider (exists c0, srpc0 = Lock c0 s') by eattac.
        assert (SRPC (Lock c0 s') (PTau P1)) by (consider (SRPC_sane _ _); eattac).
        bullshit (~ Work c = Lock c0 s').
    Qed.


    Theorem net_sane_reply_lock [N0 N1 : PNet] [n0 n1 v] :
      net_sane N0 ->
      (N0 =(NComm n0 n1 R v)=> N1) ->
      net_lock_on N0 n1 n0.

    Proof.
      intros Hs0 T.

      assert (n0 <> n1) as HNEq by (eauto using net_sane_no_self_reply with LTS).

      kill Hs0.

      kill T.
      apply H_lock_complete.
      compat_hsimpl in *.
      rewrite `(NetMod.get n0 N0 = _).
      attac.
    Qed.


    Theorem net_sane_send_Q_new_lock [N0 N1 : PNet] [n0 n1 v] :
      net_sane N0 ->
      (N0 =(NComm n0 n1 Q v)=> N1) ->
      net_lock_on N1 n0 n1.

    Proof.
      intros Hs0 T.
      consider (_ =(_)=> _).

      consider (NetMod.get n0 N0 =(send (n1, Q) v)=> NetMod.get n0 N0') by eattac.
      consider (exists srpc, SRPC_sane srpc (NetMod.get n0 N0)) by eattac.

      enough (pq_lock [n1] (NetMod.get n0 N1)) by eattac.
      enough (pq_lock [n1] (NetMod.get n0 N0')).
      - smash_eq n0 n1.
        consider (N0' ~(n0 @ _)~> _).
        2: { replace (NetMod.get n0 N0') with (NetMod.get n0 N1); attac. }

        compat_hsimpl in *.
        hsimpl in *.

        consider (pq_lock _ _).
        attac.
        assert (In (n, R, v) &I \/ In (n, R, v) [(n, Q, v0)]) as [|] by eattac.
        all: bullshit.

      - assert (NetMod.get n0 N0 =(send (n1, Q) v)=> NetMod.get n0 N0')
          by eattac.
        eauto using SRPC_sane_send_Q_lock.
    Qed.


    Lemma trans_invariant_net_sane_tau__R_in_lock [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      net_sane N0 ->
      SRPC_sane_R_in_lock (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, SRPC_sane srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (List.In (s, R, v) I0) by (consider (_ =(Tau)=> _); eapply Deq_neq_In; eattac).
      consider (exists c, srpc0 = Lock c s) by eauto using SRPC_sane_R_in_lock_inv.
      exists c.
      assert (SRPC (Lock c s) P0) by (consider (SRPC_sane _ _); eattac).
      destruct S as [I1 P1 O1].
      enough (SRPC (Lock c s) P1) by attac.
      consider (_ =(Tau)=> _); hsimpl in *; doubt.
      destruct n0 as [? [|]]; doubt.
    Qed.


    Lemma trans_invariant_net_sane_tau__Q_out_lock [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      net_sane N0 ->
      SRPC_sane_Q_out_lock (NetMod.get n N1).
    Proof.
      attac.
      consider (exists srpc0, SRPC_sane srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (SRPC_sane _ _); eattac).
      destruct S as [I1 P1 O1]; compat_hsimpl in *; simpl in *.
      consider (_ =(Tau)=> _); destruct `(NChan) as [? [|]] eqn:?; subst; doubt.
      - consider (exists c, srpc0 = Lock c s) by eattac.
        exists c; consider (SRPC_sane _ _); attac.
      - assert (exists c, srpc0 = Lock c s) by eattac.
        assert (exists c', srpc0 = Lock c' n1) by eattac.
        hsimpl in *.
        bullshit.
      - enough (n1 = s) by eattac.
        assert (List.In (s, Q, v) O0 \/ List.In (s, Q, v) [(n1, Q, v0)]) as [|] by (hsimpl in * |-; eattac).
        2: { eattac. }

        assert (exists c, SRPC (Lock c s) P0) by (consider (SRPC_sane _ _); eattac).
        assert (exists c, SRPC (Work c) P0) by eattac.
        attac.

      - assert (exists c, SRPC (Lock c s) P0).
        {
          assert (List.In (s, Q, v) O0 \/ List.In (s, Q, v) [(n1, R, v0)]) as [|] by (hsimpl in * |-; eattac).
          2: { eattac. }
          consider (exists c, srpc0 = Lock c s) by eattac.
          consider (SRPC_sane _ _); eattac.
        }
        consider (exists c, SRPC (Work c) P0) by attac.

        hsimpl in *.
        bullshit.

      - assert (exists c, SRPC (Lock c n0) P0).
        {
          consider (exists c, srpc0 = Lock c n0) by eattac.
          consider (SRPC_sane _ _); eattac.
        }
        consider (exists c, SRPC (Work c) P0) by attac.
        hsimpl in *; bullshit.
    Qed.


    Lemma trans_invariant_net_sane_tau__Q_out_last [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      net_sane N0 ->
      SRPC_sane_Q_out_last (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, SRPC_sane srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (SRPC_sane _ _); eattac).
      destruct S as [I1 P1 O1]; compat_hsimpl in *; simpl in *.
      consider (_ =(Tau)=> _); destruct `(NChan) as [? [|]] eqn:?; subst; doubt.
      - assert (List.In (s, Q, v) O0)
          by (hsimpl in *; rewrite removelast_app in * by attac; simpl in *; rewrite app_nil_r in *; attac).  (* TODO WTF *)
        assert (exists c, SRPC (Lock c s) P0) by (consider (SRPC_sane _ _); eattac).
        assert (exists c, SRPC (Work c) P0) by (eattac).
        hsimpl in *; bullshit.

      - assert (List.In (s, Q, v) O0)
          by (hsimpl in *; rewrite removelast_app in * by attac; simpl in *; rewrite app_nil_r in *; attac).  (* TODO WTF *)
        assert (exists c, SRPC (Lock c s) P0) by (consider (SRPC_sane _ _); eattac).
        assert (exists c, SRPC (Work c) P0) by (eattac).
        hsimpl in *; bullshit.
    Qed.

    Lemma trans_invariant_net_sane_tau__R_out_uniq [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      net_sane N0 ->
      SRPC_sane_R_out_uniq (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, SRPC_sane srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (SRPC_sane _ _); eattac).
      destruct S as [I1 P1 O1]; compat_hsimpl in *; simpl in *.
      consider (_ =(Tau)=> _); destruct `(NChan) as [? [|]] eqn:?; subst; doubt.
      - consider (exists O0', Deq (c, R) v O0 O0' /\ O' = O0' ++ [(n1, Q, v0)]) by (eapply Deq_app_or_l; eattac).
        enough (List.In (c, R, v') O0') by eattac.
        assert (List.In (c, R, v') O0' \/ List.In (c, R, v') [(n1, Q, v0)]) as [|] by eattac; attac.
      - smash_eq c n1.
        + assert (proc_client c P0) by eattac.
          enough (List.In (c, R, v') O0) by eattac.
          hsimpl in *.
          assert (forall a b : (NChan * Val), {a = b} + {a <> b}) as Hmeh by (ltac1:(decide equality); eauto using NChan_eq_dec, Val_eq_dec).
          destruct (in_dec Hmeh (c, R, v') O0); auto.
          consider (exists O0', Deq (c, R) v [(c, R, v0)] O0' /\ O' = O0 ++ O0') by (eapply Deq_app_or_r; eattac).
          consider (Deq _ _ [_] _).
          rewrite app_nil_r in *. (* TODO WTF *)
          attac.

        + consider (exists O0', Deq (c, R) v O0 O0' /\ O' = O0' ++ [(n1, R, v0)]) by (eapply Deq_app_or_l; eattac).
          enough (List.In (c, R, v') O0') by eattac.
          assert (List.In (c, R, v') O0' \/ List.In (c, R, v') [(n1, R, v0)]) as [|] by eattac; attac.
    Qed.

    Lemma trans_invariant_net_sane_tau__R_Q [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      net_sane N0 ->
      SRPC_sane_R_Q (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, SRPC_sane srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (SRPC_sane _ _); eattac).
      destruct S as [I1 P1 O1]; compat_hsimpl in *; simpl in *.
      consider (_ =(Tau)=> _); destruct `(NChan) as [? [|]] eqn:?; subst; doubt.
      - assert (exists c, SRPC (Lock c s) P0) by (consider (SRPC_sane _ _); eattac).
        assert (exists c', SRPC (Work c') P0) by eattac.
        hsimpl in *; bullshit.
      - assert (exists c, SRPC (Lock c s) P0) by (consider (SRPC_sane _ _); eattac).
        assert (exists c', SRPC (Work c') P0) by eattac.
        hsimpl in *; bullshit.
      - assert (exists c, SRPC (Lock c s) P0) by (consider (SRPC_sane _ _); eattac).
        assert (exists c', SRPC (Work c') P0) by eattac.
        hsimpl in *; bullshit.
    Qed.

    Lemma trans_invariant_net_sane_tau__Q_R [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      net_sane N0 ->
      SRPC_sane_Q_R (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, SRPC_sane srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (SRPC_sane _ _); eattac).
      destruct S as [I1 P1 O1]; compat_hsimpl in *; simpl in *.
      consider (_ =(Tau)=> _); destruct `(NChan) as [? [|]] eqn:?; subst; doubt.
      - assert (exists c, SRPC (Lock c s) P0) by (consider (SRPC_sane _ _); eattac).
        assert (exists c', SRPC (Work c') P0) by eattac.
        hsimpl in *; bullshit.
      - assert (exists c, SRPC (Lock c s) P0) by (consider (SRPC_sane _ _); eattac).
        assert (exists c', SRPC (Work c') P0) by eattac.
        hsimpl in *; bullshit.
      - assert (exists c, SRPC (Lock c s) P0) by (consider (SRPC_sane _ _); eattac).
        assert (exists c', SRPC (Work c') P0) by eattac.
        hsimpl in *; bullshit.
    Qed.

    Lemma trans_invariant_net_sane_tau__lock_Q [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      net_sane N0 ->
      SRPC_sane_lock_Q (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, SRPC_sane srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (SRPC_sane _ _); eattac).
      destruct S as [I1 P1 O1']; compat_hsimpl in *; simpl in *.
      destruct O1' as [|[[? ?] ?] O1]; doubt.
      consider (_ =(Tau)=> _); destruct `(NChan) as [? [|]] eqn:?; subst; doubt.
      - consider (exists c', SRPC (Work c') P1) by eattac.
        bullshit (Lock c s = Work c').
      - consider (exists c', SRPC (Work c') P1) by eattac.
        bullshit (Lock c s = Work c').
      - consider (exists c', SRPC (Lock c' n2) P1) by eattac.
        consider (Lock c s = Lock c' n2) by eattac.
        hsimpl in *.
        destruct O0; doubt; hsimpl in *; eattac.
      - assert (SRPC Free P1) by eattac.
        bullshit (Lock c s = Free) by eattac.
      - consider (exists c', SRPC (Work c') P1) by eattac.
        bullshit (Lock c s = Work c').
      - consider (exists c', SRPC (Work c') P1) by eattac.
        bullshit (Lock c s = Work c').
    Qed.

    Lemma trans_invariant_net_sane_tau__in_Q_no_client [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      net_sane N0 ->
      SRPC_sane_in_Q_no_client (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, SRPC_sane srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (SRPC_sane _ _); eattac).
      destruct S as [I1 P1 O1']; compat_hsimpl in *; simpl in *.
      consider (_ =(Tau)=> _); destruct `(NChan) as [? [|]] eqn:?; subst; consider (proc_client _ _); doubt.
      - assert (SRPC (Work n1) P1) by eattac.
        destruct `(SRPC_Handle_State _).
        + assert (SRPC (Work n1) P1) by eattac.
          consider (Work n1 = Work c) by attac.
          bullshit.
        + bullshit (Work n1 = Lock c s) by attac.
      - consider (exists c', SRPC (Lock c' n1) P0 /\ SRPC (Work c') P1) by eauto using SRPC_recv_R.
        destruct `(SRPC_Handle_State _).
        + assert (SRPC (Work c) P1) by eattac.
          consider (Work c' = Work c) by attac.
          enough (proc_client c P0); eattac.
        + bullshit (Work c' = Lock c s) by attac.
      - consider (exists c', SRPC (Work c') P0 /\ SRPC (Lock c' n1) P1) by eauto using SRPC_send_Q.
        destruct `(SRPC_Handle_State _).
        + bullshit (Work c = Lock c' n1) by attac.
        + consider (Lock c' n1 = Lock c s) by attac.
          enough (proc_client c P0); eattac.
      - consider (SRPC (Work n1) P0 /\ SRPC Free P1) by eattac.
        destruct `(SRPC_Handle_State _).
        + bullshit (Work c = Free) by attac.
        + bullshit (Lock c s = Free) by attac.
      - consider (exists c', SRPC (Work c') P0 /\ SRPC (Work c') P1) by eauto using SRPC_tau.
        destruct `(SRPC_Handle_State _).
        + consider (Work c' = Work c) by attac.
          attac.
        + bullshit (Work c' = Lock c s) by attac.
    Qed.

    Lemma trans_invariant_net_sane_tau__in_Q_no_out_R [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      net_sane N0 ->
      SRPC_sane_in_Q_no_out_R (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, SRPC_sane srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (SRPC_sane _ _); eattac).
      destruct S as [I1 P1 O1']; compat_hsimpl in *; simpl in *.
      consider (_ =(Tau)=> _); destruct `(NChan) as [? [|]] eqn:?; subst; doubt.
      - consider (exists c', SRPC (Work c') P0 /\ SRPC (Lock c' n1) P1) by eauto using SRPC_send_Q.
        assert (List.In (c, R, v') O0 \/ List.In (c, R, v') [(n1, Q, v0)]) as [|]; (hsimpl in *|-; eattac).
      - consider (SRPC (Work n1) P0 /\ SRPC Free P1) by eauto using SRPC_send_R.
        assert (List.In (c, R, v') O0 \/ List.In (c, R, v') [(n1, R, v0)]) as [|]; (hsimpl in *|-; eattac).
      - consider (exists c', SRPC (Work c') P0 /\ SRPC (Work c') P1) by eauto using SRPC_tau.
        eattac.
    Qed.

    Lemma trans_invariant_net_sane_tau__client_no_out_R [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      net_sane N0 ->
      SRPC_sane_client_no_out_R (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, SRPC_sane srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (SRPC_sane _ _); eattac).
      destruct S as [I1 P1 O1']; compat_hsimpl in *; simpl in *.
      consider (_ =(Tau)=> _); destruct `(NChan) as [? [|]] eqn:?; subst; consider (proc_client _ _); doubt.
        - assert (SRPC (Work n1) P1) by eattac.
        destruct `(SRPC_Handle_State _).
        + assert (SRPC (Work n1) P1) by eattac.
          consider (Work n1 = Work c) by attac.
          bullshit.
        + bullshit (Work n1 = Lock c s) by attac.
      - consider (exists c', SRPC (Lock c' n1) P0 /\ SRPC (Work c') P1) by eauto using SRPC_recv_R.
        destruct `(SRPC_Handle_State _).
        + assert (SRPC (Work c) P1) by eattac.
          consider (Work c' = Work c) by attac.
          enough (proc_client c P0); eattac.
        + bullshit (Work c' = Lock c s) by attac.
      - consider (exists c', SRPC (Work c') P0 /\ SRPC (Lock c' n1) P1) by eauto using SRPC_send_Q.
        destruct `(SRPC_Handle_State _).
        + bullshit (Work c = Lock c' n1) by attac.
        + consider (Lock c' n1 = Lock c s) by attac.
          assert (List.In (c, R, v) O0 \/ List.In (c, R, v) [(s, Q, v0)]) as [|]; (hsimpl in *|-; eattac).
      - consider (SRPC (Work n1) P0 /\ SRPC Free P1) by eattac.
        destruct `(SRPC_Handle_State _).
        + bullshit (Work c = Free) by attac.
        + bullshit (Lock c s = Free) by attac.
      - consider (exists c', SRPC (Work c') P0 /\ SRPC (Work c') P1) by eauto using SRPC_tau.
        destruct `(SRPC_Handle_State _).
        + consider (Work c' = Work c) by attac.
          attac.
        + bullshit (Work c' = Lock c s) by attac.
    Qed.


    Lemma trans_invariant_net_sane_tau__SRPC_sane [n N0 N1] :
      N0 ~(n @ Tau)~> N1 ->
      net_sane N0 ->
      SRPC_sane_net N1.

    Proof.
      intros.
      intros n'.

      smash_eq n n'.
      2: {
        replace (NetMod.get n' N1) with (NetMod.get n' N0) by eauto using NV_stay with LTS.
        eattac.
      }

      consider (exists srpc0 : SRPC_State, SRPC_sane srpc0 (NetMod.get n N0)) by attac.
      consider (exists srpc1, SRPC_pq srpc1 (NetMod.get n N1))
        by (hsimpl in *; assert (AnySRPC_pq (NetMod.get n N0)) by eattac; enough (AnySRPC_pq &S); eattac).

      exists srpc1.
      constructor;

      eauto using
        trans_invariant_net_sane_tau__Q_in,
        trans_invariant_net_sane_tau__R_in,
        trans_invariant_net_sane_tau__R_in_lock,
        trans_invariant_net_sane_tau__Q_out_lock,
        trans_invariant_net_sane_tau__Q_out_last,
        trans_invariant_net_sane_tau__R_out_uniq,
        trans_invariant_net_sane_tau__R_Q,
        trans_invariant_net_sane_tau__Q_R,
        trans_invariant_net_sane_tau__lock_Q,
        trans_invariant_net_sane_tau__in_Q_no_client,
        trans_invariant_net_sane_tau__in_Q_no_out_R,
        trans_invariant_net_sane_tau__client_no_out_R.
    Qed.


    Lemma net_sane_handler_uniq [N n0 n1 n1'] :
      net_sane N ->
      pq_client n0 (NetMod.get n1 N) ->
      pq_client n0 (NetMod.get n1' N) ->
      n1' = n1.

    Proof.
      intros.
      consider (net_lock_on N n0 n1 /\ net_lock_on N n0 n1') by attac.
      enough (lock_uniq_type N) by attac.
      eauto using SRPC_net_lock_uniq with LTS.
    Qed.


    Lemma pq_client_invariant_tau [c] :
      trans_invariant (fun S => AnySRPC_pq S /\ pq_client c S) (eq Tau).

    Proof.
      unfold trans_invariant.
      intros * T Hc Eq.
      subst.
      destruct Hc as [Hsrpc Hc].
      split.
      1: eauto with LTS.

      consider (pq_client c N0); consider (_ =(Tau)=> _);
        try (solve [eattac]);
        try (destruct `(NChan) as [n [|]]); doubt.

      - consider (SRPC Free P /\ SRPC (Work n) P1) by eauto using SRPC_recv_Q.
        smash_eq c n; eauto with LTS.
        enough (exists v', List.In (c, Q, v') I1) by eattac.
        exists v.
        unshelve eapply (Deq_neq_In _ `(Deq _ _ &I I1)); eattac.

      - enough (exists v', List.In (c, Q, v') I1) by eattac.
        exists v.
        unshelve eapply (Deq_neq_In _ `(Deq _ _ &I I1)); eattac.

      - consider (SRPC Free P /\ SRPC (Work n) P1) by eauto using SRPC_recv_Q.
        smash_eq c n; attac.

        consider (proc_client c (PRecv h)).
        bullshit (Free = Busy `(_)).

      - consider (exists c', SRPC (Lock c' n) P /\ SRPC (Work c') P1) by eauto using SRPC_recv_R.
        smash_eq c c'; attac.

        consider (proc_client c (PRecv &handle)).
        bullshit.

      - consider (exists c', SRPC (Work c') P /\ SRPC (Lock c' n) P1) by eauto using SRPC_send_Q.
        consider (proc_client c P) by attac.
        consider (Work c' = Busy `(_)) by attac.
        attac.

      - consider (SRPC (Work n) P /\ SRPC Free P1) by eauto using SRPC_send_R.
        enough (c = n) by attac.
        enough (proc_client n P) by attac.
        attac.

      - consider (exists c', SRPC (Work c') P /\ SRPC (Work c') P1) by eauto using SRPC_tau.
        enough (c = c') by attac.
        enough (proc_client c' P) by attac.
        attac.
    Qed.


    Lemma SRPC_net_lock_on_tau_derive [N0 N1 n0 n1 n a] :
      SRPC_net N0 ->
      net_lock_on N1 n0 n1 ->
      (N0 =(NTau n a)=> N1) ->
      net_lock_on N0 n0 n1.

    Proof.
      intros.
      smash_eq n0 n.
      - bullshit (~ net_lock_on N1 n0 n1) by eauto using SRPC_net_tau_no_lock with LTS.
      - unfold net_lock_on, net_lock in *.
        replace (NetMod.get n0 N0) with (NetMod.get n0 N1); eattac.
    Qed.


    Lemma trans_invariant_net_sane_tau__locks_sound [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      net_sane N0 ->
      locks_sound N1.

    Proof.
      repeat (intros ?).

      enough (net_lock_on N0 n0 n1).
      {
        assert (pq_client n0 (NetMod.get n1 N0)) by attac.
        smash_eq n n1.
        + eapply pq_client_invariant_tau; eattac.
        + now replace (NetMod.get n1 N1) with (NetMod.get n1 N0) by (eauto using NV_stay with LTS).
      }

      enough (N0 =(NTau n Tau)=> N1) by eauto using SRPC_net_lock_on_tau_derive with LTS.
      eattac.
    Qed.


    Lemma trans_invariant_net_sane_tau__locks_complete [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      net_sane N0 ->
      locks_complete N1.

    Proof.
      repeat (intros ?).

      assert (N0 =(NTau n Tau)=> N1) by attac.
      enough (net_lock_on N0 n0 n1) by eauto using net_lock_on_tau_preserve.
      enough (pq_client n0 (NetMod.get n1 N0)) by attac.

      smash_eq n n1.
      2: { now replace (NetMod.get n1 N1) with (NetMod.get n1 N0) by (eauto using NV_stay with LTS). }

      assert (AnySRPC_pq (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?.
      destruct (NetMod.get n N1) as [I1 P1 O1] eqn:?.

      hsimpl in *. hsimpl in *.
      rewrite `(NetMod.get n N0 = _) in *.

      consider (_ =(Tau)=> _);
        try (destruct `(NChan) as [n1 [|]]).

      - consider (SRPC Free P0 /\ SRPC (Work n1) P1) by eauto using SRPC_recv_Q.
        smash_eq n0 n1; eauto with LTS.
        consider (pq_client n0 _).
        + enough (List.In (n0, Q, v0) I0) by eattac.
          unshelve eapply (Deq_neq_In _ `(Deq _ _ I0 I1)); eattac.
        + consider (proc_client n0 P1); eattac.
        + attac.

      - consider (exists c', SRPC (Lock c' n1) P0 /\ SRPC (Work c') P1) by eauto using SRPC_recv_R.
        smash_eq n0 c'; eauto with LTS.
        consider (pq_client n0 _).
        + enough (List.In (n0, Q, v0) I0) by eattac.
          unshelve eapply (Deq_neq_In _ `(Deq _ _ I0 I1)); eattac.
        + consider (proc_client n0 P1); eattac.
        + attac.

      - consider (exists c', SRPC (Work c') P0 /\ SRPC (Lock c' n1) P1) by eauto using SRPC_send_Q.
        smash_eq n0 c'; eauto with LTS.
        consider (pq_client n0 _).
        + attac.
        + consider (proc_client n0 P1); eattac.
        + assert (List.In (n0, R, v0) O0 \/ List.In (n0, R, v0) [(n1, Q, v)]) as [|] by (hsimpl in * |-; eattac); eattac.

      - consider (SRPC (Work n1) P0 /\ SRPC Free P1) by eauto using SRPC_send_R.
        smash_eq n0 n1; eauto with LTS.
        consider (pq_client n0 _).
        + attac.
        + consider (proc_client n0 P1); eattac.
          bullshit (Free = Busy `(_)) by eattac.
        + assert (List.In (n0, R, v0) O0 \/ List.In (n0, R, v0) [(n1, R, v)]) as [|] by (hsimpl in * |-; eattac); eattac.

      - consider (exists c', SRPC (Work c') P0 /\ SRPC (Work c') P1) by eauto using SRPC_tau.
        smash_eq n0 c'; eauto with LTS.
        consider (pq_client n0 _).
        + attac.
        + consider (proc_client n0 P1); eattac.
        + attac.

    Qed.


    Lemma trans_invariant_net_sane_tau [n a N0 N1] :
      (N0 =(NTau n a)=> N1) ->
      net_sane N0 ->
      net_sane N1.

    Proof.
      intros.
      consider (_ =(_)=> _).

      constructor.
      - eauto using trans_invariant_net_sane_tau__SRPC_sane with LTS.
      - eauto using trans_invariant_net_sane_tau__locks_sound with LTS.
      - eauto using trans_invariant_net_sane_tau__locks_complete with LTS.
    Qed.


    (* TODO MOVE UP *)
    Lemma SRPC_sane_R_in_out_nil [srpc : SRPC_State] [s v S] :
      SRPC_sane srpc S ->
      In (s, R, v) (pq_I S) ->
      pq_O S = [].
    Proof.
      intros.
      destruct S as [I0 P0 O0].
      simpl in *.
      consider (exists c, srpc = Lock c s) by attac.
      destruct O0; auto.
      assert (p::O0 <> []) by attac.
      remember (p::O0) as O1; clear HeqO1.
      consider (exists v', In (s, Q, v') (pq_O (pq I0 P0 O1))) by attac.
      bullshit (In (s, R, v) (pq_I (pq I0 P0 (O1)))) by eattac.
    Qed.


    Lemma trans_invariant_net_sane__net_sane_comm__sender_Q [n0 n1 v] [N0 N1 : PNet] :
      n0 <> n1 ->
      (N0 =(NComm n0 n1 Q v)=> N1) ->
      net_sane N0 ->
      exists srpc, SRPC_sane srpc (NetMod.get n0 N1).

    Proof.
      intros.
      assert (net_lock_on N1 n0 n1) by eauto using net_sane_send_Q_new_lock.
      consider (exists n', SRPC_pq (Lock n' n1) (NetMod.get n0 N1)).
      {
        assert (pq_lock [n1] (NetMod.get n0 N1)) by attac.
        eauto using lock_SRPC_Lock_pq with LTS.
      }

      exists (Lock n' n1).

      destruct (NetMod.get n0 N0) as [I0 P0 O0] eqn:?.
      consider (exists srpc0, SRPC_sane srpc0 (NetMod.get n0 N0)) by attac.

      consider (N0 =(_)=> _); compat_hsimpl in *; doubt; rewrite `(NetMod.get n0 _ = _) in *.
      constructor; ltac1:(autounfold with SRPC); intros; simpl in *.
      - auto.
      - attac.
      - attac.
      - hsimpl in *.
        bullshit (pq_O (pq I2 P2 ((n1, Q, v) :: O2)) = []) by eauto using SRPC_sane_R_in_out_nil.

      - enough (s = n1) by eattac.
        consider (exists c, srpc0 = Lock c s) by attac.
        hsimpl in *.
        assert (SRPC_pq (Lock c s) (pq I2 P2 ((n1, Q, v)::O2))) by attac.
        consider (Lock n' n1 = Lock c s) by attac.

      - hsimpl in *.
        assert (~ In (s, Q, v0) (removelast (pq_O (pq I2 P2 ((n1, Q, v) :: O2))))) by eauto using SRPC_sane_Q_out_last_inv.
        destruct O2; attac.
      - attac.
      - compat_hsimpl in *; attac.
      - attac.
      - hsimpl in *.
        enough (O2 = []) by bullshit.
        eapply SRPC_sane__Q_out_last_nil_inv with (O0:=[]);
          eauto; simpl in *; eauto.
      - attac.
      - attac.
      - attac.
    Qed.

    (* TODO MOVE UP *)
    Lemma SRPC_sane_net_sane : forall N0, SRPC_sane_net N0 -> SRPC_net N0.
    Proof. repeat (intros ?). specialize (`(SRPC_sane_net _) n). attac. Qed.

    #[export] Hint Resolve SRPC_sane_net_sane : LTS.


    Lemma net_sane_recv_R_SRPC [n0 n1 v] [N0 N1 : PNet] :
      net_sane N0 ->
      (N0 =(NComm n0 n1 R v)=> N1) ->
      exists n', SRPC_sane (Lock n' n0) (NetMod.get n1 N0).

    Proof.
      intros.
      consider (exists srpc, SRPC_sane srpc (NetMod.get n1 N0)) by attac.
      assert (SRPC_pq srpc (NetMod.get n1 N0)) by attac.

      enough (exists n', srpc = Lock n' n0) by attac.
      enough (exists n', SRPC_pq (Lock n' n0) (NetMod.get n1 N0)) by attac.
      enough (pq_lock [n0] (NetMod.get n1 N0)) by eauto using lock_SRPC_Lock_pq with LTS.
      enough (net_lock N0 [n0] n1) by attac.
      enough (net_lock_on N0 n1 n0) by eauto using lock_singleton with LTS.
      eauto using net_sane_reply_lock.
    Qed.


    Lemma trans_invariant_net_sane__net_sane_comm__sender_R [n0 n1 v] [N0 N1 : PNet] :
      n0 <> n1 ->
      (N0 =(NComm n0 n1 R v)=> N1) ->
      net_sane N0 ->
      exists srpc, SRPC_sane srpc (NetMod.get n0 N1).

    Proof.
      intros.

      consider (exists srpc, SRPC_sane srpc (NetMod.get n0 N0)) by attac.
      exists srpc. (* The process did not change! *)

      assert (net_lock_on N0 n1 n0) by eauto using net_sane_send_R_lock_l.

      consider (exists n', SRPC_sane (Lock n' n0) (NetMod.get n1 N0))
        by eauto using net_sane_recv_R_SRPC.

      destruct (NetMod.get n0 N0) as [I00 P00 O00] eqn:?.
      destruct (NetMod.get n0 N1) as [I01 P01 O01] eqn:?.
      destruct (NetMod.get n1 N0) as [I10 P10 O10] eqn:?.
      destruct (NetMod.get n1 N1) as [I11 P11 O11] eqn:?.

      consider (_ =(_)=> _); compat_hsimpl in *.
      constructor; ltac1:(autounfold with SRPC); intros;
        repeat (rewrite `(NetMod.get _ _ = _) in * ); hsimpl in *.
      - consider (SRPC_sane srpc (pq _ P00 _)).
      - attac.
      - attac.
      - assert (In (s, R, v0) (pq_I (pq I00 P00 ((n1, R, v)::O01)))) by attac.
        consider (exists c', srpc = Lock c' s) by eauto using SRPC_sane_R_in_lock_inv.
        assert (SRPC_pq (Lock c' s) (pq I00 P00 ((n1, R, v) :: O01))) by eauto using SRPC_sane_SRPC_inv with LTS.
        attac.
      - consider (exists c', srpc = Lock c' s) by eauto using SRPC_sane_Q_out_lock_inv with datatypes LTS.
        assert (SRPC_pq (Lock c' s) (pq I00 P00 ((n1, R, v) :: O01))) by eauto using SRPC_sane_SRPC_inv with LTS.
        attac.
      - enough (~ In (s, Q, v0) (removelast ((n1, R, v)::O01))) by (destruct O01; eattac).
        eauto using SRPC_sane_Q_out_last_inv.
      - smash_eq n1 c.
        1: { bullshit (In (n1, R, v0) O01) by attac. }
        enough (~ In (c, R, v') ((n1, R, v)::O')) by eattac.
        enough (Deq (c, R) v0 (pq_O (pq I00 P00 ((n1, R, v)::O01))) ((n1, R, v)::O')) by attac.
        now enough (Deq (c, R) v0 (pq_O (pq I00 P00 O01)) O') by attac.
      - attac.
      - attac.
      - enough (exists v0, In (s, Q, v0) ((n1, R, v)::O01)) by (hsimpl in *; destruct `(_ \/ _); attac).
        assert (pq_O (pq I00 P00 ((n1, R, v)::O01)) <> []) by attac.
        enough (srpc = Lock c s) by (subst; eauto using SRPC_sane_lock_Q_inv).
        enough (SRPC_pq srpc (pq I00 P00 ((n1, R, v)::O01))) by attac.
        eauto using SRPC_sane_SRPC_inv with LTS.
      - attac.
      - attac.
      - attac.
    Qed.

    Lemma trans_invariant_net_sane__net_sane_comm__sender [n0 n1 t v] [N0 N1 : PNet] :
      n0 <> n1 ->
      (N0 =(NComm n0 n1 t v)=> N1) ->
      net_sane N0 ->
      exists srpc, SRPC_sane srpc (NetMod.get n0 N1).

    Proof.
      intros.
      destruct t;
        eauto using
          trans_invariant_net_sane__net_sane_comm__sender_Q
        , trans_invariant_net_sane__net_sane_comm__sender_R.

    Qed.


    Lemma trans_invariant_net_sane__net_sane_comm__receiver_Q [n0 n1 v] [N0 N1 : PNet] :
      n0 <> n1 ->
      (N0 =(NComm n0 n1 Q v)=> N1) ->
      net_sane N0 ->
      exists srpc, SRPC_sane srpc (NetMod.get n1 N1).

    Proof.
      intros.

      consider (exists srpc, SRPC_sane srpc (NetMod.get n1 N0)) by attac.
      exists srpc. (* The process did not change! *)

      assert (net_lock_on N1 n0 n1) by eauto using net_sane_send_Q_new_lock.
      assert (~ pq_client n0 (NetMod.get n1 N0)).
      {
        intros ?.
        absurd (net_lock_on N0 n0 n1).
        2: { attac. }
        bullshit (n0 <> n0) by eauto using net_lock_on_no_send.
      }

      destruct (NetMod.get n0 N0) as [I00 P00 O00] eqn:?.
      destruct (NetMod.get n0 N1) as [I01 P01 O01] eqn:?.
      destruct (NetMod.get n1 N0) as [I10 P10 O10] eqn:?.
      destruct (NetMod.get n1 N1) as [I11 P11 O11] eqn:?.

      consider (_ =(_)=> _);
      constructor; ltac1:(autounfold with SRPC); intros;
        repeat (rewrite `(NetMod.get _ _ = _) in * ); compat_hsimpl in * |-; hsimpl in *.
      - consider (SRPC_sane srpc _); attac.
      - assert (forall v, ~ In (n0, Q, v) I10) by attac.
        smash_eq n0 c.
        + simpl in *.
          consider (exists I'', Deq (n0, Q) v0 [(n0, Q, v)] I'' /\ I' = I10 ++ I'') by eauto using Deq_app_or_r.
          consider (Deq _ _ [_] I''); compat_hsimpl in *.
          attac.
        + simpl in *.
          assert (~ In (c, Q, v0) [(n0, Q, v)]) by attac.
          consider (exists I'', Deq (c, Q) v0 I10 I'' /\ I' = I'' ++ [(n0, Q, v)]) by eauto using Deq_app_or_l.
          assert (~ In (c, Q, v') I'') by attac.
          intros ?.
          assert (In (c, Q, v') I'' \/ In (c, Q, v') [(n0, Q, v)]) as [|] by attac; bullshit.
      - assert (~ In (s, R, v0) [(n0, Q, v)]) by attac.
        consider (exists I'', Deq (s, R) v0 I10 I'' /\ I' = I'' ++ [(n0, Q, v)]) by eauto using Deq_app_or_l.
        assert (~ In (s, R, v') I'') by attac.
        intros ?.
        assert (In (s', R, v') I'' \/ In (s', R, v') [(n0, Q, v)]) as [|] by attac; bullshit.
      - enough (exists c, SRPC_pq (Lock c s) (pq I10 P10 O10)) by attac.
        enough (exists c, srpc = Lock c s) by (hsimpl in * |-; eauto using SRPC_sane_SRPC_inv with LTS).
        enough (In (s, R, v0) (pq_I (pq I10 P10 O10))) by eauto using SRPC_sane_R_in_lock_inv.
        simpl in *.
        assert (In (s, R, v0) I10 \/ In (s, R, v0) [(n0, Q, v)]) as [|]; attac.
      - enough (exists c, SRPC_pq (Lock c s) (pq I10 P10 O10)) by attac.
        enough (exists c, srpc = Lock c s) by (hsimpl in * |-; eauto using SRPC_sane_SRPC_inv with LTS).
        enough (In (s, Q, v0) (pq_O (pq I10 P10 O10))) by eauto using SRPC_sane_Q_out_lock_inv.
        attac.

      - enough (~ In (s, Q, v0) (removelast ((n1, Q, v) :: O01))) by (destruct O01; attac).
        eauto with LTS.

      - attac.
      - enough (In (s, R, v0) (pq_I (pq I10 P10 O10))) by attac.
        enough (In (s, R, v0) I10) by attac.
        assert (In (s, R, v0) I10 \/ In (s, R, v0) [(n0, Q, v)]) as [|]; attac.

      - compat_hsimpl; attac.

      - assert (pq_O (pq I10 P10 O10) <> []) by attac.
        enough (srpc = Lock c s) by attac.
        assert (SRPC_pq srpc (pq I10 P10 O10)) by eauto using SRPC_sane_SRPC_inv.
        attac.

      - smash_eq n0 c.
        1: { attac. }
        assert (In (c, Q, v0) I10 \/ In (c, Q, v0) [(n0, Q, v)]) as [|]; attac.

      - smash_eq n0 c.
        1: { attac. }
        assert (In (c, Q, v0) I10 \/ In (c, Q, v0) [(n0, Q, v)]) as [|]; attac.

      - smash_eq n0 c; attac.
    Qed.


    Lemma trans_invariant_net_sane__net_sane_comm__receiver_R [n0 n1 v] [N0 N1 : PNet] :
      n0 <> n1 ->
      (N0 =(NComm n0 n1 R v)=> N1) ->
      net_sane N0 ->
      exists srpc, SRPC_sane srpc (NetMod.get n1 N1).

    Proof.
      intros.
      consider (exists srpc, SRPC_sane srpc (NetMod.get n1 N0)) by attac.
      exists srpc. (* The process did not change! *)

      assert (net_lock_on N0 n1 n0) by eauto using net_sane_reply_lock.
      consider (exists n', SRPC_sane (Lock n' n0) (NetMod.get n1 N0))
        by eauto using net_sane_recv_R_SRPC.

      destruct (NetMod.get n0 N0) as [I00 P00 O00] eqn:?.
      destruct (NetMod.get n0 N1) as [I01 P01 O01] eqn:?.
      destruct (NetMod.get n1 N0) as [I10 P10 O10] eqn:?.
      destruct (NetMod.get n1 N1) as [I11 P11 O11] eqn:?.

      consider (O10 = []) by attac.
      assert (forall s v, ~ In (s, R, v) I10).
      { (* TODO extract *)
        intros.
        unfold net_lock_on, net_lock in *.
        consider (pq_lock [n0] (pq I10 P10 [])) by attac 2.
        intros.
        smash_eq s n0.
        - rewrite `(NetMod.get n1 N0 = _) in *. attac.
        - intros ?.
          consider (exists c, Lock n' n0 = Lock c s) by attac.
      }

      consider (_ =(_)=> _); compat_hsimpl in *.
      constructor; ltac1:(autounfold with SRPC); intros;
        repeat (rewrite `(NetMod.get _ _ = _) in * ); hsimpl in *.
      - consider (SRPC_sane srpc (pq _ P10 _)).
      - assert (~ In (c, Q, v0) [(n0, R, v)]) by attac.
        consider (exists I'', Deq (c, Q) v0 I10 I'' /\ I' = I'' ++ [(n0, R, v)]) by eauto using Deq_app_or_l.
        intros ?.
        assert (In (c, Q, v') I'' \/ In (c, Q, v') [(n0, R, v)]) as [|]; attac.
      - consider (exists I'', Deq (s, R) v0 [(n0, R, v)] I'' /\ I' = I10 ++ I'') by eauto using Deq_app_or_r.
        consider (Deq (s, R) v0 [_] I''); doubt.
        now compat_hsimpl in *.

      - assert (In (s, R, v0) I10 \/ In (s, R, v0) [(n0, R, v)]) as [|]; attac.
        enough (exists c, SRPC_pq (Lock c s) (pq I10 P10 [])) by attac.
        eauto using SRPC_sane_SRPC_inv.
      - attac.
      - attac.
      - attac.
      - attac.
      - attac.
      - attac.
      - assert (In (c, Q, v0) I10 \/ In (c, Q, v0) [(n0, R, v)]) as [|]; attac.
      - assert (In (c, Q, v0) I10 \/ In (c, Q, v0) [(n0, R, v)]) as [|]; attac.
      - attac.
    Qed.

    Lemma trans_invariant_net_sane__net_sane_comm__receiver [n0 n1 t v] [N0 N1 : PNet] :
      n0 <> n1 ->
      (N0 =(NComm n0 n1 t v)=> N1) ->
      net_sane N0 ->
      exists srpc, SRPC_sane srpc (NetMod.get n1 N1).

    Proof.
      intros.
      destruct t;
        eauto using
          trans_invariant_net_sane__net_sane_comm__receiver_Q
        , trans_invariant_net_sane__net_sane_comm__receiver_R.
    Qed.


    Lemma trans_invariant_net_sane__net_sane_comm__self_Q [n0 v] [N0 N1 : PNet] :
      (N0 =(NComm n0 n0 Q v)=> N1) ->
      net_sane N0 ->
      exists srpc, SRPC_sane srpc (NetMod.get n0 N1).

    Proof.
      intros.

      consider (exists srpc, SRPC_sane srpc (NetMod.get n0 N0)) by attac.
      exists srpc. (* The process did not change! *)

      assert (net_lock_on N1 n0 n0) by eauto using net_sane_send_Q_new_lock.
      assert (~ pq_client n0 (NetMod.get n0 N0)).
      {
        intros ?.
        absurd (net_lock_on N0 n0 n0).
        2: { attac. }
        bullshit (n0 <> n0) by eauto using net_lock_on_no_send.
      }
      consider (exists n', SRPC_pq (Lock n' n0) (NetMod.get n0 N1)).
      {
        assert (pq_lock [n0] (NetMod.get n0 N1)) by attac.
        eauto using lock_SRPC_Lock_pq with LTS.
      }

      destruct (NetMod.get n0 N0) as [I0 P0 O0] eqn:?.
      destruct (NetMod.get n0 N1) as [I1 P1 O1] eqn:?.

      consider (N0 =(_)=> _); compat_hsimpl in *; doubt; rewrite `(NetMod.get n0 _ = _) in *.
      compat_hsimpl in *; rename I2 into I0.
      constructor; ltac1:(autounfold with SRPC); intros; simpl in *.
      - consider (SRPC_sane srpc (pq _ P1 _)).
      - smash_eq n0 c.
        + assert (forall v, ~ In (n0, Q, v) I0) by bullshit.
          consider (exists I1', Deq (n0, Q) v0 [(n0, Q, v)] I1' /\ I' = I0 ++ I1')
            by eauto using Deq_app_or_r with LTS.
          consider (Deq (n0, Q) v0 [(n0, Q, v)] I1'); doubt.
          compat_hsimpl in *; auto.
        + assert (~ In (c, Q, v0) [(n0, Q, v)]) by bullshit.
          consider (exists I1', Deq (c, Q) v0 I0 I1' /\ I' = I1' ++ [(n0, Q, v)])
            by eauto using Deq_app_or_l with LTS.
          assert (~ In (c, Q, v') I1') by eauto with LTS.
          intros ?.
          assert (In (c, Q, v') I1' \/ In (c, Q, v') [(n0, Q, v)]) as [|] by attac; bullshit.
    - assert (~ In (s, R, v0) [(n0, Q, v)]) by bullshit.
      consider (exists I1', Deq (s, R) v0 I0 I1' /\ I' = I1' ++ [(n0, Q, v)])
        by eauto using Deq_app_or_l with LTS.
      assert (~ In (s, R, v') I1') by eauto with LTS.

      intros ?.
      assert (In (s', R, v') I1' \/ In (s', R, v') [(n0, Q, v)]) as [|] by attac; bullshit.
    - assert (In (s, R, v0) I0 \/ In (s, R, v0) [(n0, Q, v)]) as [|] by attac; doubt.
      bullshit (pq_O (pq I0 P1 ((n0, Q, v) :: O1)) = []) by eauto using SRPC_sane_R_in_out_nil.

    - enough (s = n0) by eattac.
      consider (exists c, srpc = Lock c s) by attac.
      assert (SRPC_pq (Lock c s) (pq I0 P1 ((n0, Q, v)::O1))) by attac.
      consider (Lock n' n0 = Lock c s) by attac.
    - assert (~ In (s, Q, v0) (removelast (pq_O (pq I0 P1 ((n0, Q, v) :: O1))))) by eauto using SRPC_sane_Q_out_last_inv.
      destruct O1; attac.
    - attac.
    - bullshit (O1 = []) by (eapply SRPC_sane__Q_out_last_nil_inv with (O0:=[]); eauto; simpl in *; eauto).
    - assert (~ In (s, R, v') I0) by attac.
      intros ?.
      apply `(~ In _ _).
      assert (In (s, R, v') I0 \/ In (s, R, v') [(n0, Q, v)]) as [|]; attac.
    - bullshit (O1 = []) by (eapply SRPC_sane__Q_out_last_nil_inv with (O0:=[]); eauto; simpl in *; eauto).
    - assert (In (c, Q, v0) I0 \/ In (c, Q, v0) [(n0, Q, v)]) as [|] by attac; doubt.
      unfold net_lock_on, net_lock in *; hsimpl in *.
      bullshit.
    - assert (In (c, Q, v0) I0 \/ In (c, Q, v0) [(n0, Q, v)]) as [|] by attac; doubt.
      unfold net_lock_on, net_lock in *; hsimpl in *.
      bullshit.
    - unfold net_lock_on, net_lock in *; hsimpl in *.
      bullshit.
    Qed.


    Lemma trans_invariant_net_sane__net_sane_comm__self [n0 t v] [N0 N1 : PNet] :
      (N0 =(NComm n0 n0 t v)=> N1) ->
      net_sane N0 ->
      exists srpc, SRPC_sane srpc (NetMod.get n0 N1).

    Proof.
      intros.
      destruct t.
      - eauto using trans_invariant_net_sane__net_sane_comm__self_Q.
      - bullshit (n0 <> n0) by eauto using net_sane_no_self_reply.
    Qed.


    Lemma trans_invariant_net_sane_comm__SRPC_sane [n0 n1 t v] [N0 N1 : PNet] :
      (N0 =(NComm n0 n1 t v)=> N1) ->
      net_sane N0 ->
      SRPC_sane_net N1.

    Proof.
      repeat (intros ?).
      smash_eq_on n n0 n1; subst.
      - eauto using trans_invariant_net_sane__net_sane_comm__self.
      - eauto using trans_invariant_net_sane__net_sane_comm__sender.
      - eauto using trans_invariant_net_sane__net_sane_comm__receiver.
      - replace (NetMod.get n N1) with (NetMod.get n N0); attac.
        eapply (@act_particip_stay PQued PAct); attac.
    Qed.


    Lemma trans_invariant_net_sane_comm__locks_sound [n0 n1 t v] [N0 N1 : PNet] :
      (N0 =(NComm n0 n1 t v)=> N1) ->
      net_sane N0 ->
      locks_sound N1.

    Proof.
    Admitted.


    Lemma trans_invariant_net_sane_comm__locks_complete [n0 n1 t v] [N0 N1 : PNet] :
      (N0 =(NComm n0 n1 t v)=> N1) ->
      net_sane N0 ->
      locks_complete N1.

    Proof.
    Admitted.


    Hint Resolve trans_pqued | 0 : typeclass_instances.
    Lemma trans_invariant_net_sane_comm [n0 n1 t] [v] [N0 N1 : PNet] :
      (N0 =(NComm n0 n1 t v)=> N1) ->
      net_sane N0 ->
      net_sane N1.

    Proof.
      intros.

      constructor.
      - eauto using trans_invariant_net_sane_comm__SRPC_sane with LTS.
      - eauto using trans_invariant_net_sane_comm__locks_sound with LTS.
      - eauto using trans_invariant_net_sane_comm__locks_complete with LTS.
    Qed.


    Theorem trans_invariant_net_sane [a] [N0 N1 : PNet] :
      (N0 =(a)=> N1) ->
      net_sane N0 ->
      net_sane N1.

    Proof.
      intros.
      destruct a.
      - eauto using trans_invariant_net_sane_tau.
      - eauto using trans_invariant_net_sane_comm.
    Qed.


    Proof using Type.
      repeat (intros ?).

      constructor; intros m0; try (intros m1); intros.
      all: Control.enter (fun () => smash_eq_on m0 n0 n1); subst.
      all: eauto using trans_invariant_net_sane__net_sane_comm__self,
        trans_invariant_net_sane__net_sane_comm__sender,
        trans_invariant_net_sane__net_sane_comm__receiver.
      all: try (unfold net_lock_on, net_lock in *; exists [m1]; split > [attac|]).
      - admit.
      - replace (NetMod.get m1 N1) with (NetMod.get m1 N0); attac.
        eapply (@act_particip_stay PQued PAct); attac. ; consider (net_sane N0); attac)

      all: try (Control.enter (fun _ => replace (NetMod.get m0 N1) with (NetMod.get m0 N0)
                       by (eapply (@act_particip_stay PQued PAct); attac); consider (net_sane N0); attac)).
      . (* TODO automate *)
      -

      constructor; intros n; intros.
      - Control.enter (fun () => smash_eq_on n n0 n1); subst.
      eauto using trans_invariant_net_sane__net_sane_comm__self,
        trans_invariant_net_sane__net_sane_comm__sender,
        trans_invariant_net_sane__net_sane_comm__receiver.

      replace (NetMod.get n N1) with (NetMod.get n N0); attac.
               compat_hsimpl in *. eapply (@act_particip_stay PQued PAct). attac.


      Control.enter (fun () => smash_eq_on n n0 n1); subst.
       eauto using trans_invariant_net_sane__net_sane_comm__self,
         trans_invariant_net_sane__net_sane_comm__sender,
         trans_invariant_net_sane__net_sane_comm__receiver.

      all: try (replace (NetMod.get n N1) with (NetMod.get n N0)
               by (eapply (@act_particip_stay PQued PAct); attac)).
      - replace (NetMod.get n N1) with (NetMod.get n N0)
          by (eapply (@act_particip_stay PQued PAct); attac). (* TODO This typeclass sucks *)

        consider (net_sane N0); auto.
      -
      -
    Qed.

      have (N0 =(NComm n0 n1 &t v)=> N1) as T'.

      kill Hs0.
      rename H_Sane_SRPC into Hsrpc0.

      kill T.
      rename H into T_s.
      rename H0 into T_r.

      destruct (Name.eq_dec n' n1); destruct (Name.eq_dec n' n0); subst.

      4: specialize (Hsrpc0 n'); rewrite (NV_stay T_s) in *; eauto; rewrite (NV_stay T_r) in *; eauto.

      all: kill T_s; rename H into T_s.
      all: kill T_r; rename H into T_r.

      all: assert (exists srpc, SRPC_sane srpc (NetMod.get n0 N0)) as Hsrpc_s by auto.
      2,3: assert (exists srpc, SRPC_sane srpc (NetMod.get n1 N0)) as Hsrpc_r by auto.

      all: repeat (ltac1:(simpl_net)). (* TODO FIXME: why repeat? *)

      all: destruct (NetMod.get n0 N0) as [Is0 Ps0 Os0] eqn:HEqNs0;
        destruct S as [Is1 Ps1 Os1] eqn:HEqNs1.
      2,3: destruct (NetMod.get n1 N0) as [Ir0 Pr0 Or0] eqn: HEqNr0.
      all: destruct S0 as [Ir1 Pr1 Or1] eqn:HEqNr1.

      all: destruct t.

      - (* Sender is the recipient: Q *)
        compat_hsimpl in *.

        kill Hsrpc_s.

        specialize (H_Q_out_lock n0 v ltac:(eattac)).
        hsimpl in H_Q_out_lock.
        exists (Lock c n0).

        assert (Or1 = []).
        {
          intros.
          clear - H_Q_out_last.
          destruct Or1; auto.
          specialize (H_Q_out_last n0 v).
          bullshit.
        }
        subst.

        assert (forall s v', ~ List.In (s, R, v') Is1) as HNIn.
        {
          intros * Hx.
          specialize (H_R_in_lock _ _ Hx).
          hsimpl in H_R_in_lock.
          eapply H_R_Q in Hx.
          apply Hx.
          eattac.
        }

        assert (forall s v', ~ List.In (s, R, v') ([(n0, Q, v)])) as HNIn' by (intros * Hx; kill Hx).

        assert (~ pq_client n0 (NetMod.get n0 N0)) as HNc.
        {
          intros HL.
          apply H_lock_complete in HL.
          destruct HL as [L [HIn HL]].
          eapply net_sane_get_lock_In in HL; eauto with LTS.
          unfold net_lock in HL.
          rewrite HEqNs0 in HL.
          kill HL.
        }

        assert (~ proc_client n0 Pr1) as HNcP by (rewrite HEqNs0 in HNc; attac).

        constructor; eauto with LTS datatypes; intros.
        + destruct (Name.eq_dec c0 n0); subst.
          * assert (forall v, ~ List.In (n0, Q, v) Is1).
            {
              intros ? Hx.
              apply HNc.
              rewrite HEqNs0.
              econstructor 1.
              eauto.
            }
            apply Deq_app_or_r in H; eauto.
            hsimpl in H.
            kill H.
            compat_hsimpl.
            eauto with LTS.
          * assert (forall v', ~ List.In (c0, Q, v') [(n0, Q, v)]) by (intros * Hx; kill Hx).
            apply Deq_app_or_l in H; eauto.
            hsimpl in H.
            intros Hx.
            apply in_app_or in Hx as [?|?]; bullshit.

        + apply Deq_app_or_l in H; eauto.
          hsimpl in H.
          attac.
        + apply in_app_or in H as [?|?]; bullshit.
        + bullshit.
        + bullshit.
        + bullshit.
        + assert (forall v', List.In (c, R, v') (Is1 ++ [(n0, Q, v)]) -> List.In (c, R, v') Is1).
          {
            intros.
            apply in_app_or in H as [?|?]; auto.
            kill H.
          }

          specialize (H_query_uniq c0).
          destruct_mut_exclusive @H_query_uniq.

          destruct (Name.eq_dec c0 n0); subst.
          * solve_mut_exclusive true;
            Control.enter (
                fun () => repeat (match! goal with
                               | [h : exists _, _ |- _] => strip_exists h; ()
                               end)
              ); bullshit.

          * assert (forall v', List.In (c0, Q, v') (Is1 ++ [(n0, Q, v)]) -> List.In (c0, Q, v') Is1).
            { intros * Hx.
              apply in_app_or in Hx as [?|?]; auto.
              kill H5.
            }

          solve_mut_exclusive true;
            Control.enter (
                fun () => repeat (match! goal with
                               | [h : exists _, _ |- _] => strip_exists h; ()
                               end)
              ); bullshit.

      - (* Sender is the recipient: R *)

        absurd (n0 <> n0). 1: bullshit.
        eapply net_sane_no_self_reply; eattac.

      - (* Let's talk about the recipient: Q *)
        kill T_s; kill T_r.
        destruct Hsrpc_r as [srpc_r Hsrpc_r].

        exists srpc_r.

        hsimpl in *.
        kill Hsrpc_r.

        assert (~ pq_client n0 (NetMod.get n1 N0)) as HNc.
        {
          intros HL.
          apply H_lock_complete in HL.
          destruct HL as [L [HIn HL]].
          eapply net_sane_get_lock_In in HL; eauto with LTS.
          unfold net_lock in HL.
          rewrite HEqNs0 in HL.
          kill HL.
        }

        assert (forall v', ~ List.In (n0, Q, v') Ir0) as HNIn.
        {
          intros v' Hx.
          rewrite HEqNr0 in HNc.
          eauto with LTS.
        }

        constructor; eauto with LTS datatypes; intros.
        + destruct (Name.eq_dec c n0); subst.
          * specialize (Deq_app_or_r H (HNIn v0)) as HDeq'.
            hsimpl in HDeq'.
            kill HDeq'.
            compat_hsimpl.
            eauto.
          * assert (~ List.In (c, Q, v0) [(n0, Q, v)]) as HNIn' by (intros Hx; kill Hx).
            specialize (Deq_app_or_l H HNIn') as HDeq'.
            hsimpl in HDeq'.
            eapply H_Q_in with (v':=v') in HDeq'.
            intros Hx.
            apply in_app_or in Hx as [?|?].
            bullshit.
            kill H0.
        + assert (~ List.In (s, R, v0) [(n0, Q, v)]) as HNIn' by (intros Hx; kill Hx).
          specialize (Deq_app_or_l H HNIn') as HDeq'.
          hsimpl in HDeq'.
          eapply H_R_in with (v':=v') in HDeq'.
          intros Hx.
          apply in_app_or in Hx as [?|?].
          bullshit.
          kill H0.
        + apply in_app_or in H as [?|?].
          eauto.
          kill H.
        + apply in_app_or in H as [?|?].
          eauto.
          kill H.
        + hsimpl in H.
          intros Hx.
          apply in_app_or in Hx as [?|?].
          2: kill H0.
          bullshit.

        + assert (forall v', List.In (c, R, v') (Ir0 ++ [(n0, Q, v)]) -> List.In (c, R, v') Ir0).
          {
            intros.
            apply in_app_or in H as [?|?]; auto.
            kill H.
          }

          rewrite HEqNr0 in HNc.

          specialize (H_query_uniq c).
          destruct_mut_exclusive @H_query_uniq.

          destruct (Name.eq_dec c n0); subst.
          * solve_mut_exclusive true;
            Control.enter (
                fun () => repeat (match! goal with
                               | [h : exists _, _ |- _] => strip_exists h; ()
                               end)
              ); bullshit.

          * assert (forall v', List.In (c, Q, v') (Ir0 ++ [(n0, Q, v)]) -> List.In (c, Q, v') Ir0).
            { intros * Hx.
              apply in_app_or in Hx as [?|?]; auto.
              kill H5.
            }

          solve_mut_exclusive true;
            Control.enter (
                fun () => repeat (match! goal with
                               | [h : exists _, _ |- _] => strip_exists h; ()
                               end)
              ); bullshit.

      - (* Let's talk about the recipient: R *)
        kill T_s; kill T_r.
        destruct Hsrpc_r as [srpc_r Hsrpc_r].

        exists srpc_r.

        hsimpl in *.
        (* kill Hsrpc_r. *)

        assert (net_lock_on N0 n1 n0) as HL.
        {
          enough (pq_client n1 (NetMod.get n0 N0)) as Hc by auto.

          rewrite HEqNs0.
          econstructor 3.
          attac.
        }

        assert (exists c, srpc_r = Lock c n0) as [c HEq].
        {
          destruct HL as [L [HIn HL]].
          eapply net_sane_get_lock_In in HL; eauto with LTS.
          kill HL.
          rewrite HEqNr0 in H2.
          kill H2.
          have (SRPC_pq srpc_r (pq Ir0 Pr1 [])) by eauto with LTS.
          have (SRPC srpc_r Pr1) by re_have (eauto with LTS).
          apply (lock_SRPC_Lock) in H0; re_have (eauto with LTS).
          hsimpl in H0.
          eexists.
          eapply SRPC_inv; re_have eauto.
        }
        subst.

        assert (forall s' v', ~ List.In (s', R, v') Ir0) as HNIn.
        {
          intros.
          intros Hx.
          destruct (Name.eq_dec s' n0); subst.
          -  destruct HL as [L [HIn HL]].
            eapply net_sane_get_lock_In in HL; eauto with LTS.
            kill HL.
            rewrite HEqNr0 in H2.
            kill H2.
            bullshit.
          - consider (exists c', (Lock c n0) = (Lock c' s')) by eauto with LTS.
        }

        constructor; eauto with datatypes LTS; intros.
        + enough (SRPC_pq (Lock c n0) (pq Ir0 Pr1 Or1)); eauto with LTS.
        + assert (~ List.In (c0, Q, v0) [(n0, R, v)]) as HNIn' by (intros Hx; kill Hx).
          specialize (Deq_app_or_l H HNIn') as HDeq'.
          hsimpl in HDeq'.
          assert (not (List.In (c0, Q, v0) Q1')) by eauto with LTS.
          intros Hx.
          apply in_app_or in Hx as [?|?].
          bullshit.
          attac.
        + eapply (Deq_app_or_r) in H; eauto.
          hsimpl in H.
          kill H; hsimpl in *; attac.
        + apply in_app_or in H as [?|?]; eauto with LTS.
          kill H. kill H0.
          eattac.
        + apply in_app_or in H as [?|?]; eauto with LTS.
          kill H. kill H0.
          destruct HL as [L [HIn HL]].
          kill HL.
          rewrite HEqNr0 in H2.
          kill H2.
          bullshit.
        + destruct HL as [L [HIn HL]].
          kill HL.
          rewrite HEqNr0 in H3.
          kill H3.
        + consider (c = c0) by attac.
          consider (n0 = s) by attac.
          eauto with LTS.
        + assert (forall v', List.In (c0, Q, v') (Ir0 ++ [(n0, R, v)]) -> List.In (c0, Q, v') Ir0).
          {
            intros.
            apply in_app_or in H as [?|?]; auto.
            kill H.
          }

          kill Hsrpc_r.
          specialize (H_query_uniq c0).
          destruct_mut_exclusive @H_query_uniq.
          solve_mut_exclusive true;
            try (ltac1:(replace c with c0 in * by auto));
            Control.enter (
                fun () => repeat (match! goal with
                               | [h : exists _, _ |- _] => strip_exists h; ()
                               end)
              ); bullshit.

      - (* Let's talk about the sender: Q *)

        kill T_s; kill T_r.
        destruct Hsrpc_s as [srpc_s Hsrpc_s].

        exists srpc_s.

        kill HEnq.

        kill Hsrpc_s.

        edestruct (H_Q_out_lock) as [c Hsrpc_s'].
        1: left; reflexivity.
        subst.

        constructor; eauto with datatypes LTS; intros.
        + intros HIn.
          eapply H_Q_out_last.
          destruct Os1; eattac.
        + assert ((c0, R) <> (n1, Q)) by bullshit.
          assert (Deq (c0, R) v0 ((n1, Q, v) :: Os1) ((n1, Q, v) :: O')) by attac.
          eapply H_R_out_uniq in H1.
          eattac.
        + eattac.
        + exfalso.
          kill H.
          edestruct H_lock_Q.
          1: eauto.
          1: bullshit.
          eapply H_Q_out_last.
          destruct Os1.
          1: bullshit.
          simpl.
          eauto.
        + specialize (H_query_uniq c0).
          destruct_mut_exclusive @H_query_uniq.

          assert (proc_client c0 Ps1 -> c0 = c).
          {
            intros PC.
            destruct PC as [srpcb Hsrpc'].
            apply (SRPC_inv Hsrpc) in Hsrpc'.
            kill Hsrpc.
          }

          solve_mut_exclusive true;
            try (ltac1:(replace c0 with c in * by auto));
            Control.enter (
                fun () => match! goal with
                       | [h : exists _, _ |- _] => strip_exists h; bullshit
                       end
              ).
      - (* Let's talk about the sender: R *)

        destruct Hsrpc_s as [srpc_s Hsrpc_s].
        exists srpc_s.

        kill T_s; kill T_r.
        kill HEnq.

        kill Hsrpc_s.

        constructor; eauto with datatypes LTS; intros.
        + intros HIn.
          eapply H_Q_out_last.
          destruct Os1; eattac.
        + assert (Deq (c, R) v0 ((n1, R, v) :: Os1) ((n1, R, v) :: O')).
          {
            destruct (Name.eq_dec c n1); subst.
            - attac.
            - assert ((c, R) <> (n1, R)) by bullshit.
              attac.
          }
          eapply H_R_out_uniq in H0.
          eattac.
        + eattac.
        + subst.
          edestruct H_lock_Q.
          1: eauto.
          1: bullshit.
          kill H.
          eattac.
        + specialize (H_query_uniq c).
          destruct_mut_exclusive @H_query_uniq.

          solve_mut_exclusive true;
            try (ltac1:(replace c0 with c in * by auto));
            Control.enter (
                fun () => match! goal with
                       | [h : exists _, _ |- _] => strip_exists h; bullshit
                       end
              ).
    Qed.

    Ltac2 fill_pred () :=
      let check_f f :=
        (multi_match! get_left_app f with | pq_lock => () | pq_client => () | (SRPC_pq _) => () | _ => fail end)
      in
      match! goal with
      | [eq : (NetMod.get ?n ?net) = ?c, h : context [?f (NetMod.get ?n ?net)] |- _] =>
          check_f f;
          if is_constructor_app c
          then let eqh := hyp eq in rewrite $eqh in $h
          else fail
      | [eq : (NetMod.get ?n ?net) = ?c |- context [?f (NetMod.get ?n ?net)]] =>
          check_f f;
          if is_constructor_app c
          then let eqh := hyp eq in rewrite $eqh
          else fail
      end.


    Ltac2 fill_preds () := repeat (fill_pred ()).

    Lemma trans_invariant_net_sane_comm [n0 n1 t v] [N0 N1 : PNet] :
      (N0 =(NComm n0 n1 t v)=> N1) ->
      net_sane N0 ->
      net_sane N1.

    Proof.
      intros T HNs0.

      assert (net_sane N1) as HsrpcN1
          by (eauto using trans_invariant_net_sane_comm).

      destruct t.
      - (* Query *)

        assert (net_lock_on N1 n0 n1) as HL
            by eauto using net_sane_query_new_lock with LTS.

        constructor; auto.
        + intros c s HL'.

          unfold net_lock in *.
          kill T.

          smash_eq n0 c.
          -- assert (n1 = s) by ltac1:(eauto using lock_uniq with LTS).
             compat_hsimpl in *.
             eattac.
          -- assert (net_lock_on N0 c s).
             {
               apply lock_singleton in HL'. 2: attac.
               exists [s]. split. 1: attac.
               unfold net_lock in *.
               smash_eq c n1; compat_hsimpl in *; fill_preds (); kill HL'; attac.
             }
             assert (pq_client c (NetMod.get s N0)) by (kill HNs0; attac).

             compat_hsimpl in *.
             smash_eq s n1 n0; attac.
             ++ kill H2; hsimpl in *; attac.
             ++ kill H2; hsimpl in *; attac.

        + intros c s HL'.

          assert (forall (x y : Name), x <> n1 -> pq_client y (NetMod.get x N1) -> pq_client y (NetMod.get x N0)) as Hback.
          {
            intros * ? HL1.
            kill T.
            hsimpl in *.
            smash_eq x n0; compat_hsimpl in *; fill_preds (); kill HL1; attac.
          }

          smash_eq n1 s.
          -- smash_eq c n0.
             kill T.
             compat_hsimpl in *.
             exists [n1]; split; auto with datatypes.
             apply lock_singleton in HL; attac.
             unfold net_lock in *.
             smash_eq c n1; compat_hsimpl in *; hsimpl in |- *.
             ++ enough (pq_lock [c] (pq I0 P0 O0)).
                {
                  kill H1.
                  eattac.
                  apply in_app_or in H5 as [|]; eattac.
                }

                rewrite <- H0.
                enough (net_lock_on N0 c c) as Hx by (apply lock_singleton in Hx; eattac).
                enough (pq_client c (NetMod.get c N0)) by (kill HNs0; attac).
                fill_preds().
                kill HL'; eattac.
                apply in_app_or in H1 as [|]; eattac.
             ++ enough (net_lock_on N0 c n1) as Hx by (apply lock_singleton in Hx; eattac).
                enough (pq_client c (NetMod.get n1 N0)) by (kill HNs0; attac).
                smash_eq n0 n1; compat_hsimpl in *.
                ** fill_preds ().
                   kill HL'; eattac.
                   apply in_app_or in H0 as [|]; eattac.
                ** fill_preds ().
                   kill HL'; eattac.
                   apply in_app_or in H1 as [|]; eattac.

          -- specialize (Hback s c HEq HL').
             assert (net_lock_on N0 c s) by (kill HNs0; attac).
             kill T.
             exists [s]; split; auto with datatypes.
             apply lock_singleton in H. 2: attac.
             assert (not_unlocking_msg [s] (send (n1, Q) v)) by (unfold not_unlocking_msg; attac).
             assert (not_unlocking_msg [s] (recv (n0, Q) v)) by (unfold not_unlocking_msg; attac).

             enough (net_lock N0' [s] c).
             {
               unfold net_lock in *.
               kill H1.
               smash_eq c n1.
               - hsimpl in |- *.
                 eapply (apply_invariant (@pq_lock_invariant [s])); eauto.
               - attac.
             }

             unfold net_lock in *.
             kill H0.
             smash_eq c n0.
             ++ hsimpl in |- *.
                eapply (apply_invariant (@pq_lock_invariant [s])); eauto.
             ++ attac.

      - (* Reply *)

        assert (n0 <> n1) by (eapply net_sane_no_self_reply; eauto).

        assert (net_lock_on N0 n1 n0) as HL
            by eauto using net_sane_reply_lock with LTS.

        constructor; auto.
        + intros c s HL'.

          assert (net_lock_on N0 c s).
          {
            apply lock_singleton in HL'. 2: attac.
            smash_eq c n1; compat_hsimpl in *.
            - assert (n0 = s).
              {
                apply lock_singleton in HL. 2: attac.
                apply lock_SRPC_Lock_pq in HL as [c' Hsrpc']. 2: attac.
                unfold net_lock in HL'.
                consider (N0 =(_)=> N1).
                compat_hsimpl in *.
                assert (pq_lock [s] (NetMod.get c N0)) as HL''.
                {
                  kill HL'; hsimpl in *; fill_preds (); attac.
                }

                apply lock_SRPC_Lock_pq in HL'' as [c'' Hsrpc'']. 2: attac.
                consider (Lock c' n0 = Lock c'' s); attac.
              }
              attac.
            - consider (N0 =(_)=> N1); compat_hsimpl in *.
              unfold net_lock in HL'.
              hsimpl in HL'.
              exists [s]; split; auto with datatypes.
              apply lock_singleton in HL. 2: attac.
              unfold net_lock in *.
              smash_eq c n0; compat_hsimpl in *; auto.
              kill HL'.
              hsimpl in *.
              (* fill_preds (). *)

              assert (AnySRPC_pq (NetMod.get c N0)) as [srpc Hsrpc] by attac.
              consider (exists c', SRPC (Lock c' s) P1) by (eapply lock_SRPC_Lock; attac).

              assert (SRPC_sane (Lock c' s) (pq I1 P1 [(n1, R, v)])) as Hsrpc'.
              {
                kill HNs0.
                specialize (H_Sane_SRPC c) as [? ?].
                consider (x = Lock c' s). eauto using SRPC_pq_inv with LTS.
                cbv in *; rewrite <- `(NetMod.get c N0 = _).
                auto.
              }

              (* TODO that notation sucks (simpl) *)
              consider (exists v0 : Val, List.In (s, Q, v0) [(n1, R, v)]) by (simpl in * |-; eauto with LTS).
              bullshit.
          }
          assert (pq_client c (NetMod.get s N0)) as HC by (kill HNs0; attac).

          hsimpl in *; hsimpl in *; fill_preds ().

          consider (N0 =(_)=> N1); compat_hsimpl in *.
          smash_eq c s n0 n1; hsimpl in |- *; auto with LTS; hsimpl in *.
          all: eauto with LTS.

          * absurd (pq_lock [c] (pq I1 P1 ((n1, R, v) :: O1))). 1: intros Hx; kill Hx. (* TODO bullshit *)
            apply lock_singleton in H0. 2: attac.
            unfold net_lock in *. fill_preds (). auto.
          * hsimpl in *.
            apply lock_singleton in HL'. 2: attac.
            unfold net_lock in *.
            hsimpl in HL'.
            kill HL'.
            absurd ( ~ List.In (s, R, v) (I0 ++ [(s, R, v)])).
            1: intros Hx; attac.
            attac.
          * fill_preds ().
            kill HC; eattac 2.

        + intros c s HL'.

          kill T; do 2 (compat_hsimpl in *).

          smash_eq c n1.
          * smash_eq s n0; compat_hsimpl in *.
            -- exfalso.
               assert (net_sane N0) as HsrpcN0 by eauto with LTS.
               specialize (HsrpcN0 s) as [srpc Hsrpc].
               kill Hsrpc.
               specialize (H_query_uniq c).
               destruct_mut_exclusive @H_query_uniq.
               kill HL'; attac.
            -- exfalso.

               apply lock_singleton in HL. 2: attac.
               unfold net_lock in *.
               fill_preds ().
               assert (exists c', SRPC_pq (Lock c' n0) (pq I0 P0 O0)) as [c' Hsrpc'].
               {
                 apply lock_SRPC_Lock_pq.
                 rewrite <- H1.
                 all: attac.
               }
               kill HL.

               enough (exists c'', SRPC_pq (Lock c'' s) (pq I0 P0 [])) as [c'' Hsrpc''].
               {
                 assert (Lock c' n0 = Lock c'' s) by (eapply SRPC_inv; attac).
                 attac.
               }
               enough (exists c'', SRPC (Lock c'' s) P0) by (hsimpl in *; exists c''; constructor; kill H5; attac).
               enough (pq_client c (NetMod.get s N0)).
               {
                 assert (net_lock_on N0 c s) by (kill HNs0; attac).
                 apply lock_singleton in H6; attac.
                 eapply lock_SRPC_Lock; attac.
               }
               smash_eq s c; hsimpl in *; auto.
               fill_preds ().
               kill HL'; eattac.
               apply in_app_or in H5 as [|]; eattac; kill H5.
          * assert (pq_client c (NetMod.get s N0)).
            {
              smash_eq s n0 n1; hsimpl in *; fill_preds (); kill HL'; attac.
              assert (List.In (c, Q, v0) I0) by (apply in_app_or in H2 as [|]; attac; kill H2).
              attac.
            }
            assert (net_lock_on N0 c s) by (kill HNs0; attac).
            apply lock_singleton in H3. 2: attac.
            exists [s]; split; auto with datatypes.
            unfold net_lock in *; hsimpl in *; hsimpl in |- *.
            smash_eq c n0; hsimpl in |- *; auto.
            fill_preds ().
            kill H3.
    Qed.


    Theorem trans_invariant_net_sane : trans_invariant net_sane always.

    Proof with (eauto with LTS).
      unfold trans_invariant.
      intros N0 N1 a TN HNs0 _.

      destruct a.
      - kill TN.
        hsimpl in *.
        eapply trans_invariant_net_sane_tau; eauto.
        attac.
      - eapply trans_invariant_net_sane_comm; eauto.
    Qed.

    #[export] Hint Resolve trans_invariant_net_sane : inv.
    #[export] Hint Extern 0 (net_sane _) => solve_invariant : LTS.



  Print net_undep_send_inv.
  Goal Net.Model.Que.Channel.Name = Name.
End Srpc.
