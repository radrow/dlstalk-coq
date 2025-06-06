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
From Coq Require Import Structures.Orders.
From Coq Require Import Structures.OrdersFacts.
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

  Lemma dm_ltb_pass : forall dm0 dm1, dm_pass dm0 < dm_pass dm1 ->
                                 dm_ltb dm0 dm1 = true.
  Proof.
    intros.
    destruct dm0, dm1; simpl in *.
    unfold dm_ltb in *; simpl.
    destruct (dm_pass0 =? dm_pass1) eqn:?.
    - rewrite PeanoNat.Nat.eqb_eq in *; lia.
    - now rewrite PeanoNat.Nat.ltb_lt.
  Qed.

  Hint Resolve dm_ltb_pass : LTS.

  Lemma dm_leb_asim : forall dm0 dm1,
      dm_leb dm0 dm1 = true ->
      dm_leb dm1 dm0 = true ->
      dm0 = dm1.
  Proof.
    intros.
    destruct dm0, dm1.
    unfold dm_leb in *.
    simpl in *.
    blast_cases; attac.
    all: try (rewrite PeanoNat.Nat.eqb_eq in * ).
    all: try (rewrite PeanoNat.Nat.eqb_neq in * ).
    all: try (rewrite PeanoNat.Nat.leb_le in * ).
    all: subst; auto.
    all: bs.
  Qed.

  Lemma dm_leb_trans : forall dm0 dm1 dm2,
      dm_leb dm0 dm1 = true ->
      dm_leb dm1 dm2 = true ->
      dm_leb dm0 dm2 = true.
  Proof.
    intros.
    destruct dm0, dm1, dm2.
    unfold dm_leb in *.
    simpl in *.
    destruct (dm_pass0 =? dm_pass1) eqn:?;
      destruct (dm_pass1 =? dm_pass2) eqn:?;
      destruct (dm_pass0 =? dm_pass2) eqn:?;
      destruct (dm_flush0 =? dm_flush1) eqn:?;
      destruct (dm_flush1 =? dm_flush2) eqn:?;
      destruct (dm_flush0 =? dm_flush2) eqn:?.
    all: auto.

    all: try (rewrite PeanoNat.Nat.eqb_eq in * ).
    all: try (rewrite PeanoNat.Nat.eqb_neq in * ).
    all: rewrite PeanoNat.Nat.leb_le in *; lia.
  Qed.

  Lemma dm_leb_total : forall dm0 dm1,
      dm_leb dm0 dm1 = true \/ dm_leb dm0 dm1 = false.
  Proof. intros. destruct (dm_leb dm0 dm1) eqn:?; auto. Qed.

  Lemma dm_leb_ltp : forall dm0 dm1,
      dm_leb dm0 dm1 = dm_eqb dm0 dm1 || dm_ltb dm0 dm1.
  Proof.
    intros.
    destruct dm0, dm1.
    unfold dm_leb, dm_ltb, dm_eqb, andb, orb in *.
    simpl in *.
    blast_cases; auto.

    all: try (rewrite PeanoNat.Nat.eqb_eq in * ).
    all: try (rewrite PeanoNat.Nat.eqb_neq in * ).
    all: try (rewrite PeanoNat.Nat.leb_le in * ).
    all: try (rewrite PeanoNat.Nat.ltb_lt in * ).
    all: subst.
    all: doubt.
    - destruct (dm_flush0 <? dm_flush1) eqn:?.
      + rewrite PeanoNat.Nat.leb_le in *.
        rewrite PeanoNat.Nat.ltb_lt in *.
        lia.
      + rewrite PeanoNat.Nat.leb_nle in *.
        rewrite PeanoNat.Nat.ltb_nlt in *.
        lia.
    - destruct (dm_pass0 <? dm_pass1) eqn:?.
      + rewrite PeanoNat.Nat.leb_le in *.
        rewrite PeanoNat.Nat.ltb_lt in *.
        lia.
      + rewrite PeanoNat.Nat.leb_nle in *.
        rewrite PeanoNat.Nat.ltb_nlt in *.
        lia.
    - destruct (dm_pass0 <? dm_pass1) eqn:?.
      + rewrite PeanoNat.Nat.leb_le in *.
        rewrite PeanoNat.Nat.ltb_lt in *.
        lia.
      + rewrite PeanoNat.Nat.leb_nle in *.
        rewrite PeanoNat.Nat.ltb_nlt in *.
        lia.
  Qed.


  Lemma dm_leb_not_ltp : forall dm0 dm1, dm_leb dm0 dm1 = negb (dm_ltb dm1 dm0).
  Proof.
    intros.
    destruct dm0, dm1.
    unfold dm_ltb, dm_leb, negb.
    simpl.
    blast_cases.

    all: try (rewrite PeanoNat.Nat.eqb_eq in * ).
    all: try (rewrite PeanoNat.Nat.eqb_neq in * ).
    all: subst; try (congruence).
    all: try (rewrite PeanoNat.Nat.leb_le in * ).
    all: try (rewrite PeanoNat.Nat.leb_nle in * ).
    all: try (rewrite PeanoNat.Nat.ltb_lt in * ).
    all: try (rewrite PeanoNat.Nat.ltb_nlt in * ).
    all: attac.
  Qed.

  Lemma dm_ltb_neq : forall dm0 dm1,
      dm_ltb dm0 dm1 = true ->
      dm_eqb dm0 dm1 = false.
  Proof.
    intros.
    destruct dm0, dm1.
    unfold dm_ltb, dm_eqb in *.
    simpl in *.
    blast_cases; attac.
  Qed.

  Lemma measure_zero_lowest : forall dm, dm_leb dm_zero dm = true.
  Proof.
    intros.
    destruct dm.
    unfold dm_zero, dm_leb.
    simpl.
    blast_cases; attac.
  Qed.

  Lemma dm_ltb_wf : well_founded (fun dm0 dm1 => dm_ltb dm0 dm1 = true).
  Proof.
    unfold well_founded.
    intros dm0.
    destruct dm0.
    generalize dependent dm_flush0.

    induction (PeanoNat.Nat.lt_wf_0 dm_pass0).
    intros.

    induction (PeanoNat.Nat.lt_wf_0 dm_flush0).

    constructor.
    intros dm1 **.
    destruct dm1; simpl in *.
    unfold dm_ltb in *; simpl in *.

    destruct (dm_pass0 =? x) eqn:?.
    - rewrite PeanoNat.Nat.eqb_eq in *.
      subst.
      eapply H2.
      destruct (dm_flush0 =? x0) eqn:?; attac.
      now rewrite PeanoNat.Nat.ltb_lt in *.
    - rewrite PeanoNat.Nat.ltb_lt in *.
      eauto.
  Qed.


  Module DetectMeasureOrder <: OrderedTypeFull with Definition t := DetectMeasure.
    Definition t := DetectMeasure.
    Definition lt := fun dm0 dm1 => dm_ltb dm0 dm1 = true.
    Definition le := fun dm0 dm1 => dm_leb dm0 dm1 = true.
    Definition eq := fun dm0 dm1 => dm_eqb dm0 dm1 = true.

    Instance eq_equiv : Equivalence eq.
    constructor; repeat (intros ?); unfold eq in *; rewrite dm_eqb_eq in *; attac.
    Qed.

    Instance lt_strorder : StrictOrder lt.
    constructor.
    - unfold Irreflexive, Reflexive, complement, lt, dm_ltb. intros.
      destruct x; blast_cases; attac.
    - unfold Transitive, lt, dm_ltb; intros.
      destruct x, y, z; simpl in *.
      destruct
        (dm_pass0 =? dm_pass1) eqn:?,
        (dm_pass1 =? dm_pass2) eqn:?,
        (dm_pass0 =? dm_pass2) eqn:?,
        (dm_flush0 =? dm_flush1) eqn:?,
        (dm_flush1 =? dm_flush2) eqn:?,
        (dm_flush0 =? dm_flush2) eqn:?.
      all: try (congruence).
      all: try (rewrite PeanoNat.Nat.eqb_eq in * ).
      all: try (rewrite PeanoNat.Nat.eqb_neq in * ).
      all: try (rewrite PeanoNat.Nat.ltb_lt in * ).
      all: subst; lia.
    Qed.

    Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
    split; attac; unfold eq, lt in *; rewrite dm_eqb_eq in *; attac.
    Qed.

    Definition compare dm0 dm1 : comparison :=
      if dm_ltb dm0 dm1 then Lt
      else if dm_ltb dm1 dm0 then Gt
           else Eq.

    Lemma compare_spec : forall dm0 dm1,
        CompareSpec
          (eq dm0 dm1)
          (lt dm0 dm1)
          (lt dm1 dm0)
          (compare dm0 dm1).
    Proof.
      unfold compare.
      intros.
      destruct (dm_ltb dm0 dm1) eqn:?.
      1: { constructor; attac. }
      destruct (dm_ltb dm1 dm0) eqn:?.
      1: { constructor; attac. }
      constructor.
      unfold eq.
      destruct (dm_eqb dm0 dm1) eqn:?; auto.
      unfold dm_ltb in *.
      rewrite dm_eqb_neq in Heqb1.
      destruct dm0, dm1; simpl in *.
      destruct
        (dm_pass0 =? dm_pass1) eqn:?, (dm_flush0 =? dm_flush1) eqn:?,
        (dm_pass1 =? dm_pass0) eqn:?, (dm_flush1 =? dm_flush0) eqn:?; auto.
      all: simpl in *.
      all: try (rewrite PeanoNat.Nat.eqb_eq in * ).
      all: try (rewrite PeanoNat.Nat.eqb_neq in * ).
      all: try (rewrite PeanoNat.Nat.ltb_lt in * ).
      all: try (rewrite PeanoNat.Nat.ltb_nlt in * ).
      all: subst.
      all: try (lia).
      attac.
    Qed.

    Lemma eq_dec : forall dm0 dm1, {eq dm0 dm1}+{~ eq dm0 dm1}.
    Proof. unfold eq; intros; destruct (dm_eqb dm0 dm1); eauto. Qed.

    Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
    Proof.
      split; intros.
      - unfold lt, le in *.
        rewrite dm_leb_ltp in H.
        apply orb_prop in H.
        destruct `(_ \/ _); eauto.
      - unfold lt, le, eq, dm_ltb, dm_leb in *.
        destruct x, y.
        attac.
        destruct (dm_pass0 =? dm_pass1) eqn:?, (dm_flush0 =? dm_flush1) eqn:?; auto.
        all: try (destruct `(_ \/ _)).
        all: try (rewrite PeanoNat.Nat.eqb_eq in * ).
        all: try (rewrite PeanoNat.Nat.eqb_neq in * ).
        all: try (rewrite PeanoNat.Nat.ltb_lt in * ).
        all: try (rewrite PeanoNat.Nat.leb_le in * ).
        all: lia.
    Qed.
  End DetectMeasureOrder.

  Module DetectMeasureOrder' <: OrderedTypeFull' with Definition t := DetectMeasure
    := DetectMeasureOrder <+ EqLtLeNotation.

  Module DetectMeasureTO := OTF_to_TotalOrder(DetectMeasureOrder).

  Module DetectMeasureOF <: OrderFunctions(DetectMeasureOrder).
    Import DetectMeasureOrder.
    Module Import DetectMeasureOrderFacts := OrderedTypeFullFacts(DetectMeasureOrder').

    Definition eqb := dm_eqb.
    Definition ltb := dm_ltb.
    Definition leb := dm_leb.
    Lemma eqb_eq : forall x y : t, eqb x y = true <-> eq x y. split; intros; auto. Qed.
    Definition ltb_lt : forall x y : t, ltb x y = true <-> lt x y. split; intros; auto. Qed.
    Definition leb_le : forall x y : t, leb x y = true <-> le x y. split; intros; auto. Qed.
    Definition compare := compare.

    Lemma compare_spec : forall dm0 dm1,
        CompareSpec
          (eq dm0 dm1)
          (lt dm0 dm1)
          (lt dm1 dm0)
          (compare dm0 dm1).
      exact compare_spec.
    Qed.
  End DetectMeasureOF.

  Import DetectMeasureOrder'.


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
      destruct (alarm (MSend (a, t0) p (MSend_all ws t0 p M))) eqn:?; hsimpl in H; attac.
      unfold option_map in *.
      destruct MQ; attac.
      unfold option_map in *.
      destruct (measure_mon_fin (MSend_all ws t0 p M)) eqn:?.
      consider (m0 = m).
      {
        transitivity '(next_state (MSend_all ws t0 p M)).
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
        destruct ( measure_mon_fin (MSend_all ws t0 p M) ) eqn:?; attac.
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
    - destruct (measure_mon_fin (MSend (n, t0) v M3)) eqn:?.
      destruct MQ; attac; unfold option_map in *; blast_cases; attac.
    - blast_cases; attac; unfold option_map in *; blast_cases; attac.
  Qed.


  Lemma measure_ms_fin_noincr : forall (MS0 MS1 : MServ) a dm0,
      (MS0 =(a)=> MS1) ->
      measure_ms_fin MS0 = Some dm0 ->
      exists dm1, measure_ms_fin MS1 = Some dm1 /\ (dm1 <= dm0)%nat.

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
      exists dm, measure_mq n p (MSend_all ws R p M) MQ = Some dm /\ (dm <= length ws)%nat.
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
    - destruct (measure_mon n p (MSend (n0, t0) v M3)) eqn:?.
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
    - destruct (measure_mon n p (MSend (n0, t0) v M3)) eqn:?.
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
      (exists dm1, measure_ms n p MS1 = Some dm1 /\ dm1 <= dm0)%nat \/ a = send (n, R) ^ p.

  Proof.
    intros.
    destruct MS0 as [MQ0 M0 S0].
    destruct MS1 as [MQ1 M1 S1].
    have (a = a).
    destruct_ma a; attac.
    all: unfold measure_ms in *.
    all: simpl in *; compat_hsimpl in *.
    all: blast_cases; attac; blast_cases; attac.
    destruct (measure_mon n p (MSend (n0, t0) v M3)) eqn:?.
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
      (exists dm1, measure_ms n1 p (MN1 n0) = Some dm1 /\ dm1 <= dm0)%nat \/
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


  Lemma measure_ms_fin_net_decr : forall (MN0 MN1 : MNet) n a dm,
      Flushing_NAct n a ->
      (MN0 =(a)=> MN1) ->
      measure_ms_fin (MN0 n) = Some (S dm) ->
      measure_ms_fin (MN1 n) = Some dm.

  Proof.
    intros.
    destruct (MN0 n) as [MQ0 M0 S0] eqn:?.
    destruct (MN1 n) as [MQ1 M1 S1] eqn:?.
    unfold NetGet in *.
    destruct a.
    - kill H.
      kill H0.
      kill H2.
      hsimpl in *.
      rewrite `(NetMod.get n MN0 = _) in *.
      eauto using measure_ms_fin_decr.
    - hsimpl in *.
      consider (_ =(_)=> _).
      kill H.
      rewrite `(NetMod.get n MN0 = _) in *.
      eapply measure_ms_fin_decr in H0; eauto with LTS.
      2: attac; blast_cases; attac.
      smash_eq n n1; compat_hsimpl in *; attac.
      blast_cases; attac.
      compat_hsimpl in *.
      unfold measure_ms_fin in *.
      eauto using measure_mq_fin_push.
  Qed.


  Lemma measure_ms_fin_net_noincr : forall (MN0 MN1 : MNet) n a dm0,
      (MN0 =(a)=> MN1) ->
      measure_ms_fin (MN0 n) = Some dm0 ->
      exists dm1, measure_ms_fin (MN1 n) = Some dm1 /\ (dm1 <= dm0)%nat.

  Proof.
    intros.
    destruct (MN0 n) as [MQ0 M0 S0] eqn:?.
    destruct (MN1 n) as [MQ1 M1 S1] eqn:?.
    unfold NetGet in *.
    destruct a.
    - kill H.
      kill H2.
      smash_eq n n0; attac.
      rewrite `(NetMod.get n MN0 = _) in *.
      eauto using measure_ms_fin_noincr.
    - hsimpl in *.
      consider (_ =(_)=> _).
      kill H1.
      smash_eq n n0; attac.
      + rewrite `(NetMod.get n MN0 = _) in *.
        eapply measure_ms_fin_noincr in H; eauto with LTS.
        hsimpl in *.
        smash_eq n n1; compat_hsimpl in *; attac.
        blast_cases; attac.
        compat_hsimpl in *.
        unfold measure_ms_fin in *.
        eauto using measure_mq_fin_push.
      + smash_eq n n1; compat_hsimpl in *; attac.
        blast_cases; attac.
        compat_hsimpl in *.
        unfold measure_ms_fin in *.
        eauto using measure_mq_fin_push.
  Qed.


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


  Lemma measure_lock_chain_split_tip : forall (MN0 : MNet) (n0 n1 m0 : Name) (L : list Name) p dm,
      NoDup L ->
      n0 <> m0 ->
      ~ In n1 L ->
      measure_lock_chain MN0 n0 L n1 p = Some (m0, n1, dm) ->
      exists L0, L = L0 ++ [m0]
               /\ ~ In m0 L0
               /\ measure_ms m0 p (MN0 n1) = Some (dm_flush dm)
               /\ measure_lock_chain MN0 n0 L0 m0 p = None
               /\ dm_pass dm = S (S (length L0)).

  Proof.
    intros.

    generalize dependent n0 m0 n1 dm.
    induction L; intros; simpl in *; hsimpl in *.
    1: { blast_cases; attac. }

    consider (NoDup (_ :: _)).

    destruct (measure_ms n0 p (MN0 a)) eqn:?; attac.
    destruct (measure_lock_chain MN0 a L n1 p) as [[[m0' m1'] dm'] | ] eqn:?; attac.
    destruct dm'; attac.

    smash_eq m0 a.
    - destruct L using rev_ind.
      {
        simpl in *.
        destruct (measure_ms m0 p (MN0 n1)) eqn:?; attac.
        exists [].
        attac.
      }
      clear IHL0.
      clear IHL.
      exfalso.
      simpl in *.
      eapply measure_lock_chain_split in Heqo0.
      hsimpl in *.
      destruct L0; kill Heqo0.
      + rewrite <- app_assoc in *.
        destruct L; attac.
      + rewrite <- app_assoc in *.
        assert (~ In m0 (L ++ [x] ++ [n1])) by (intros ?; eapply `(~ In m0 L); attac).
        rewrite <- H2 in H.
        attac.

    - eapply IHL in Heqo0; eauto.
      clear IHL.
      hsimpl in *.
      exists (a :: L0); attac.
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


  Import DetectMeasureOrder'.

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
        /\ dm1 < dm0.

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

  Lemma measure_lock_chain_pass_tip : forall (MN0 MN1 : MNet) (n0 n1 m0 : Name)
                                    (L : list Name) p dm0,
      KIC MN0 ->
      NoDup L ->
      n0 <> m0 ->
      ~ In n1 L ->
      lock_chain MN0 n0 L n1 ->
      measure_lock_chain MN0 n0 L n1 p = Some (m0, n1, dm0) ->
      (MN0 =(NComm n1 m0 R ^ p)=> MN1) ->
      origin p <> m0 ->
      exists m' dm1,
        measure_lock_chain MN1 n0 L n1 p = Some (m', m0, dm1)
        /\ dm1 < dm0.
  Proof.
    intros.
    apply measure_lock_chain_split_tip in H4; auto.
    assert (measure_ms m0 p (MN0 n1) = Some 1) by eauto using measure_ms_net_send_zero.
    hsimpl in *.

    destruct L0 using rev_ind; simpl in *.
    - destruct (measure_ms n0 p (MN0 m0)) eqn:?. 1: attac.
      eapply measure_ms_net_recv in H5; auto.
      all: attac.
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
        3: attac.
        all: auto.
        eapply NoDup_app_remove_l in H0.
        consider (NoDup (_ :: _)); attac.
      }

      eapply measure_lock_chain_decapitate with (L1:=[]) in H5; auto.
      5: eauto.
      hsimpl in *.
      all: attac.
      2: {
        clear - H0 H18 H12 H8 H2 H1.
        induction L0; attac.
        - kill H0.
          constructor; attac.
          constructor; attac.
          constructor; attac.
        - kill H0.
          constructor; attac.
          eapply IHL0 in H4; attac.
      }

      eapply measure_lock_chain_extend in H14.
      2: eauto.

      eapply measure_lock_chain_cut in H14.
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
        /\ dm1 < dm0.

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
                 dm1 < dm0)
        by attac.

      re_have eauto using measure_lock_chain_pass with LTS.
    - assert (measure_ms m0 p (MN1 m1) = Some (S n)) by eauto using measure_ms_net_decr.

      clear H8.
      assert (a = NComm m1 m0 R ^ p \/ a <> NComm m1 m0 R ^ p) as [|].
      {
        clear; destruct a; attac.
        destruct p0; attac;
          destruct (MProbe_eq_dec m p); attac;
          smash_eq n m1; smash_eq n0 m0; attac; destruct t0; attac. right; intros ?; attac.
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
        exists dm1, measure_lock_chain MN1 n0 L n1 (active_probe_of MN0 n0) = Some (n0, m1, dm1) /\ dm1 < dm0.

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


  Lemma measure_lock_chain_extends : forall MN n0 n1 n2 m0 m1 p dm L,
    measure_lock_chain MN n0 L n1 p = Some (m0, m1, dm) ->
    measure_lock_chain MN n0 (L ++ [n1]) n2 p = Some (m0, m1, dm).

  Proof.
    intros.
    generalize dependent n0 dm m0 m1.
    induction L; attac.
    - blast_cases; attac.
    - blast_cases; attac.
      eapply IHL with (n0:=a) in Heqo0.
      attac.
  Qed.


  Lemma measure_loop_decr : forall (MN0 MN1 : MNet) (n m0 m1 : Name)
                              (L : list Name) dm0 a,
      KIC MN0 ->
      NoDup L ->
      ~ In n L ->
      lock_chain MN0 n L n ->
      measure_loop MN0 n L = Some (m0, m1, dm0) ->
      Flushing_NAct m1 a ->
      alarm (MN0 n) = false ->
      (MN0 =(a)=> MN1) ->
      exists m0' m1' dm1, measure_loop MN1 n L = Some (m0', m1', dm1)
                     /\ dm1 < dm0.
  Proof.
    intros.

    unfold measure_loop in *.
    replace (active_probe_of MN1 n) with (active_probe_of MN0 n).
    2: {
      eapply deadlocked_preserve_active_probe_of1; attac.
      eapply dep_self_deadlocked; attac.
    }

    destruct (measure_ms_fin (MN0 n)) eqn:?; simpl in *.
    - exists n, n.
      hsimpl in *.
      destruct n0.
      1: {
        unfold measure_ms_fin in *.
        hsimpl in *.
        unfold option_map in *.
        exfalso.
        blast_cases; attac.
      }
      eapply measure_ms_fin_net_decr in Heqo; eauto.
      attac.
      eexists _.
      split; eauto.
      unfold dm_ltb; attac.

    - smash_eq n m0.
      + assert (0 < dm_pass dm0)%nat by (destruct L; attac; blast_cases; attac).
        eapply measure_lock_chain_finish in H3 as [|]; eauto; hsimpl in *.
        * eexists _, _, _.
          split; eauto.
          destruct dm0.
          attac.
        * destruct (measure_ms_fin (MN1 n)).
          -- eexists _, _, _.
             split; eauto.
             destruct dm0.
             attac.
          -- eexists _, _, _; eauto.

      + smash_eq n m1.
        * assert (0 < dm_pass dm0)%nat by (destruct L; attac; blast_cases; attac).
          destruct (measure_ms_fin (MN1 n)).
          1: { eexists _, _, _; attac. }

          destruct (dm_flush dm0) eqn:?.
          1: {
            eapply measure_lock_chain_split_tip in H3; eauto.
            hsimpl in *.
            rewrite `(dm_flush dm0 = _) in *.

            clear - H9.
            unfold measure_ms in *.
            destruct (measure_mon m0 (active_probe_of MN0 n) (MN0 n)) eqn:?.
            hsimpl in *.
            blast_cases; attac.
            induction (MN0 n); attac.
            induction (mserv_m0); attac.
            blast_cases; attac.
            destruct n0; attac.
          }
          destruct n0.
          -- eapply  measure_lock_chain_pass_tip in H3; eauto.
             hsimpl in *.
             eexists _, _, _.
             eauto.
             eapply measure_lock_chain_split in H3.
             hsimpl in *.
             rewrite Heqn0 in *.
             eapply measure_ms_net_send in H8; eauto.
             subst; auto.
          -- eapply measure_lock_chain_split_tip in H3; eauto.
             hsimpl in *.
             rewrite Heqn0 in *.

             eapply measure_ms_net_decr in H9; eauto.
             destruct (measure_lock_chain MN1 n L0 m0 (active_probe_of MN0 n)) as [[[m0' m1'] dm'] | ] eqn:?.
             ++ eexists _, _, _.
                split; eauto using measure_lock_chain_extends.

               apply measure_lock_chain_split in Heqo0.
               hsimpl in *.
               apply dm_ltb_pass.
               destruct dm', dm0; attac.
               clear - Heqo0.
               destruct L1. 1: attac.
               simpl in *.
               enough (length L1 < length L0)%nat by lia.
               kill Heqo0.
               generalize dependent L1 L2 m0' m1'.
               induction L0; intros; simpl in *.
               ** induction L1; attac.
               ** destruct L1. 1: attac.
                  rewrite <- app_comm_cons in H0.
                  kill H0.
                  apply IHL0 in H1.
                  simpl.
                  lia.
             ++ eexists _, _, _.
                split.
                eapply measure_lock_chain_extend; eauto.

                destruct dm0; simpl in *.
                unfold dm_ltb; attac.
        * destruct (measure_ms_fin (MN1 n)).
          2: { eauto using measure_lock_chain_flush. }
          eexists _, _, _.
          split; eauto.
          apply dm_ltb_pass.
          simpl.
          destruct L; attac; blast_cases; attac.
  Qed.


  (** ** NO INCR  *)

  Lemma Flushing_NAct_dec : forall n a,
      Flushing_NAct n a \/ ~ Flushing_NAct n a.

  Proof.
    intros.
    destruct a; attac; smash_eq n n0; attac.
    blast_cases; attac.
    blast_cases; attac.
    blast_cases; attac.
    blast_cases; attac.
  Qed.


  Lemma dm_leb_refl : forall dm, dm <= dm.
  Proof. intros. unfold dm_leb. attac. Qed.


  Lemma lock_tau_flush : forall MN0 MN1 n0 n1 a,
        KIC MN0 ->
        lock MN0 n0 n1 ->
        (MN0 =(NTau n0 a)=> MN1) ->
        Flushing_act a.

  Proof.
    intros.
    destruct_ma a; attac.
    - unfold lock, lock_set in *.
      attac.
      unfold deinstr in *.
      rewrite NetMod.get_map in *.
      destruct (NetMod.get n0 MN0); attac.
      blast_cases; attac.
      consider (serv_lock _ _).
      consider (_ =(_)=> _).
      consider (_ =(_)=> _).
      bs.
    - eapply lock_singleton in H0; attac.
      unfold lock, lock_set in *.
      attac.
      unfold deinstr in *.
      rewrite NetMod.get_map in *.
      destruct (NetMod.get n0 MN0); attac.
      blast_cases; attac.
      consider (serv_lock _ _).
      consider (_ =(_)=> _).
      consider (_ =(_)=> _); attac.
      consider (_ =(_)=> _); attac.
      destruct n.
      destruct t0.
      + specialize H3 with (n:=n).
        attac.
      + specialize H3 with (n:=n).
        attac.
        smash_eq n n1; attac.
        assert (In (n, R, v) (serv_i0 ++ retract_recv mserv_q0)) by attac.
        attac.
  Qed.

  Lemma measure_lock_chain_tau_noincr : forall MN0 MN1 n0 n1 n2 n3 L p dm m a,
        KIC MN0 ->
        lock_chain MN0 n0 L n3 ->
        (MN0 =(NTau m a)=> MN1) ->
        n2 <> m ->
        measure_lock_chain MN0 n0 L n3 p = Some (n1, n2, dm) ->
        measure_lock_chain MN1 n0 L n3 p = Some (n1, n2, dm).

  Proof.
    intros.

    generalize dependent n0 dm.
    induction L; intros; simpl in *.
    - hsimpl in *.
      unfold NetGet in *.
      smash_eq n3 m; attac.
      destruct (measure_ms n0 p (Transp.Net.NetMod.get n3 MN0)) eqn:?; attac.
    - assert (m = a0 -> Flushing_act a).
      {
        consider (exists n', lock MN0 a0 n') by (destruct L; attac).
        intros; subst; eauto using lock_tau_flush.
      }
      hsimpl in *.
      destruct (measure_ms n0 p (MN0 a0)) eqn:?; hsimpl in *.
      + unfold NetGet in *.
        smash_eq n2 m; attac.
      + destruct (measure_lock_chain MN0 a0 L n3 p) as [[[m0' m1'] [? ?]] | ] eqn:?; attac.
        eapply IHL in Heqo0; auto. clear IHL.
        rewrite Heqo0.

        unfold NetGet in *.
        smash_eq a0 m; attac.
        destruct (measure_ms n0 p &S) eqn:?; auto.
        exfalso.

        clear - Heqo1 Heqo H1 H6 H2 H4.
        destruct_ma a; compat_hsimpl in *; attac.
        all: rewrite `(NetMod.get _ _ = _) in *.
        all: unfold measure_ms in *; simpl in *.
        all: blast_cases; attac.
        destruct (measure_mon n0 p (MSend (n1, t0) v M1)) eqn:?.
        attac. blast_cases; attac.
  Qed.


  Lemma measure_lock_chain_comm_noincr : forall MN0 MN1 n0 n1 n2 n3 L p tag v dm0 m0 m1,
      KIC MN0 ->
      lock_chain MN0 n0 L n3 ->
      (MN0 =(NComm m1 m0 tag v)=> MN1) ->
      n2 <> m1 ->
      ~ In n0 L ->
      ~ In n3 L ->
      NoDup L ->
      measure_lock_chain MN0 n0 L n3 p = Some (n1, n2, dm0) ->
      exists m0' m1' dm1, measure_lock_chain MN1 n0 L n3 p = Some (m0', m1', dm1) /\ dm1 <= dm0.

  Proof.
    intros.

    generalize dependent n0 dm0.
    induction L; intros; simpl in *.
    - eexists n1, n2, dm0. split; eauto using dm_leb_refl.
      hsimpl in *.
      unfold NetGet in *.
      destruct (measure_ms n0 p (Transp.Net.NetMod.get n3 MN0)) eqn:?; attac.
      smash_eq n2 m0.
      2: {
        replace (NetMod.get n2 MN1) with (NetMod.get n2 MN0) by eauto using NComm_neq_stay.
        now rewrite Heqo.
      }
      hsimpl in *.
      destruct v; attac.
      + unfold measure_ms in *; simpl in *; hsimpl in *.
        eapply measure_mq_push in Heqo. now erewrite Heqo.
      + unfold measure_ms in *; simpl in *; hsimpl in *.
        compat_hsimpl in *.
        rewrite `(NetMod.get n2 _ = _) in *.
        simpl in *.
        eapply measure_mq_push in Heqo. now erewrite Heqo.
    - hsimpl in *.
      destruct (measure_ms n0 p (MN0 a)) eqn:?; hsimpl in *.
      + eexists n1, n2, _. split; eauto using dm_leb_refl.
        unfold NetGet in *.
        smash_eq n2 m0.
        2: {
          replace (NetMod.get n2 MN1) with (NetMod.get n2 MN0) by eauto using NComm_neq_stay.
          now rewrite Heqo.
        }
        destruct (measure_ms n1 p (Transp.Net.NetMod.get n2 MN1)) eqn:?.
        1: {
          enough (n = n0) by attac.
          consider (_ =(_)=> _).
          destruct v; attac.
          all: compat_hsimpl in *.
          all: try (rewrite `(NetMod.get n2 _ = _) in * ).
          - unfold measure_ms in *.
            simpl in *.
            eapply measure_mq_push in Heqo.
            rewrite Heqo0 in Heqo; attac.
          - unfold measure_ms in *.
            simpl in *.
            eapply measure_mq_push in Heqo.
            rewrite Heqo0 in Heqo; attac.
        }
        exfalso.
        clear IHL.
        consider (_ =(_)=> _); destruct v; compat_hsimpl in *.
        all: try (rewrite `(NetMod.get n2 _ = _) in * ).
        all: unfold measure_ms in *; simpl in *.
        all: eapply measure_mq_push in Heqo.
        all: rewrite Heqo0 in Heqo; attac.

      + consider (NoDup (_ :: _)).
        unfold NetGet in *.

        destruct (measure_lock_chain MN0 a L n3 p) as [[[m0' m1'] [? ?]] | ] eqn:?; attac.

        destruct dm_pass0.
        1: {
          clear - Heqo0. destruct L; attac; blast_cases; attac.
        }
        eapply IHL in Heqo0 as ?; auto. clear IHL.
        hsimpl in *.

        destruct (measure_ms n0 p (NetMod.get a MN1)) eqn:?; attac.
  Qed.

  Lemma measure_loop_noincr : forall (MN0 MN1 : MNet) (n m0 m1 : Name)
                                (L : list Name) dm0 a,
      KIC MN0 ->
      NoDup L ->
      ~ In n L ->
      lock_chain MN0 n L n ->
      measure_loop MN0 n L = Some (m0, m1, dm0) ->
      alarm (MN0 n) = false ->
      (MN0 =(a)=> MN1) ->
      exists m0' m1' dm1, measure_loop MN1 n L = Some (m0', m1', dm1)
                     /\ dm1 <= dm0.

  Proof.
    intros.
    destruct (Flushing_NAct_dec m1 a) as [|].
    1: {
      consider (exists m0' m1' dm1,
            measure_loop MN1 n L = Some (m0', m1', dm1)
            /\ dm1 < dm0) by eauto using measure_loop_decr.
      exists m0', m1', dm1.
      split; eauto.
      unfold dm_ltb, dm_leb in *.
      destruct dm0, dm1; attac.
      destruct (dm_pass1 =? dm_pass0) eqn:?; auto.
      - destruct (dm_flush1 =? dm_flush0) eqn:?; auto.
        rewrite PeanoNat.Nat.ltb_lt in *.
        rewrite PeanoNat.Nat.leb_le in *.
        lia.
      - rewrite PeanoNat.Nat.ltb_lt in *.
        rewrite PeanoNat.Nat.leb_le in *.
        lia.
    }

    unfold measure_loop in *.
    replace (active_probe_of MN1 n) with (active_probe_of MN0 n).
    2: {
      eapply deadlocked_preserve_active_probe_of1; attac.
      eapply dep_self_deadlocked; attac.
    }

    destruct (measure_ms_fin (MN0 n)) eqn:?.
    {
      eapply measure_ms_fin_net_noincr in Heqo; eauto.
      attac.
      eexists _, _, _; unfold dm_leb; attac.
      destruct (dm1 =? n0); auto.
      now apply PeanoNat.Nat.leb_le.
    }

    destruct (measure_ms_fin (MN1 n)) eqn:?.
    {
      eexists _, _, _; split; eauto.
      destruct (dm_pass dm0) eqn:?.
      - exfalso.
        destruct dm0; attac.
        destruct L; attac; blast_cases; attac.
      - unfold dm_leb; attac.
    }

    destruct a; simpl in *.
    2: eauto using measure_lock_chain_comm_noincr.

    smash_eq n0 m1.
    2: eapply measure_lock_chain_tau_noincr in H3; eauto using dm_leb_refl with LTS.

    consider (exists m', lock MN0 n0 m').
    {
      eapply measure_lock_chain_in_r in H3 as [|]; attac.
      - destruct L; attac.
      - apply in_split in H3; attac.
        destruct l2; attac.
    }
    assert (Flushing_act m) by eauto using lock_tau_flush.

    exfalso.

    eapply H6.
    attac.
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
      + destruct a; attac; blast_cases; attac.
        rewrite next_state_Send_all; attac.
      + destruct a; attac; blast_cases; attac.
        rewrite next_state_Send_all; attac.
      + destruct a; attac; blast_cases; attac.
        rewrite next_state_Send_all; attac.
      + exists (S (add dmm' dmf)).
        destruct (MQ ++ [MqRecv (n, Q) v]); doubt.
        unfold option_map in *; attac.
        clear - H6; blast_cases; attac.
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
      + destruct a; attac; blast_cases; attac.
        unfold andb in *;  blast_cases; attac.
        rewrite next_state_Send_all; attac.
      + destruct a; attac; blast_cases; attac.
        unfold andb in *;  blast_cases; attac.
        rewrite next_state_Send_all; attac.
      + destruct a; attac; blast_cases; attac.
        rewrite next_state_Send_all; attac.
      + exists (S (add dmm' dmf)).
        destruct (MQ ++ [MqProbe (n', R) p]); doubt.
        unfold option_map in *; attac.
        clear - H6; blast_cases; attac.
    - eattac.
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

  Lemma measure_lock_chain_tip_add : forall (MN : MNet) n0 L n1 n2 p dmm,
      measure_ms n1 p (MN n2) = Some dmm ->
      exists m0 m1 dm, measure_lock_chain MN n0 (L ++ [n1]) n2 p = Some (m0, m1, dm).

  Proof.
    intros.
    generalize dependent n0.
    induction L; attac.
    - unfold measure_ms in *.
      blast_cases; attac.
    - blast_cases; attac.
      specialize (IHL a).
      attac.
  Qed.

  Lemma measure_lock_chain_mid_add : forall (MN : MNet) n0 L0 n1 n2 L1 n3 p dmm,
      measure_ms n1 p (MN n2) = Some dmm ->
      exists m0 m1 dm, measure_lock_chain MN n0 (L0 ++ n1::n2::L1) n3 p = Some (m0, m1, dm).

  Proof.
    intros.
    generalize dependent L1 n0 n1 n2.
    induction L0; attac.
    - unfold measure_ms in *.
      blast_cases; attac.
    - blast_cases; attac.
      eapply IHL0 in H.
      eattac.
  Qed.


  Lemma measure_ac : forall (MN0 : MNet) (n : Name) (L : list Name),
      (KIC MN0) ->
      (lock_chain '' MN0 n L n) ->
      alarm_condition n MN0 ->
      exists m0 m1 dm, measure_loop MN0 n L = Some (m0, m1, dm).

  Proof.
    intros.
    kill H1.
    - unfold measure_loop, NetGet, measure_ms_fin in *.
      destruct (NetMod.get n MN0); simpl in *.
      destruct (measure_mon_fin mserv_m0) eqn:?.
      compat_hsimpl.
      eauto.
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

        apply measure_sp_true in H4.
        hsimpl in *.
        apply lock_chain_split_in with (n1:=m) in H0; eauto.
        hsimpl in *.

        destruct L1; hsimpl in *.
        * consider (m' = n) by (eapply SRPC_lock_set_uniq; eauto with LTS).
          eauto using measure_lock_chain_tip_add.
        * consider (m' = n0) by (eapply SRPC_lock_set_uniq; eauto with LTS).
          eauto using measure_lock_chain_mid_add.
    - unfold measure_loop, measure_ms_fin, active_ev_of, active_probe_of in *.
      apply in_split in H3 as (MQ & MQ' & ?).
      rewrite H1.

      assert (locked (MN0 n) = Some n') by attac.
      assert (NoRecvR_from n' (mserv_q (MN0 n))) by eauto using lock_NoRecvR_from.
      assert (no_sends_in n MN0) by eauto using lock_M_no_sends_in.
      clear H0 H2.

      assert (self (MN0 n) = n) by attac.
      destruct (alarm (MN0 n)) eqn:?.
      1: { compat_hsimpl; eauto. }

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
          by (clear - H4 H3 H5 H6; unfold NoRecvR_from in *; destruct a; simpl; blast_cases; attac; try (specialize H4 with v); try (rewrite next_state_Send_all); attac).

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
          destruct `(_ \/ _); attac.
        }
        specialize (IHMQ ltac:(auto)).
        destruct (MQ ++ [MqProbe (n', R) {| origin := self mserv_m0; lock_id := lock_count mserv_m0 |}]) eqn:?; doubt.
        setoid_rewrite Heql in Heqo.
        setoid_rewrite Heql in IHMQ.
        clear H4.
        blast_cases; attac.
        blast_cases; attac.
        blast_cases; attac.
        blast_cases; attac.
  Qed.

  Lemma measure_ms_fin_get_flush : forall MS0 dmm,
      measure_ms_fin MS0 = Some dmm ->
      alarm MS0 = true \/ (exists a MS1, Flushing_act a /\ (MS0 =(a)=> MS1)).

  Proof.
    intros.
    destruct MS0 as [MQ0 M0 [I0 P0 O0]].
    destruct dmm.
    1: {
      unfold measure_ms_fin in *.
      simpl in *.
      generalize dependent M0.
      induction MQ0; attac; induction M0; attac; unfold option_map in *; blast_cases; attac.
    }

    right.
    unfold measure_ms_fin in *; simpl in *.
    destruct M0; attac; blast_cases; attac.
    - destruct MQ0; attac; blast_cases; attac.
      unfold option_map in *; blast_cases; attac.
      destruct e; attac.
      + eexists (MActT (Send n v)), _; attac.
      + eexists (MActP (Recv n v)), _; attac.
      + eexists (MActM Tau), _; attac.
    - eexists (MActM (Send to msg)), _; attac.
  Qed.

  Lemma measure_ms_get_flush : forall n p MS0 dmm,
      measure_ms n p MS0 = Some dmm ->
      exists a MS1, Flushing_act a /\ (MS0 =(a)=> MS1).

  Proof.
    intros.
    destruct MS0 as [MQ0 M0 [I0 P0 O0]].
    destruct dmm.
    1: {
      unfold measure_ms in *.
      simpl in *.
      generalize dependent M0.
      induction MQ0; attac; induction M0; attac; unfold option_map in *; blast_cases; attac.
    }

    unfold measure_ms in *; simpl in *.
    destruct M0; attac; blast_cases; attac.
    - destruct MQ0; attac; blast_cases; attac.
      unfold option_map in *; blast_cases; attac.
      destruct e; attac.
      + eexists (MActT (Send n0 v)), _; attac.
      + eexists (MActP (Recv n0 v)), _; attac.
      + eexists (MActM Tau), _; attac.
    - eexists (MActM (Send to msg)), _; attac.
  Qed.


  Lemma lift_Flushing_act : forall (MN0 : MNet) n a MS1,
      (MN0 n =(a)=> MS1) ->
      Flushing_act a ->
      exists na MN1,
        Flushing_NAct n na /\ (MN0 =(na)=> MN1).

  Proof.
    intros.
    unfold NetGet in *.
    destruct (NetMod.get n MN0) as [MQ0 M0 S0] eqn:?.
    destruct_ma a; consider (_ =(_)=> _); compat_hsimpl in *; attac.
    - eexists (NTau n _), _.
      split.
      2: econstructor.
      3: econstructor.
      3: rewrite Heqm. 3: eapply (MTRecvP); attac.
      all: eattac.
    - smash_eq n n0.
      + eexists (NComm n n t0 # v), _.
        attac; econstructor; eattac. rewrite Heqm; eattac. eattac. compat_hsimpl; eattac.
      + destruct (NetMod.get n0 MN0) eqn:?.
        eexists (NComm n n0 t0 # v), _.
        attac; econstructor; eattac. rewrite Heqm; eattac. compat_hsimpl; eattac.
    - smash_eq n n0.
      + eexists (NComm n n t0 ^ v), _.
        attac; econstructor; eattac. rewrite Heqm; eattac. eattac. compat_hsimpl; eattac.
      + destruct (NetMod.get n0 MN0) eqn:?.
        eexists (NComm n n0 t0 ^ v), _.
        attac; econstructor; eattac. rewrite Heqm; eattac. compat_hsimpl; eattac.
    - eexists (NTau n _), _.
      split.
      2: econstructor.
      3: econstructor.
      3: rewrite Heqm. 3: eapply (MTPickM); attac.
      all: eattac.
  Qed.

  Lemma measure_lock_chain_get_flush : forall n0 L n1 p MN0 dm m0 m1,
      measure_lock_chain MN0 n0 L n1 p = Some (m0, m1, dm) ->
      exists a MN1, Flushing_NAct m1 a /\ (MN0 =(a)=> MN1).

  Proof.
    intros.

    generalize dependent dm n0.
    induction L; intros; simpl in *.
    - destruct (measure_ms n0 p (MN0 n1)) eqn:?; attac.
      eapply measure_ms_get_flush in Heqo; eauto.
      hsimpl in *.
      eauto using lift_Flushing_act.
    - destruct (measure_ms n0 p (MN0 a)) eqn:?; attac.
      + eapply measure_ms_get_flush in Heqo; eauto.
        hsimpl in *.
        eauto using lift_Flushing_act.
      + destruct (measure_lock_chain MN0 a L n1 p) as [[[m0' m1'] dm'] | ] eqn:?; attac.
        destruct dm'; attac.
  Qed.


  Lemma measure_loop_get_flush : forall n L MN0 dm m0 m1,
      measure_loop MN0 n L = Some (m0, m1, dm) ->
      alarm (MN0 n) = true \/ exists a MN1, Flushing_NAct m1 a /\ (MN0 =(a)=> MN1).

  Proof.
    intros.
    destruct (alarm (MN0 n)) eqn:?; eauto.
    right.

    unfold measure_loop in *; attac.
    blast_cases.
    - eapply measure_ms_fin_get_flush in Heqo; eattac.
      eauto using lift_Flushing_act.
    - eapply measure_lock_chain_get_flush in H; eattac.
  Qed.

  Lemma flush_irrefutable : forall MN0 MN1 MN1' (af a : MNAct) n,
      Flushing_NAct n af ->
      (MN0 =(af)=> MN1) ->
      (MN0 =(a)=> MN1') ->
      a <> af ->
      exists MN2, MN1' =(af)=> MN2.

  Proof.
    intros.
    destruct af; consider (Flushing_NAct _ _).
    - destruct a.
      + smash_eq n n0.
        *
          destruct m, m0; attac.
          all: blast_cases; attac.
          all: consider (MN0 =(_)=> _); consider (MN0 =(_)=> _).
          all: attac.
          all: consider (NetMod.get n MN0 =(_)=> _); consider (MN0 =(_)=> _).
          all: attac.
          all: rewrite `(NetMod.get n _ = _) in *.
          all: compat_hsimpl in *; attac.
          eexists. econstructor. eattac. eattac. compat_hsimpl. econstructor; eattac.
          destruct S1. eexists. econstructor. eattac. econstructor.
          compat_hsimpl. econstructor. eattac. econstructor.
          eexists. econstructor. eattac. eattac. compat_hsimpl. econstructor; eattac.
          eexists. econstructor. eattac. eattac. compat_hsimpl. econstructor; eattac.

        * assert (NetMod.get n MN0 = NetMod.get n MN1') by eauto using NTau_neq_stay.
          exists (NetMod.put n (NetMod.get n MN1) MN1').
          constructor. attac.
          constructor. eattac.
          rewrite <- H3.
          attac.
          kill H0.
          attac.
      + smash_eq n n0.
        * destruct m; attac.
          all: blast_cases; attac.
          all: consider (MN0 =(_)=> _); consider (MN0 =(_)=> _).
          all: attac.
          all: consider (NetMod.get n MN0 =(_)=> _); consider (MN0 =(_)=> _).
          all: attac.
          all: rewrite `(NetMod.get n _ = _) in *.
          all: destruct p; attac.
          smash_eq n n1; attac; compat_hsimpl in *; bs.
        * destruct m; attac.
          all: blast_cases; attac.
          all: consider (MN0 =(_)=> _); compat_hsimpl in *; consider (MN0 =(_)=> _).
          all: destruct p; compat_hsimpl in *.
          -- smash_eq n0 n1; compat_hsimpl in *.
             eexists; econstructor; eattac.
             smash_eq n n0; compat_hsimpl in *; attac.
             smash_eq n n1; compat_hsimpl in *; attac.
             ++ eexists; econstructor; eattac.
                compat_hsimpl.
                econstructor; eattac.
             ++ eexists; constructor; compat_hsimpl; auto.
                constructor; compat_hsimpl.
                eapply MTRecvP; attac.
          -- smash_eq n0 n1; compat_hsimpl in *.
             eexists; econstructor; eattac.
             smash_eq n n0; compat_hsimpl in *; attac.
             smash_eq n n1; compat_hsimpl in *; attac.
             ++ eexists.
                econstructor; attac.
                compat_hsimpl.
                econstructor; attac.
             ++ eexists.
                econstructor; attac.
                compat_hsimpl.
                econstructor; attac.
          -- smash_eq n0 n1; compat_hsimpl in *.
             eexists; econstructor; eattac.
             smash_eq n n0; compat_hsimpl in *; attac.
             smash_eq n n1; compat_hsimpl in *; attac.
             ++ eexists.
                econstructor; attac.
                compat_hsimpl.
                econstructor; attac.
             ++ eexists.
                econstructor; attac.
                compat_hsimpl.
                econstructor; attac.
          -- smash_eq n0 n1; compat_hsimpl in *.
             eexists; econstructor; eattac.
             smash_eq n n0; compat_hsimpl in *; attac.
             smash_eq n n1; compat_hsimpl in *; attac.
             ++ eexists.
                econstructor; attac.
                compat_hsimpl.
                econstructor; attac.
             ++ eexists.
                econstructor; attac.
                compat_hsimpl.
                econstructor; attac.
    - destruct a; compat_hsimpl in *;
        consider (MN0 =(_)=> _); consider (MN0 =(NComm _ _ _ _)=> _).
      + compat_hsimpl in *.
        smash_eq n n1; attac.
        * all: destruct m.
          all: try (destruct p).
          all: try (destruct a).
          all: smash_eq n n0; compat_hsimpl in *.
          all: try (rewrite `(NetMod.get n MN0 = _) in * ).
          all: try (destruct p0).
          all: compat_hsimpl in *.
          all: eexists; eapply NComm_eq.
          all: try (rewrite NetMod.get_put_eq by auto).
          all: try (rewrite NetMod.get_put_neq by auto).
          all: try (econstructor; eattac).
          all: try (rewrite `(NetMod.get n MN0 = _) in * ).
          all: compat_hsimpl in *.
          all: eattac.
        * destruct m; eattac.
          all: try (destruct p).
          all: try (destruct a).
          all: smash_eq n1 n0; compat_hsimpl in *.
          all: try (smash_eq n n0); compat_hsimpl in *.
          all: try (destruct p0).
          all: compat_hsimpl in *.
          all: eexists; eapply NComm_neq; eauto using eq_sym.
          all: try (rewrite NetMod.get_put_eq by auto).
          all: try (rewrite NetMod.get_put_neq by auto using eq_sym).
          all: try (rewrite `(NetMod.get n MN0 = _) in * ).
          all: try (rewrite `(NetMod.get n0 MN0 = _) in * ).
          all: try (rewrite `(NetMod.get n1 MN0 = _) in * ).
          all: try (econstructor; eattac).
          all: bs.
      + smash_eq n n1.
        * smash_eq n n0; smash_eq n n2; compat_hsimpl in *.
          all: destruct p, p0; attac.
          all: compat_hsimpl in *.
          all: doubt.
          all: eexists; eapply NComm_eq.
          all: repeat (rewrite NetMod.get_put_eq by auto).
          all: repeat (rewrite NetMod.get_put_neq by auto using eq_sym).
          all: try (rewrite `(NetMod.get n MN0 = _) in * ).
          all: try (rewrite `(NetMod.get n0 MN0 = _) in * ).
          all: try (rewrite `(NetMod.get n1 MN0 = _) in * ).
          all: try (rewrite `(NetMod.get n2 MN0 = _) in * ).
          all: eattac.
        * smash_eq n n0 n1 n2; compat_hsimpl in *.
          all: destruct p, p0; attac.
          all: compat_hsimpl in *.
          all: doubt.
          all: eexists; eapply NComm_neq; eauto using eq_sym.
          all: repeat (rewrite NetMod.get_put_eq in * by auto).
          all: repeat (rewrite NetMod.get_put_neq in * by auto using eq_sym).
          all: try (rewrite `(NetMod.get n MN0 = _) in * ).
          all: try (rewrite `(NetMod.get n0 MN0 = _) in * ).
          all: try (rewrite `(NetMod.get n1 MN0 = _) in * ).
          all: try (rewrite `(NetMod.get n2 MN0 = _) in * ).
          all: eattac.
          all: repeat (rewrite NetMod.get_put_eq by auto).
          all: repeat (rewrite NetMod.get_put_neq by auto using eq_sym).
          all: eattac.
          Unshelve. all: doubt. all: attac.
  Qed.


  Inductive Measures (MN : MNet) (n : Name) : DetectMeasure -> Prop :=
  | Measures_ : forall m0 m1 dm L, lock_chain MN n L n ->
                           NoDup L -> ~ In n L ->
                           measure_loop MN n L = Some (m0, m1, dm) ->
                           Measures MN n dm.

  Lemma measures_deadlock : forall MN DS,
      KIC MN ->
      dead_set DS MN ->
      exists n dm, In n DS /\ Measures MN n dm.
  Proof.
    intros.

    consider (exists n0, In n0 DS /\ trans_lock MN n0 n0) by (consider (KIC _); eapply dead_set_cycle; eauto with LTS).
    consider (exists n, trans_lock '' MN n0 n /\ alarm_condition n MN) by (consider (KIC _)).

    consider (exists L', lock_chain MN n0 L' n /\ ~ In n L') by eauto using dep_lock_chain with LTS.
    consider (exists L', lock_chain MN n0 L' n0 /\ ~ In n0 L') by eauto using dep_lock_chain with LTS.
    consider (exists L', lock_chain MN n L' n) by eauto using lock_chain_reloop with LTS.
    consider (exists L : Names, lock_chain MN n L n /\ NoDup L /\ ~ In n L /\ ~ In n L) by eauto using lock_chain_dedup with LTS.

    consider (exists m0 m1 dm, measure_loop MN n L = Some (m0, m1, dm)) by eauto using measure_ac.
    exists n, dm.
    split.
    - now eauto using dead_set_dep_in.
    - now constructor 1 with (m0:=m0)(m1:=m1)(L:=L).
  Qed.


  Lemma measures_end : forall MN n,
      Measures MN n dm_zero ->
      alarm (MN n) = true.

  Proof.
    intros.
    consider (Measures _ _ _).
    eauto using measure_loop_end.
  Qed.

  Lemma measures_noincr : forall MN0 MN1 n a dm0,
      KIC MN0 ->
      (MN0 =(a)=> MN1) ->
      Measures MN0 n dm0 ->
      exists dm1, Measures MN1 n dm1 /\ dm1 <= dm0.

  Proof.
    intros.
    consider (Measures _ _ _).

    assert (lock_chain MN1 n L n).
    {
      enough (deadlocked n MN0).
      {
        destruct (MNAct_to_PNAct a) eqn:?.
        - assert ('' MN0 =(p)=> '' MN1) by eauto using deinstr_act_do.
          eauto using deadlocked_lock_chain_invariant1.
        - replace (deinstr MN1) with (deinstr MN0); eauto using deinstr_act_skip with LTS.
      }

      eauto using dep_self_deadlocked with LTS.
    }

    destruct (alarm (MN0 n)) eqn:?.
    - assert (alarm (MN1 n) = true) by eauto using net_preserve_alarm.
      exists dm_zero.
      split.
      2: { unfold dm_zero, dm_leb; attac; blast_cases; attac. }
      econstructor 1 with (m0:=n)(m1:=n); eauto.
      unfold measure_loop, measure_ms_fin.
      rewrite unfold_measure_mq_fin_alarm; attac.

    - consider (exists m0' m1' dm1, measure_loop MN1 n L = Some (m0', m1', dm1) /\ dm1 <= dm0) by eauto using measure_loop_noincr.
      exists dm1.

      split; auto.
      constructor 1 with (m0:=m0')(m1:=m1')(L:=L); auto.
  Qed.


  Lemma measures_decr : forall MN0 n dm0,
      KIC MN0 ->
      Measures MN0 n dm0 ->
      alarm (MN0 n) = true
      \/ exists m a MN1 dm1,
          (MN0 =(a)=> MN1)
          /\ Flushing_NAct m a
          /\ Measures MN1 n dm1
          /\ dm1 < dm0.

  Proof.
    intros.
    consider (Measures _ _ _).

    assert (measure_loop MN0 n L = Some (m0, m1, dm0)) by assumption.
    eapply measure_loop_get_flush in H0 as [|]; eauto.
    hsimpl in *.

    assert (lock_chain MN1 n L n).
    {
      enough (deadlocked n MN0).
      {
        destruct (MNAct_to_PNAct a) eqn:?.
        - assert ('' MN0 =(p)=> '' MN1) by eauto using deinstr_act_do.
          eauto using deadlocked_lock_chain_invariant1.
        - replace (deinstr MN1) with (deinstr MN0); eauto using deinstr_act_skip with LTS.
      }

      eauto using dep_self_deadlocked with LTS.
    }

    destruct (alarm (MN0 n)) eqn:?; eauto.
    right.
    exists m1, a, MN1; intros.

    consider (exists m0' m1' dm1, measure_loop MN1 n L = Some (m0', m1', dm1) /\ dm_ltb dm1 dm0 = true) by eauto using measure_loop_decr.

    exists dm1.

    repeat split; auto.
    constructor 1 with (m0:=m0')(m1:=m1')(L:=L); auto.
  Qed.

End COMPL_STRONG_F.
