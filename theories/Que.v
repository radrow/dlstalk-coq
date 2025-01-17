Require Import Coq.Program.Equality.

From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Bool.
From Coq Require Import Structures.Equalities.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Std.

From Ltac2 Require Fresh.
From Ltac2 Require Import Control.
From Ltac2 Require Import Message.
From Ltac2 Require Import Std.
From Ltac2 Require Import Printf.
Import Ltac2.Notations.

Import ListNotations.
Import BoolNotations.

Require Import DlStalk.LTS.
Require Import DlStalk.Tactics.
Require Import DlStalk.ModelData.


(** No clue why I have to prove this *)
Lemma app_id : forall [A] (l0 l1 : list A), l0 ++ l1 = l1 -> l0 = [].
  intros.
  rewrite <- app_nil_l in H.
  apply app_inv_tail in H.
  assumption.
Qed.


Lemma app_self_l [A] (l0 l1 : list A) : (l0 = l0 ++ l1) <-> l1 = [].
  split; intros.
  - induction l0; auto.
    kill H; auto.
  - attac.
Qed.
Lemma app_self_r [A] (l0 l1 : list A) : (l0 = l1 ++ l0) <-> l1 = [].
  split; intros.
  - ltac1:(generalize dependent l1).
    induction l0; auto; intros.
    1: rewrite app_nil_r in *; auto.

    destruct l1; auto.
    simpl in H.
    kill H.

    assert (l1 ++ a0 :: l0 = ((l1 ++ [a0]) ++ l0)) by attac.
    rewrite H in *.

    apply IHl0 in H1.
    bullshit.
  - attac.
Qed.

Lemma app_self_l' [A] (l0 l1 : list A) : (l0 ++ l1 = l0) <-> l1 = [].
Proof.
  split; intros.
  - apply eq_sym in H.
    eapply app_self_l; eauto.
  - attac.
Qed.
Lemma app_self_r' [A] (l0 l1 : list A) : (l1 ++ l0 = l0) <-> l1 = [].
Proof.
  split; intros.
  - apply eq_sym in H.
    eapply app_self_r; eauto.
  - attac.
Qed.

Lemma app_inv_l [A] (l0 l1 l2 : list A) : (l0 ++ l2 = l1 ++ l2) <-> l0 = l1.
Proof.
  split; intros.
  - generalize dependent l0 l1.
    induction l2; intros; simpl in *; try (rewrite app_nil_r in * ); attac.

    replace (a :: l2) with ([a] ++ l2) in H by auto.
    repeat (rewrite app_assoc in H).
    apply IHl2 in H.
    clear IHl2 l2.
    generalize dependent l0.
    induction l1; intros.
    + destruct l0; attac.
    + destruct l0. attac.
      kill H.
      f_equal.
      auto.
  - attac.
Qed.
Lemma app_inv_r [A] (l0 l1 l2 : list A) : (l0 ++ l1 = l0 ++ l2) <-> l1 = l2.
Proof.
  split; intros.
  - generalize dependent l1 l2.
    induction l0; intros; simpl in *; attac.
  - attac.
Qed.

Lemma cons_self_l [A] (l0 : list A) (a : A) : (l0 = a :: l0) <-> False.
Proof.
  split; intros; attac.
  induction l0.
  - attac.
  - attac.
Qed.
Lemma cons_self_r [A] (l0 : list A) (a : A) : (a :: l0 = l0) <-> False.
Proof.
  split; intros; attac.
  induction l0; attac.
Qed.

Hint Resolve cons_self_l cons_self_r : bullshit.


Lemma nodup_one : forall [A] (l : list A),
    NoDup l ->
    List.length l = 1%nat ->
    exists n, l = [n].

Proof.
  intros.
  destruct l > [|destruct l]; simpl in *; try (bullshit).
  eauto.
Qed.


Lemma all_same_nodup_one : forall [T] [a l] (eq_dec : forall x0 x1 : T, {x0=x1}+{x0<>x1}),
    Forall (eq a) l ->
    nodup eq_dec l = [a] \/ l = [].

Proof.
  intros.
  destruct l.
  right; auto.

  left.
  simpl.
  hsimpl.
  kill H.
  induction l; auto.
  kill H1; subst.
  apply IHl in H0.
  unfold nodup.
  destruct (in_dec eq_dec a (a::l)); try (bullshit).
  auto.
Qed.


Lemma nodup_nil_inv [T : Type] : forall (H : forall x y : T, {x = y} + {x <> y}) l, nodup H l = [] <-> l = [].
Proof.
  split; intros.
  - induction l; attac.
    kill H0.
    destruct (in_dec H a l); attac.
    assert (l = []) by auto.
    attac.
  - induction l; attac.
Qed.


Lemma nodup_one_all_same : forall T a l (eq_dec : forall x0 x1 : T, {x0=x1}+{x0<>x1}),
    nodup eq_dec l = [a] ->
    Forall (eq a) l.

Proof.
  intros.
  induction l; simpl in *; try (bullshit).

  destruct (eq_dec a a0); subst.
  - constructor; auto.
    destruct (in_dec eq_dec a0 l); auto.
    kill H.
    assert (l = []) by (eapply nodup_nil_inv; attac).
    subst.
    constructor.
  - destruct (in_dec eq_dec a0 l); auto.
    + specialize (IHl H); clear H H0.
      enough (a = a0) by bullshit.
      specialize (Forall_forall (eq a) l) as [H _].
      apply H; auto.
    + kill H.
Qed.

Module Type QUE(Import ModelData : PROC_DATA).
  #[export] Hint Rewrite -> app_self_l app_self_r app_self_l' app_self_r' using assumption : LTS LTS_concl.

  #[export] Hint Rewrite -> length_app using (solve [auto with datatypes; lia]) : LTS LTS_concl.
  #[export] Hint Rewrite -> app_nil_l app_nil_r using assumption : LTS LTS_concl.
  #[export] Hint Rewrite -> Forall_app Forall_cons_iff using assumption : LTS LTS_concl.
  #[export] Hint Rewrite -> in_app_or using assumption : LTS LTS_concl.

  #[export] Hint Constructors Forall : LTS.


  Notation Que E := (list (NChan * E)).


  Inductive QAct (E : Set) :=
  | QEnq (n : NChan) (e : E) : QAct E
  | QDeq (n : NChan) (e : E) : QAct E
  .
  #[export] Hint Constructors QAct : LTS.

  Arguments QEnq [E].
  Arguments QDeq [E].


  Inductive QTrans {E : Set} : QAct E -> Que E -> Que E -> Prop :=
  | QPush (n : NChan) (e : E) (Q : Que E)
    : QTrans (QEnq n e) Q (Q ++ [(n, e)])
  | QPop (n : NChan) (e : E) (Q : Que E)
    : QTrans (QDeq n e) ((n, e)::Q) Q
  | QSeek (n : NChan) (e : E) {n' : NChan} {e' : E}
      (Q0 Q1 : Que E)
      (HSkip : n <> n')
      (HSeek : QTrans (QDeq n e) Q0 Q1)
    : QTrans (QDeq n e) ((n', e')::Q0) ((n', e')::Q1)
  .
  #[export] Hint Constructors QTrans : LTS.


  #[export] Instance trans_que {E : Set} : LTS (QAct E) (Que E) :=
    {
      trans := QTrans
    }.

  #[export] Hint Unfold trans_que : LTS.
  #[export] Hint Transparent trans_que : LTS.


  Notation Enq n v Q0 Q1 := (QTrans (QEnq n v) Q0 Q1).
  Notation Deq n v Q0 Q1 := (QTrans (QDeq n v) Q0 Q1).


  (** Enq inversion for rewriting *)
  Lemma Enq_inv [E : Set] : forall n (v : E) Q0 Q1, Enq n v Q0 Q1 <-> Q1 = (Q0 ++ [(n, v)]).
  Proof.
    split; intros; eattac.
  Qed.

  #[export] Hint Rewrite -> @Enq_inv using assumption : LTS.
  #[export] Hint Resolve <- Enq_inv : LTS.


  (** Enque does not leave empty *)
  Fact Enq_nil : forall [E : Set] [n] [v : E] [Q], ~ Enq n v Q [].

  Proof.
    unfold not; intros.
    destruct Q; inversion H.
  Qed.

  #[export] Hint Resolve Enq_nil : LTS.


  (** No deques from empty *)
  Fact Deq_nil : forall [E : Set] [n] [v : E] [Q], ~ Deq n v [] Q.

  Proof.
    unfold not; intros E n v Q H.
    inversion H.
  Qed.

  #[export] Hint Resolve Deq_nil : LTS bullshit.


  (** Decidability of arbitrary deque *)
  Lemma Deq_dec' : forall [E : Set] Q n,
      (exists (v : E) Q', Deq n v Q Q') \/ (forall v Q', ~ Deq n v Q Q').

  Proof with eattac.
    induction Q; intros...

    destruct a.
    destruct n.
    destruct n0.

    destruct (NChan_eq_dec (n, t) (n0, t0)). 1: attac.
    specialize (IHQ (n, t)).
    destruct IHQ.
    + destruct H as [v [Q' H]].
      left.
      exists v, ((n0, t0, e)::Q')...

    + right; repeat (intros ?).
      consider (Deq _ _ _ _)...
  Qed.


  (** Decidability of concrete deque *)
  Lemma Deq_dec : forall [E : Set], (forall e0 e1 : E, {e0 = e1} + {e0 <> e1}) ->
                         forall Q n (v : E),
                           (exists Q', Deq n v Q Q') \/ (forall Q', ~ Deq n v Q Q').

  Proof with eattac.
    induction Q; intros...

    destruct a.
    destruct n.
    destruct n0.

    destruct (NChan_eq_dec (n0, t0) (n, t)).
    - inversion e0; subst; clear e0.
      destruct (H e v); subst.
      + left. exists Q...
      + right. intros.
        unfold not; intros.
        inversion H0; subst; ltac1:(congruence).
    - specialize (IHQ (n, t) v).
      destruct IHQ.
      + destruct H0 as [Q' H0].
        left.
        exists ((n0, t0, e)::Q').
        constructor...
      + right; repeat (intros ?).
        consider (Deq _ _ _ _).
        attac.
  Qed.


  (** If you deque something, it must have been in the queue *)
  Lemma Deq_In : forall [E : Set] n (v : E) Q0 Q1,
      Deq n v Q0 Q1 -> In (n, v) Q0.

  Proof.
    induction Q0; intros.
    - inversion H.
    - inversion H; clear H; subst; eattac.
  Qed.

  #[export] Hint Resolve Deq_In : LTS.


  (** Presence of a candidate, makes some deq possible *)
  Lemma In_Deq : forall [E : Set] n (v : E) Q0,
      List.In (n, v) Q0 -> exists v' Q1, Deq n v' Q0 Q1.

  Proof.
    induction Q0; intros.
    1: bullshit.

    destruct a as [n' v'].
    destruct (NChan_eq_dec n' n); kill H; subst.
    - exists v', Q0; attac.
    - exists v', Q0; attac.
    - specialize (IHQ0 H0) as (v'' & Q1 & HDeq).
      exists v'', ((n', v')::Q1).
      attac.
  Qed.

  #[export] Hint Immediate In_Deq : LTS.


  (** If something wasn't in the queue, then dequeing won't change it *)
  Lemma Deq_not_In : forall [E : Set] [n] [v : E] [n' v'] [Q0 Q1],
      ~ (In (n', v') Q0) ->
      Deq n v Q0 Q1 ->
      ~ (In (n', v') Q1).

  Proof.
    induction Q0; intros.
    - inversion H0.
    - repeat (intros ?).
      hsimpl in *; consider (Deq _ _ _ _); attac.
  Qed.

  #[export] Hint Resolve Deq_not_In : bullshit.


  (** Finding the dequed element *)
  Lemma Deq_split [E : Set] [n] [v : E] [Q0 Q1] :
    Deq n v Q0 Q1 ->
    exists Q10 Q11,
      Q0 = Q10 ++ (n, v)::Q11
      /\ Q1 = Q10 ++ Q11
      /\ forall v', ~ (List.In (n, v') Q10).

  Proof with (eattac).
    revert Q1.
    induction Q0; intros; inversion H; subst.
    - exists [], Q1...
    - specialize (IHQ0 _ HSeek) as (Q10 & Q11 & HEq0 & HEq1 & HNotIn).
      subst.

      hsimpl in *.

      exists ((n', e')::Q10), Q11...
  Qed.

  Hint Rewrite app_inv_l using assumption : LTS_R.
  Hint Rewrite app_inv_r using assumption : LTS_L.


  Lemma Deq_split_bs [E : Set] [n] [v v' : E] [Q0 Q1] :
    Deq n v (Q0 ++ (n, v)::Q1) (Q0 ++ Q1) ->
    ~ (List.In (n, v') Q0 /\ v <> v').

  Proof with (eattac).
    induction Q0; attac.
    kill H; attac. hsimpl in *.
    replace (Q0 ++ (n, v) :: Q1) with ((Q0 ++ [(n, v)]) ++ Q1) by attac.
    hsimpl in *.
    apply IHQ0; attac.
    rewrite H6.
    attac.
  Qed.

  #[export] Hint Resolve Deq_split_bs : bullshit.


  (** Dequeing two different things is interchangable *)
  Lemma Deq_Deq_swap [E : Set] [n0 n1] [v0 v1 : E] [Q0 Q1 Q2] :
    n0 <> n1 ->
    Deq n0 v0 Q0 Q1 ->
    Deq n1 v1 Q1 Q2 ->
    exists Q1', Deq n1 v1 Q0 Q1' /\ Deq n0 v0 Q1' Q2.

  Proof with (eattac).
    intros HNeq HDeq0 HDeq1.

    ltac1:(generalize dependent Q1).
    ltac1:(generalize dependent Q2).
    induction Q0; intros; inversion HDeq0; subst.
    2: inversion HDeq1; subst.
    - exists ((n0, v0)::Q2)...
    - exists Q0...
    - edestruct IHQ0 as [Q1 [HDeq1' HDeq0']]...
  Qed.


  (** If you enque then you can deque (something) *)
  Lemma Enq_Deq : forall [E : Set] n (v : E) Q,
    exists Q' v', Deq n v' (Q ++ [(n, v)]) Q'.

  Proof with attac.
    induction Q; intros.
    exists [], v...

    destruct a.
    destruct (NChan_eq_dec n n0); subst.
    + exists (Q ++ [(n0, v)]), e...
    + destruct IHQ as (Q' & v' & H).
      exists ((n0, e) :: Q'), v'...
  Qed.


  (** Prepending to a queue does not cancel enqueues. *)
  Lemma que_Enq1 : forall [E : Set] [n v] [Q0 Q1 : Que E] a,
      Enq n v Q0 Q1 -> Enq n v (a :: Q0) (a :: Q1).

  Proof. attac. Qed.

  #[export] Hint Resolve que_Enq1 : LTS.


  (** Prepending to a queue does not cancel enqueues. *)
  Lemma que_Enq : forall [E : Set] [n v] [Q0 Q1 : Que E] Q',
      Enq n v Q0 Q1 -> Enq n v (Q' ++ Q0) (Q' ++ Q1).

  Proof with eattac.
    induction Q'; intros...
  Qed.

  #[export] Hint Resolve que_Enq : LTS.


  (** Adding to a queue does not cancel dequeues. *)
  Lemma que_Deq : forall [E : Set] [n v] [Q0 Q1 : Que E] Q',
      Deq n v Q0 Q1 -> Deq n v (Q0 ++ Q') (Q1 ++ Q').

  Proof with attac.
    induction Q0; intros; kill H...
  Qed.

  #[export] Hint Resolve que_Deq : LTS.


  (** Deq decreases the length by 1 *)
  Lemma Deq_length_S [E : Set] [n] [v : E] [Q0 Q1] :
    Deq n v Q0 Q1 -> (length Q0 = S (length Q1))%nat.

  Proof.
    intro T.
    apply Deq_split in T as (? & ? & ? & ? & ?).
    subst.
    repeat (rewrite app_length).
    eattac.
  Qed.

  #[export] Hint Rewrite -> Deq_length_S using assumption : LTS.


  (** Deq decreases the length *)
  Lemma Deq_length [E : Set] [n] [v : E] [Q0 Q1] :
    Deq n v Q0 Q1 -> (length Q1 < length Q0)%nat.

  Proof.
    intro T.
    apply Deq_split in T as (? & ? & ? & ? & ?).
    subst.
    repeat (rewrite app_length).
    simpl.
    ltac1:(lia).
  Qed.

  #[export] Hint Resolve Deq_length : LTS bullshit.


  (** Deq changes length *)
  Lemma Deq_length_neq [E : Set] [n] [v : E] [Q0 Q1] :
    Deq n v Q0 Q1 -> (length Q1 <> length Q0)%nat.

  Proof.
    intro T.
    apply Deq_split in T as (? & ? & ? & ? & ?).
    subst.
    repeat (rewrite app_length).
    simpl.
    ltac1:(lia).
  Qed.

  #[export] Hint Resolve Deq_length_neq : LTS bullshit.


  (** Que after Deq is a subque of the original one *)
  Lemma Deq_incl [E : Set] [Q0 Q1] [n] [v : E] :
    Deq n v Q0 Q1 ->
    incl Q1 Q0.

  Proof.
    intros.
    generalize dependent Q1.
    induction Q0; intros; kill H.
    eattac.
    eapply IHQ0 in HSeek.
    intros x HIn.
    kill HIn; eattac.
  Qed.


  (** If something wasn't dequed and isn't in the resulting que, then it wasn't in the former *)
  Lemma Deq_not_In_r : forall [E : Set] [n n' : NChan] [v v' : E] [Q0 Q1],
      n <> n' ->
      Deq n v Q0 Q1 ->
      ~ (List.In (n', v') Q1) ->
      ~ (List.In (n', v') Q0).

  Proof.
    induction Q0; intros.
    - inversion H0.
    - unfold not in *.
      intros.
      kill H0; kill H2; bullshit.
  Qed.


  (** If something is not in left part of the que but a deque succeeded, then it was in the right *)
  Lemma Deq_app_or_l : forall [E : Set] [n : NChan] [v : E] [Q0 Q0' Q1],
      Deq n v (Q0 ++ Q0') Q1 ->
      ~ List.In (n, v) Q0' ->
      exists Q1', Deq n v Q0 Q1' /\ Q1 = Q1' ++ Q0'.
  Proof.
    induction Q0; intros; simpl in *.
    eattac.
    kill H.
    - eattac.
    - apply IHQ0 in HSeek as [Q1' [HDeq HEq]]; eattac.
  Qed.


  (** If something is not in right part of the que but a deque succeeded, then it was in the left *)
  Lemma Deq_app_or_r : forall [E : Set] [n : NChan] [v : E] [Q0 Q0' Q1],
      Deq n v (Q0 ++ Q0') Q1 ->
      ~ List.In (n, v) Q0 ->
      exists Q1', Deq n v Q0' Q1' /\ Q1 = Q0 ++ Q1'.
  Proof.
    induction Q0; intros; simpl in *; attac.
    kill H.
    apply IHQ0 in HSeek as [Q1' [HDeq HEq]]; eattac.
  Qed.


  Lemma Deq_neq_In [E : Set] [n n' v v'] [Q0 Q1 : Que E]:
    n <> n' ->
    Deq n v Q0 Q1 ->
    List.In (n', v') Q0 <->
      List.In (n', v') Q1.

  Proof.
    intros HNEq HDeq.
    split; intros HIn.
    - apply Deq_split in HDeq.
      hsimpl in *.
      apply in_app_or in HIn as [?|?]; attac.
    - apply Deq_split in HDeq.
      hsimpl in *.
      apply in_app_or in HIn as [?|?]; attac.
  Qed.


  Lemma Deq_app_and_l : forall [E : Set] [n : NChan] [v v' : E] [Q0 Q0' Q1 Q1'],
      Deq n v Q0 Q1 ->
      Deq n v' (Q0 ++ Q0') Q1' ->
      Q1' = Q1 ++ Q0' /\ v' = v.

  Proof.
    induction Q0; intros.
    - eattac.
    - simpl in *.
      kill H.
      + split; kill H0.
      + kill H0.
        edestruct IHQ0; eauto.
        attac.
  Qed.


  Lemma in_dec_v [E : Set] (n : NChan) Q :
    (exists (v : E), List.In (n, v) Q) \/ (forall (v : E), ~ List.In (n, v) Q).

  Proof.
    intros.
    induction Q; attac.
    destruct IHQ; hsimpl in *; eattac.
    destruct a as [n' v'].
    destruct (NChan_eq_dec n n'); eattac.
    right.
    eattac.
  Qed.

End QUE.
