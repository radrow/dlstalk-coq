From Coq Require Import Lia.

From DlStalk Require Import Tactics.

From Ltac2 Require Import Ltac2.

From Coq Require Import Lists.List.
Import ListNotations.

Theorem list_in_ind {A : Type} {eq_dec : forall x0 x1, {x0 = x1}+{x0 <> x1}}
  [P : list A -> Prop] :
  P [] ->
  (forall a l, List.In a l -> P (List.remove eq_dec a l) -> P l) ->
  forall l, P l.

Proof.
  intros Pnil HI.
  refine '(PeanoNat.Nat.measure_induction
            (list A)
            (@List.length A)
            P
            _
         ).
  intros l HI_len.

  destruct l; auto.
  assert (List.In a (a :: l)) by auto with datatypes.
  apply HI in H; auto.
  apply HI_len.
  eapply (remove_length_lt eq_dec); eauto.
Qed.


Theorem list_find_ind {A : Type} {eq_dec : forall x0 x1, {x0 = x1}+{x0 <> x1}}
  [P : list A -> Prop]
  (K : A -> Prop) (k_dec : forall x, {K x}+{not (K x)})
  :
  (forall l, Forall K l -> P l) ->
  (forall a l, List.In a l -> not (K a) -> P (List.remove eq_dec a l) -> P l) ->
  forall l, P l.

Proof.
  intros HAll HEx.

  refine '(PeanoNat.Nat.measure_induction
            (list A)
            (@List.length A)
            P
            _
         ).
  intros l HI_len.

  destruct (Forall_Exists_dec K k_dec l); auto.

  apply Exists_exists in e as [x [H HIn]].
  apply HEx in H; auto.
  apply HI_len.
  eapply (remove_length_lt eq_dec); eauto.
Qed.


Lemma partition_Forall [A : Type] (f : A -> bool) (l : list A) [l1 l2 : list A] :
  partition f l = (l1, l2) -> Forall (fun x => f x = true) l1 /\ Forall (fun x => f x = false) l2.

Proof.
  revert l1 l2.
  induction l; intros; simpl in *.
  - kill H; split; constructor.
  - destruct (partition f l) eqn:HEql.
    destruct (f a) eqn:HEqb; kill H; edestruct IHl; auto.
Qed.


Fixpoint partition_first [A : Type] (f : A -> bool) (l : list A) :=
  match l with
  | [] => ([], [])
  | y :: rest =>
      if f y then ([], y :: rest)
      else let (l0, l1) := partition_first f rest in (y::l0, l1)
  end.


Lemma partition_first_find [A : Type] (f : A -> bool) (l : list A) [l1 l2 : list A] [x : A] :
  partition_first f l = (l1, x::l2) -> f x = true.

Proof.
  revert l1 l2 x.
  induction l; intros; simpl in *.
  - kill H.
  - kill H.
    destruct (partition_first f l) eqn:HEql.

    destruct (f a) eqn:Heqb; eattac.
Qed.


Lemma partition_first_Forall [A : Type] (f : A -> bool) (l : list A) [l1 l2 : list A] :
  partition_first f l = (l1, l2) -> Forall (fun x => f x = false) l1.

Proof.
  revert l1 l2.
  induction l; intros; simpl in *.
  - kill H; constructor.
  - destruct (partition_first f l) eqn:HEql.
    destruct (f a) eqn:HEqb; kill H.
    constructor.
    constructor; auto.
    eapply IHl; eauto.
Qed.


Lemma partition_first_eq [A : Type] (f : A -> bool) (l : list A) [l1 l2 : list A] :
  partition_first f l = (l1, l2) -> l = l1 ++ l2.

Proof.
  revert l1 l2.
  induction l; intros; simpl in *.
  - kill H; constructor.
  - destruct (partition_first f l) eqn:HEql.
    destruct (f a) eqn:HEqb; kill H; auto.
    simpl.
    f_equal.
    eapply IHl; eauto.
Qed.


Theorem partition_first_eq_tail_ind {A : Type}
  (eqb : A -> A -> bool)
  (eqb_eq : forall x0 x1, eqb x0 x1 = true <-> x0 = x1)
  [P : list A -> Prop]
  :
  P [] ->
  (forall a l l0 l1,
      partition_first (eqb a) l = (l0, l1) ->
      P l1 -> P (a::l)
  ) ->
  forall l, P l.

Proof.
  intros H_nil HI.
  refine '(PeanoNat.Nat.measure_induction
            (list A)
            (@List.length A)
            P
            _
         ).
  intros l HI_len.

  destruct l; auto.

  destruct (partition_first (eqb a) l) eqn:HEq; auto.
  specialize (partition_first_Forall _ _ HEq) as Hl0.
  specialize (partition_first_eq _ _ HEq) as HEql. subst.

  eapply HI.
  apply HEq.
  apply HI_len.
  simpl.
  rewrite length_app.
  auto with arith.
Qed.


Theorem partition_first_tail_ind {A : Type}
  (f : A -> bool)
  [P : list A -> Prop]
  :
  (forall l, Forall (fun x => f x = false) l -> P l) ->
  (forall l l0 x l1,
      partition_first f l = (l0, x :: l1) ->
      P l1 -> P l
  ) ->
  forall l, P l.

Proof.
  intros H_base HI.
  refine '(PeanoNat.Nat.measure_induction
            (list A)
            (@List.length A)
            P
            _
         ).
  intros l HI_len.

  destruct (partition_first f l) eqn:HEq; auto.
  specialize (partition_first_Forall _ _ HEq) as Hl0.
  specialize (partition_first_eq _ _ HEq) as HEql. subst.

  destruct l1.
   - rewrite app_nil_r in *.
     apply H_base; auto.
   - eapply HI.
     apply HEq.
     apply HI_len.
     rewrite length_app.
     simpl in *.
     auto with arith.
Qed.


Fixpoint partition_last [A : Type] (f : A -> bool) (l : list A) :=
  match l with
  | [] => ([], [])
  | y :: rest => match partition_last f rest with
                | (l0, []) => if f y then ([], y::l0) else (y::l0, [])
                | (l0, z::l1) => (y::l0, z::l1)
                end
  end.


Lemma rev_iso :
  forall {A : Type} (P : list A -> Prop),
    (forall (l : list A), P l) <-> (forall (l : list A), P (rev l)).

Proof.
  intros.
  split; intros.
  - apply H.
  - specialize (H (rev l)).
    rewrite rev_involutive in H.
    assumption.
Qed.


Lemma rev_ind :
  forall [A : Type] (P : list A -> Prop),
    P [] ->
    (forall (l : list A) (a : A), P l -> P (l ++ [a])) ->
    forall l : list A, P l.

Proof.
  intros A P HBase HInd.
  apply rev_iso.
  apply rev_list_ind.
  - assumption.
  - intros.
    specialize (HInd (rev l) a H).
    assert (forall A (a : A), [a] = rev [a]) as HRev1. intros. simpl. reflexivity.
    rewrite HRev1 in HInd. clear HRev1.
    rewrite <- rev_app_distr in HInd.
    unfold app in HInd.
    assumption.
Qed.

Ltac rev_induction l :=
  try intros until l;
  generalize dependent l;
  refine (rev_ind _ _ _).



Lemma partition_last_find [A : Type] (f : A -> bool) (l : list A) [l1 l2 : list A] [x : A] :
  partition_last f l = (l1, x::l2) -> f x = true.

Proof.
  revert l1 l2 x.

  induction l; intros; simpl in *.
  - kill H.
  - destruct (partition_last f l) eqn:HEq.
    destruct l3.
    + destruct (f a) eqn:HEqb; kill H; auto.
    + kill H.
      eapply IHl.
      reflexivity.
Qed.


Lemma partition_last_Forall [A : Type] (f : A -> bool) (l : list A) :
  match partition_last f l with
  | (l0, []) => Forall (fun x => f x = false) l0
  | (_, (x::l1)) => Forall (fun x => f x = false) l1
  end.

Proof.
  induction l; intros; simpl in *; auto.
  destruct (partition_last f l) eqn:HEql.
  destruct l1; auto.
  destruct (f a) eqn:HEqb; auto.
Qed.


Lemma partition_last_eq [A : Type] (f : A -> bool) (l : list A) [l1 l2 : list A] :
  partition_last f l = (l1, l2) -> l = l1 ++ l2.

Proof.
  revert l1 l2.
  induction l; intros; simpl in *.
  - kill H; constructor.
  - destruct (partition_last f l) eqn:HEql.
    specialize (IHl l0 l3 eq_refl).
    subst.
    destruct l3.
    + destruct (f a) eqn:HEqb; kill H; auto with datatypes.
    + kill H.
      auto with datatypes.
Qed.


Theorem partition_last_eq_init_ind {A : Type}
  (eqb : A -> A -> bool)
  (eqb_eq : forall x0 x1, eqb x0 x1 = true <-> x0 = x1)
  [P : list A -> Prop]
  :
  P [] ->
  (forall a l l0 l1,
      partition_last (eqb a) l = (l0, l1) ->
      P l1 -> P (a::l)
  ) ->
  forall l, P l.

Proof.
  intros H_nil HI.
  refine '(PeanoNat.Nat.measure_induction
            (list A)
            (@List.length A)
            P
            _
         ).
  intros l HI_len.

  destruct l; auto.

  destruct (partition_last (eqb a) l) eqn:HEq; auto.
  specialize (partition_last_Forall (eqb a) l) as Hl0.
  rewrite HEq in Hl0.
  specialize (partition_last_eq _ _ HEq) as HEql. subst.

  eapply HI.
  apply HEq.
  apply HI_len.
  simpl.
  rewrite length_app.
  auto with arith.
Qed.


Theorem partition_last_eq_init_cons_ind {A : Type}
  (eqb : A -> A -> bool)
  (eqb_eq : forall x0 x1, eqb x0 x1 = true <-> x0 = x1)
  [P : list A -> Prop]
  :
  P [] ->
  (forall a l l0,
      partition_last (eqb a) l = (l0, []) ->
      P l0 -> P (a::l)
  ) ->
  (forall a l l0 l1,
      partition_last (eqb a) l = (l0, a::l1) ->
      P (a::l1) -> P (a::l)
  ) ->
  forall l, P l.

Proof.
  intros H_base H_nil H_cons.
  refine '(PeanoNat.Nat.measure_induction
            (list A)
            (@List.length A)
            P
            _
         ).
  intros l HI_len.

  destruct l; auto.

  destruct (partition_last (eqb a) l) eqn:HEq; auto.
  specialize (partition_last_Forall (eqb a) l) as Hl0.
  specialize (partition_last_eq _ _ HEq) as HEql. subst.
  destruct l1.
  - rewrite app_nil_r in *.
    eapply H_nil.
    apply HEq.
    apply HI_len.
    eauto with datatypes arith.
  - eapply H_cons.
    specialize (partition_last_find _ _ HEq) as HEqa.
    apply &eqb_eq in HEqa; subst.
    apply HEq.
    apply HI_len.
    simpl.
    rewrite length_app.
    simpl.
    auto with datatypes arith.
Qed.


Lemma decide_any [A : Type] [L P] :
  (forall x : A, List.In x L -> P x \/ ~ P x) ->
  (exists x, List.In x L /\ P x)
  \/ (forall x, List.In x L -> ~ P x).

Proof.
  intros Hdec.
  induction L.
  - right.
    intros.
    kill H.
  - destruct IHL; auto.
    + intros.
      apply Hdec.
      auto with datatypes.
    + left.
      destruct H as [x [HInx Hx]].
      exists x.
      split; auto with datatypes.
    + destruct (Hdec a); auto with datatypes.
      * left.
        exists a.
        split; auto with datatypes.
      * right.
        intros.
        kill H1; auto.
Qed.

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
    bs.
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
Qed.
Lemma cons_self_r [A] (l0 : list A) (a : A) : (a :: l0 = l0) <-> False.
Proof.
  split; intros; attac.
Qed.

#[export] Hint Rewrite -> cons_self_l cons_self_r using assumption : bs.


Lemma nodup_one : forall [A] (l : list A),
    NoDup l ->
    List.length l = 1%nat ->
    exists n, l = [n].

Proof.
  intros.
  destruct l > [|destruct l]; simpl in *; try (bs).
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
  destruct (in_dec eq_dec a (a::l)); doubt.
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
  induction l; simpl in *; try (bs).

  destruct (eq_dec a a0); subst.
  - constructor; auto.
    destruct (in_dec eq_dec a0 l); auto.
    kill H.
    assert (l = []) by (eapply nodup_nil_inv; attac).
    subst.
    constructor.
  - destruct (in_dec eq_dec a0 l); auto.
    + specialize (IHl H); clear H H0.
      enough (a = a0) by bs.
      specialize (Forall_forall (eq a) l) as [H _].
      apply H; auto.
    + kill H.
Qed.


Lemma append_bs : forall A l (a : A) l', l = l ++ (a :: l') <-> False.
Proof.
  split; intros.
  2: contradiction.
  intros. induction l; simpl in *.
  - discriminate.
  - bs.
Qed.

#[export] Hint Rewrite -> append_bs using spank : bs.


#[export] Hint Rewrite -> app_self_l app_self_r app_self_l' app_self_r' using assumption : LTS LTS_concl.

#[export] Hint Rewrite -> length_app using (solve [auto with datatypes; lia]) : LTS LTS_concl.

#[export] Hint Rewrite -> app_nil_l app_nil_r using assumption : LTS LTS_concl.

#[export] Hint Rewrite -> in_app_or using assumption : LTS LTS_concl.

#[export] Hint Rewrite -> Forall_app Forall_cons_iff using assumption : LTS LTS_concl.


#[export] Hint Constructors Forall : LTS.
