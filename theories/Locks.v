From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Std.

From Ltac2 Require Fresh.
From Ltac2 Require Import Control.
From Ltac2 Require Import Message.
From Ltac2 Require Import Std.
From Ltac2 Require Import Printf.

Import Ltac2.Notations.

Require Import LTS.
Require Import Model.
Require Import ModelData.
Require Import Network.
Require Import LTSTactics.
Require Import Que.

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
  (eq_b : A -> A -> bool)
  (eqb_eq : forall x0 x1, eqb x0 x1 = true <-> x0 = x1)
  [P : list A -> Prop]
  :
  P [] ->
  (forall a l l0 l1,
      partition_first (eq_b a) l = (l0, l1) ->
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

  destruct (partition_first (eq_b a) l) eqn:HEq; auto.
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
  (eq_b : A -> A -> bool)
  (eqb_eq : forall x0 x1, eqb x0 x1 = true <-> x0 = x1)
  [P : list A -> Prop]
  :
  P [] ->
  (forall a l l0 l1,
      partition_last (eq_b a) l = (l0, l1) ->
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

  destruct (partition_last (eq_b a) l) eqn:HEq; auto.
  specialize (partition_last_Forall (eq_b a) l) as Hl0.
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
  (eq_b : A -> A -> bool)
  (eqb_eq : forall x0 x1, eq_b x0 x1 = true <-> x0 = x1)
  [P : list A -> Prop]
  :
  P [] ->
  (forall a l l0,
      partition_last (eq_b a) l = (l0, []) ->
      P l0 -> P (a::l)
  ) ->
  (forall a l l0 l1,
      partition_last (eq_b a) l = (l0, a::l1) ->
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

  destruct (partition_last (eq_b a) l) eqn:HEq; auto.
  specialize (partition_last_Forall (eq_b a) l) as Hl0.
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


Module Locks(Name : UsualDecidableSet)(NetModF : NET).

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

  Parameter (Name_lt : Name -> Name -> Prop).
  Axiom (Name_lt_trans : forall x y z : Name, Name_lt x y -> Name_lt y z -> Name_lt x z).
  Axiom (Name_lt_not_eq : forall x y : Name, Name_lt x y -> ~ eq x y).
  Axiom Name_compare : forall x y, Compare Name_lt eq x y.

  Module Name_as_OT <: UsualOrderedType.
    Definition t := Name.

    Definition eq := @eq t.
    Definition eq_refl := @eq_refl t.
    Definition eq_sym := @eq_sym t.
    Definition eq_trans := @eq_trans t.

    Definition lt := Name_lt.

    Definition lt_trans := Name_lt_trans.

    Definition lt_not_eq := Name_lt_not_eq.

    Definition compare := Name_compare.

    Definition eq_dec := MD.NAME.eq_dec.
  End Name_as_OT.


  Module Import NetMap := FMapList.Make(Name_as_OT).

  Notation "# v" := (NetMap.t v) (at level 20) : type_scope.

  Notation Names := (list Name).

  Module NetMod := NetModF(MD.NAME).
  Module Net := Net(MD)(NetMod).

  Import Net.Model.

  Notation R := Tag.R.
  Notation Q := Tag.Q.

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
      intros P0 P1 a T HD _.
      kill T; kill HD...
      destruct n.
      destruct t0.
      - apply HDecQ in H.
        destruct H...
      - apply HDecR in H.
        destruct H...
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
      destruct n.
      specialize (H n).
      destruct H.
      destruct t0.
      1: cbv in *; bullshit.
      apply H...
      unfold not; intros.
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
      destruct t0.
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
        eapply act_particip_stay; eauto.
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
          + assert (forall x, List.In x l -> t0 <> x).
            apply Forall_forall.
            unshelve eapply (Forall_impl _ _ Hl0).
            * intros.
              apply NAME_H.eqb_neq_inv in H.
              auto.
            * intros HIn.
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
      (* SRPC_net N0 -> *)
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


  Module Import SRPC.
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

  End SRPC.


  Notation "'Work'" := (fun c => Busy (HWork c)) (at level 30).
  Notation "'Lock'" := (fun c s => Busy (HLock c s)) (at level 30).

  Notation "'Work' c" := (Busy (HWork c)) (at level 200) : type_scope.
  Notation "'Lock' c s" := (Busy (HLock c s)) (at level 200) : type_scope.


  Module Import NetSRPC.
    Import Net.


    Section LocksStatic.

      Context `[N : PNet].
      Context `{Hsrpc : forall n, AnySRPC_pq (NetMod.get n N)}.


      (** In SRPC network, a process can have at most one lock *)
      Lemma lock_uniq [n m0 m1] :
        net_lock_on N n m0 ->
        net_lock_on N n m1 ->
        m0 = m1.

      Proof with (eauto with LTS).
        unfold net_lock_on.
        unfold net_lock.

        intros HL0 HL1.

        destruct HL0 as [L0 [HIn0 HL0]].
        destruct HL1 as [L1 [HIn1 HL1]].

        assert (incl L1 L0 /\ incl L0 L1) as [Hincl0 Hincl1] by attac.
        apply (SRPC_pq_one_lock (Hsrpc n)) in HL1...

        assert (nodup Name.eq_dec L1 = [m1]) as Hm1.
        {
          assert (exists m', nodup Name.eq_dec L1 = [m'])
            by (apply nodup_one; auto using NoDup_nodup).
          hsimpl in *.
          enough (m' = m1) by attac.
          assert (Forall (eq m') L1) by eauto using nodup_one_all_same.
          assert (List.In m1 L1 -> eq m' m1) by (apply Forall_forall; attac).
          attac.
        }

        apply (nodup_incl Name.eq_dec) in Hincl1.
        rewrite Hm1 in Hincl1.

        unfold incl in *.

        apply Hincl1 in HIn0.

        kill HIn0; auto.
      Qed.

      Hint Resolve lock_uniq : LTS.


      (** In an SRPC network, lock sets are singletons  *)
      Lemma SRPC_net_get_lock [L n0] :
        net_lock N L n0 ->
        exists n1, net_lock N [n1] n0.

      Proof with eattac.
        intros HL.
        eapply SRPC_pq_get_lock...
      Qed.


      (** In an SRPC network, any member of a lock set is the lock set *)
      Lemma SRPC_net_get_lock_In [L n0 n1] :
        List.In n1 L ->
        net_lock N L n0 ->
        net_lock N [n1] n0.

      Proof with eattac.
        intros HIn HL.

        edestruct (SRPC_net_get_lock HL) as [n' HL']...

        assert (net_lock_on N n0 n1)...
        assert (net_lock_on N n0 n')...
        assert (n' = n1)...
      Qed.

      Hint Immediate SRPC_net_get_lock_In : LTS.


      (** Lock set is always a singleton *)
      Lemma lock_singleton [n0 n1] :
        net_lock_on N n0 n1 ->
        net_lock N [n1] n0.

      Proof with eattac.
        intros HL.
        destruct HL as [L [HIn HL]].

        specialize (SRPC_pq_get_lock (Hsrpc n0) HL) as [n HLn].
        specialize (pq_lock_equiv HL HLn) as [HinL HinR].
        specialize (HinL n1 HIn).
        kill HinL...
      Qed.

      Hint Resolve lock_singleton : LTS.


      Lemma deadlocked_lock_on' [n0 : Channel.Name] [n1 : Name] :
        deadlocked n1 N ->
        net_lock_on N n0 n1 ->
        deadlocked n0 N.

      Proof.
        intros.
        eauto with LTS.
      Qed.

      Hint Immediate deadlocked_lock_on' : LTS.


      Lemma deadlocked_dep' [n0 : Channel.Name] [n1 : Name] :
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
        intros H0 H1.

        kill H0; rewrite (lock_uniq H1 H) in *.
        constructor; auto.
        assumption.
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
        eapply lock_uniq; eauto.

        rewrite (lock_uniq HLnn H) in *.
        apply IHHLnm.
        rewrite <- (lock_uniq HLnn H)...
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
        - rewrite (lock_uniq H HL) in *...
        - rewrite (lock_uniq H HL) in *.
          specialize (IHHLc HL) as [HF HEq]; subst...
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
          kill HLc1; rewrite (lock_uniq H H0) in *...
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

        kill HLc1; rewrite (lock_uniq H H1) in *; clear H.
        1: bullshit.

        clear n3.
        rename l into L0.
        rename l0 into L1.
        rename n0 into n2.
        rename n4 into n0.

        destruct (lock_chain_prefix H0 H2) as [L' [HEq'|HEq']]; subst.
        - apply in_or_app. right.
          clear HEq0.
          clear H1.

          generalize dependent L'.
          generalize dependent n0.
          generalize dependent n1.
          generalize dependent n2.
          ltac1:(dependent induction L1); intros; simpl in *.
          + kill H2.
            kill H0; rewrite (lock_uniq H H1) in *; attac.
          + kill H2.
            kill H0.
            eapply IHL1; attac.
        - exfalso.

          specialize (lock_chain_break H0 H2) as [HEq' | [L [HEq' HLc]]]; subst.
          { rewrite app_nil_r in *.
            rewrite (lock_chain_target H0 H2) in *.
            bullshit.
          }
          clear H2.

          apply lock_chain_dedup in HLc as (L1 & HLc1 & _ & HIn0' & HIn0''); subst.

          kill HLc1; rewrite (lock_uniq H H1) in *; auto.

          apply Decidable.not_or in HIn as [_ HIn].
          apply Net.not_in_app_inv in HIn as [HIn _].
          rename l into L1.
          clear HEq0.
          clear H1.
          clear H.
          clear n4.

          specialize (lock_chain_prefix H0 H2) as [L'' [HEq'|HEq']]; subst.
          + generalize dependent L''.
            generalize dependent n0.
            generalize dependent n1.
            generalize dependent n2.

            induction L1; intros; simpl in *.
            * kill H2.
              kill H0; rewrite (lock_uniq H H1) in *; attac.
            * kill H2.
              kill H0.
              eapply IHL1; eauto with datatypes LTS.

          + generalize dependent L''.
            generalize dependent n0.
            generalize dependent n1.
            generalize dependent n2.

            induction L0; intros; simpl in *.
            * kill H0.
              kill H2; rewrite (lock_uniq H H0) in *; attac.
            * kill H0.
              kill H2.
              eapply IHL0; eauto with datatypes LTS.
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
            kill HLc'; rewrite (lock_uniq H H0) in *; auto.

            destruct (lock_chain_loop_in HLc1 H1); auto.

          + kill HLc0.
            smash_eq a m; auto.
            right.

            assert (dep_on N a m) as HD.
            {
              kill H; ltac1:(eassert (a = _) by (eapply lock_uniq; eattac));
              congruence.
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
            rewrite (lock_uniq H1 H0) in *; eauto.
            rewrite (lock_uniq H1 H0) in *; eauto.
            kill H2; bullshit.

          + kill HLc.
            smash_eq a m; auto.

            assert (dep_on N a m) as HD.
            {
              kill H; ltac1:(eassert (a = _) by (eapply lock_uniq; eattac)); congruence.
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

          apply (SRPC_net_get_lock_In HIn'r) in HLc'r...
          exists [n']...

        - destruct H as [Lr' [HIn'r HLc'r]].

          apply (SRPC_net_get_lock_In HIn'r) in HLc'r...
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


      Lemma dep_set_lock_on_dec [m n D] :
        dep_set N D m ->
        List.In n D ->
        (exists n', net_lock_on N n n') \/ forall n', ~ net_lock_on N n n'.
      Proof.
          intros.

          specialize (@lock_singleton n) as Hls.

          assert (AnySRPC_pq (NetMod.get n N)) as Hsrpc_n by auto.
          assert (forall s, pq_lock [s] (NetMod.get n N) -> exists c, SRPC_pq (Lock c s) (NetMod.get n N))
            as H_lock
              by (intros; apply lock_SRPC_Lock_pq; auto).

          destruct Hsrpc_n as [srpc Hsrpc_n].
          unfold net_lock_on in *.
          unfold net_lock in *.
          destruct (NetMod.get n N) as [I P O].
          simpl in Hsrpc_n.

          destruct srpc > [|destruct s].
          - right.
            intros n' HL'.
            apply Hls in HL'.
            specialize (H_lock _ HL') as [c H_lock].
            simpl in H_lock.
            specialize (SRPC_inv Hsrpc_n H_lock) as Boom.
            bullshit.
          - right.
            intros n' HL'.
            apply Hls in HL'.
            specialize (H_lock _ HL') as [c' H_lock].
            simpl in H_lock.
            specialize (SRPC_inv Hsrpc_n H_lock) as Boom.
            kill Boom.
          - destruct (Deq_dec' &I (s, R)) as [[v [I' HDeq]]|HNDeq].
            + apply Deq_In in HDeq.
              right.
              intros n' HL'.
              apply Hls in HL'.
              specialize (H_lock _ HL') as [c' H_lock].
              simpl in H_lock.
              specialize (SRPC_inv Hsrpc_n H_lock) as HEq; kill HEq.
              kill HL'.
              bullshit.
            + destruct O.
              * left.
                exists s, [s].
                split; attac.
                -- apply SRPC_Decisive; eattac.
                -- apply In_Deq in H2 as (v' & I' & HDeq).
                   bullshit.
              * right.
                intros n' HL'.
                apply Hls in HL'.
                kill HL'.
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
            apply SRPC_net_get_lock in HD1 as [n2 HD1].
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
              rewrite (lock_uniq H Ha) in *; eauto.
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
              rewrite (lock_uniq H Ha) in *; eauto.
              attac.
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
          apply SRPC_net_get_lock in HL' as [n' HL'].
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
          apply SRPC_net_get_lock in HL2 as [n1 HL2].
          exists n1.
          eattac.
        }

        exists n1; split; auto with LTS.

        enough (List.In n1 L) by attac.

        eapply deadset_in; eauto.
      Qed.

    End LocksStatic.

    #[export] Hint Resolve
      lock_uniq
      deadlocked_dep'
      lock_chain_target
      lock_self_dep_uniq
      dep_loop_dep_set
      : LTS.

    #[export] Hint Immediate
      dep_set_deadset
      deadlocked_lock_on'
      dep_loop1
      dep_loop
      SRPC_net_get_lock_In
      dep_reloop
      dep_set_reloop
      : LTS.

    #[export] Hint Rewrite
      lock_uniq
      lock_self_dep_uniq
      lock_self_lock_chain_uniq
      lock_chain_target
      using assumption
      : LTS.


    Inductive mut_exclusive : list Prop -> list Prop -> Prop :=
    | me_nil Ps : mut_exclusive Ps nil
    | me_cons [P : Prop] [Ps0 Ps1] :
      (P -> Forall not (Ps0 ++ Ps1)) ->
      mut_exclusive (P :: Ps0) Ps1 ->
      mut_exclusive Ps0 (P :: Ps1)
    .

    #[export] Hint Constructors mut_exclusive : LTS.
    Notation mut_excl := (mut_exclusive []).


  (** Replaces all parameters with fresh variables. Returns hypos to destruct. *)
  Ltac2 rec unsubst (t : constr) : ident list :=
    match! t with
    | ?f ?x =>
        if Bool.or (Constr.is_var x)
             (Bool.or (Constr.is_ind x) (Constr.is_const x))
        then unsubst f
        else
          (let i := Fresh.in_goal @arg in
           let e := Fresh.in_goal @HEq in
           remember $x as $i eqn:$e;
           (e :: unsubst f)
        )
    | _ => []
    end.


  Ltac2 inversion_stable_ (c : constr) (i : intro_pattern option) : unit :=
    let var := Fresh.in_goal @x in
    let to_kill := unsubst (Constr.type c) in
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Var v => rename $v into $var
    | _ => remember $c as $var
    end;
    Std.inversion FullInversion (ElimOnIdent var) i None;
    Control.enter (
        fun () =>
          let _ := List.map (
                     fun i =>
                       try (ltac1:(i |- dependent destruction i) (Ltac1.of_constr (hyp i)))
                     ) to_kill
          in
          try (clear $var); ssubst
      ).


  Ltac2 Notation "inversion_stable"
    arg(constr)
    pat(opt(seq("as", intropattern))) :=
    inversion_stable_ arg pat.

    Fact ex_to_forall [T] [P : T -> Prop] [p] : (ex P -> p) -> forall x, P x -> p.
    Proof. intros. eauto. Qed.


    Ltac2 rec destruct_not_Forall h :=
      let hh := hyp h in
      match! Constr.type hh with
      | _ -> Forall not [] => clear $h
      | ?p -> Forall not (?x::?rest) =>
          let l := Fresh.in_goal @H in
          assert ($p -> not $x) as $l by (intros; apply (Forall_inv ($hh ltac:(assumption))));
          let lh := hyp l in
          try (
              specialize (ex_to_forall $lh); clear $l; intros $l; simpl in $l
            );
          let r := Fresh.in_goal @H in
          assert ($p -> Forall not $rest) as $r by (intros; apply (Forall_inv_tail ($hh ltac:(assumption))));
          clear $h;
          destruct_not_Forall r
      end.


    Ltac2 rec destruct_Forall (h : ident) : unit :=
      let hh := hyp h in
      lazy_match! Constr.type hh with
      | Forall _ nil => clear $h
      | Forall ?f (cons ?p ?ps) =>
          let hp := Fresh.in_goal h in
          let hRest := Fresh.fresh (Fresh.Free.union (Fresh.Free.of_goal ()) (Fresh.Free.of_ids [hp])) h  in
          first [ assert (?f ?P) by assumption
                | specialize (Forall_inv $hh) as $hp
            ];
          specialize (Forall_inv_tail $hh) as $hRest;
          clear $h;
          destruct_Forall hRest
      | Forall _ _ => ()
      | _ -> Forall _ [] =>
          clear $h
      | ?p -> Forall _ _ =>
          try (specialize ($hh ltac:(eauto)); destruct_Forall h)
      | _ => Control.zero Match_failure
      end.


    Ltac2 rec destruct_mut_exclusive h :=
      let hh := hyp h in
      lazy_match! Constr.type hh with
      | mut_exclusive _ [] =>
          clear $h; subst
      | mut_exclusive _ (_ :: _) =>
          let p := Fresh.in_goal @p_ in
          let ps0 := Fresh.in_goal @ps0_ in
          let ps1 := Fresh.in_goal @ps1_ in
          let hnot := Fresh.in_goal @H_excl in
          let h_next := Fresh.in_goal @next_ in
          let hs0 := Fresh.in_goal @hs0_ in
          let hs1 := Fresh.in_goal @hs1_ in
          let hsn0 := Fresh.in_goal @hsn0_ in
          let hsn1 := Fresh.in_goal @hsn1_ in
          let hsn2 := Fresh.in_goal @hsn2_ in
          inversion_stable $hh
            as [$p $hs0 $hs1 | $p $ps0 $ps1 $hnot $h_next $hsn0 [$hsn1 $hsn2]];
          doubt;
          clear $h;
          try (subst $ps0);
          try (subst $ps1);
          try (subst $p);
          let h_nexth := hyp h_next in
          destruct_mut_exclusive h_next;
          simpl app in $hnot;
          destruct_Forall hnot;
          try (destruct_not_Forall hnot)
      end.


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


    (** A much stronger version of SRPC_pq which holds in any network with the same premises *)
    Inductive SRPC_pq_in_net (srpc : SRPC_State) : PQued -> Prop :=
      SPRC_pq_net_ [I P O]
        (* The process code is SRPC *)
        (Hsrpc : SRPC srpc P)

        (* Incoming queries are unique per sender *)
        (H_Q_in : forall I' c v v', Deq (c, Q) v I I' -> not (List.In (c, Q, v') I'))

        (* Incoming reply is unique *)
        (H_R_in : forall I' s s' v v', Deq (s, R) v I I' -> not (List.In (s', R, v') I'))

        (* Incoming reply implies a lock  *)
        (H_R_in_lock : forall s v, List.In (s, R, v) I -> exists c, srpc = Lock c s)

        (* Outgoing query implies a lock  *)
        (H_Q_out_lock : forall s v, List.In (s, Q, v) O -> exists c, srpc = Lock c s)

        (* Outgoing query is the last outgoing message *)
        (H_Q_out_last : forall s v, not (List.In (s, Q, v) (List.removelast O)))

        (* Outgoing reply is unique per recipient *)
        (H_R_out_uniq : forall O' c v v', Deq (c, R) v O O' -> not (List.In (c, R, v') O'))

        (* If there is an incoming reply, then there is no outgoing query *)
        (H_R_Q : forall s v v', List.In (s, R, v) I -> not (List.In (s, Q, v') O))

        (* If there is an outgoing query, then there is no incoming reply *)
        (H_Q_R : forall s v v', List.In (s, Q, v) O -> not (List.In (s, R, v') I))

        (* If the process is locked, and output que is not empty, then there is a query in there *)
        (H_lock_Q : forall c s, srpc = Lock c s -> [] <> O -> exists v, List.In (s, Q, v) O)

        (* For any client, its query is at one "stage" at a time *)
        (H_query_uniq : forall c,
            mut_excl
              [ exists v, List.In (c, Q, v) I;
                proc_client c P;
                exists v, List.In (c, R, v) O
              ]
        )

        : SRPC_pq_in_net srpc (pq I P O).


    Lemma SRPC_pq_in_net_SRPC [srpc : SRPC_State] [S] :
      SRPC_pq_in_net srpc S -> SRPC_pq srpc S.

    Proof. intros. kill H. attac. Qed.

    Lemma SRPC_pq_in_net_Q_in [srpc : SRPC_State] [c v v' I I' P O] :
      SRPC_pq_in_net srpc (pq I P O) ->
      Deq (c, Q) v I I' ->
      not (List.In (c, Q, v') I').
    Proof. intros. kill H. attac 1. Qed.

    Lemma SRPC_pq_in_net_R_in [srpc : SRPC_State] [s s' v v' I I' P O] :
      SRPC_pq_in_net srpc (pq I P O) ->
      Deq (s, R) v I I' ->
      not (List.In (s', R, v') I').
    Proof. intros. kill H. attac 1. Qed.

    Lemma SRPC_pq_in_net_R_in_lock [srpc : SRPC_State] [s v I P O] :
      SRPC_pq_in_net srpc (pq I P O) ->
      List.In (s, R, v) I ->
      exists c, srpc = Lock c s.
    Proof. intros. kill H. eapply H_R_in_lock. eattac 1. Qed.

    Lemma SRPC_pq_in_net_Q_out_lock [srpc : SRPC_State] [s v I P O] :
      SRPC_pq_in_net srpc (pq I P O) ->
      List.In (s, Q, v) O ->
      exists c, srpc = Lock c s.
    Proof. intros. kill H. eapply H_Q_out_lock. eattac 1. Qed.

    Lemma SRPC_pq_in_net_Q_out_last [srpc : SRPC_State] [s v I P O] :
      SRPC_pq_in_net srpc (pq I P O) ->
       ~ (List.In (s, Q, v) (List.removelast O)).
    Proof. intros. kill H. eattac 1. Qed.

    Lemma SRPC_pq_in_net_Q_out_uniq [srpc : SRPC_State] [c v v' I P O O'] :
      SRPC_pq_in_net srpc (pq I P O) ->
      Deq (c, R) v O O' ->
      ~ (List.In (c, R, v') O').
    Proof. intros. kill H. eattac 1. Qed.

    Lemma SRPC_pq_in_net_R_Q [srpc : SRPC_State] [s v v' I P O] :
      SRPC_pq_in_net srpc (pq I P O) ->
      List.In (s, R, v) I -> not (List.In (s, Q, v') O).
    Proof. intros. kill H. eattac 1. Qed.

    Lemma SRPC_pq_in_net_Q_R [srpc : SRPC_State] [s v v' I P O] :
      SRPC_pq_in_net srpc (pq I P O) ->
      List.In (s, Q, v) O -> not (List.In (s, R, v') I).
    Proof. intros. kill H. eattac 1. Qed.

    Lemma SRPC_pq_in_net_lock_Q [c s I P O] :
      SRPC_pq_in_net (Lock c s) (pq I P O) ->
      O <> [] ->
      exists v, List.In (s, Q, v) O.
    Proof. intros. kill H. eattac 1. Qed.

    Lemma SRPC_pq_in_net_Q_excl_R [srpc : SRPC_State] [c v v' I P O] :
      SRPC_pq_in_net srpc (pq I P O) ->
      List.In (c, Q, v) I ->
      ~ List.In (c, R, v') O.
    Proof. intros. kill H. specialize (H_query_uniq c). destruct_mut_exclusive @H_query_uniq. eauto. Qed.

    Lemma SRPC_pq_in_net_Q_excl_c [srpc : SRPC_State] [c v I P O] :
      SRPC_pq_in_net srpc (pq I P O) ->
      List.In (c, Q, v) I ->
      ~ proc_client c P.
    Proof. intros. kill H. specialize (H_query_uniq c). destruct_mut_exclusive @H_query_uniq. eauto. Qed.

    Lemma SRPC_pq_in_net_R_excl_Q [srpc : SRPC_State] [c v v' I P O] :
      SRPC_pq_in_net srpc (pq I P O) ->
      List.In (c, R, v) O ->
      ~ List.In (c, Q, v') I.
    Proof. intros. kill H. specialize (H_query_uniq c). destruct_mut_exclusive @H_query_uniq. eauto. Qed.

    Lemma SRPC_pq_in_net_R_excl_c [srpc : SRPC_State] [c v I P O] :
      SRPC_pq_in_net srpc (pq I P O) ->
      List.In (c, Q, v) I ->
      ~ proc_client c P.
    Proof. intros. kill H. specialize (H_query_uniq c). destruct_mut_exclusive @H_query_uniq. eauto. Qed.

    Lemma SRPC_pq_in_net_c_excl_Q [srpc : SRPC_State] [c v I P O] :
      SRPC_pq_in_net srpc (pq I P O) ->
      proc_client c P ->
      ~ List.In (c, Q, v) I.
    Proof. intros. kill H. specialize (H_query_uniq c). destruct_mut_exclusive @H_query_uniq. eauto. Qed.

    Lemma SRPC_pq_in_net_c_excl_R [srpc : SRPC_State] [c v I P O] :
      SRPC_pq_in_net srpc (pq I P O) ->
      proc_client c P ->
      ~ List.In (c, R, v) O.
    Proof. intros. kill H. specialize (H_query_uniq c). destruct_mut_exclusive @H_query_uniq. eauto. Qed.


    #[export] Hint Resolve
      SRPC_pq_in_net_SRPC
      SRPC_pq_in_net_Q_in
      SRPC_pq_in_net_R_in
      SRPC_pq_in_net_R_in_lock
      SRPC_pq_in_net_Q_out_lock
      SRPC_pq_in_net_Q_out_last
      SRPC_pq_in_net_Q_out_uniq
      SRPC_pq_in_net_R_Q
      SRPC_pq_in_net_Q_R
      SRPC_pq_in_net_lock_Q
      SRPC_pq_in_net_Q_excl_R
      SRPC_pq_in_net_Q_excl_c
      SRPC_pq_in_net_R_excl_Q
      SRPC_pq_in_net_R_excl_c
      SRPC_pq_in_net_c_excl_Q
      SRPC_pq_in_net_c_excl_R
      : LTS.


    (** If an SRPC service is locked after an action, then it's either a send (todo: from its output
    queue) or a non-unlocking message *)
    Lemma SRPC_pq_send_lock [srpc n a S0 S1] :
      SRPC_pq_in_net srpc S0 -> (*  TODO : to net and remove n'<>n *)
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


    (* Not enough! We need inter-proc facts! *)
    Definition SRPC_net (N : PNet) := forall n, exists srpc, SRPC_pq_in_net srpc (NetMod.get n N).
    #[export] Hint Unfold SRPC_net : LTS.
    #[export] Hint Transparent SRPC_net : LTS.


    (* (* This is to allow the condition from LocksStatic be used in Immediate hints. *) *)
    (* Lemma SRPC_net_AnySRPC' (N : PNet) : SRPC_net N -> forall n, AnySRPC_pq (NetMod.get n N). *)
    (* Proof. intros. specialize (H n). kill H. attac. Qed. *)
    (* #[export] Hint Extern 0 (forall n, AnySRPC_pq (NetMod.get n _)) => simple apply SRPC_net_AnySRPC'; eassumption : LTS. *)


    Section Inversions.
      (* These hints should not quadrate with SRPC_pq variants because SRPC_net does not expose
      SRPC_pq_in_net *)

      Lemma SRPC_net_AnySrpc [N S n] :
        SRPC_net N ->
        NetMod.get n N = S ->
        AnySRPC_pq S.
      Proof.
        intros. specialize (H n) as [srpc H]. rewrite H0 in *. kill H. eauto with LTS.
      Qed.

      Lemma SRPC_net_in_net_Q_in [N n c v v' I I' P O] :
        SRPC_net N ->
        NetMod.get n N = pq I P O ->
        Deq (c, Q) v I I' ->
        not (List.In (c, Q, v') I').
      Proof. intros. specialize (H n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma SRPC_net_in_net_R_in [N n s s' v v' I I' P O] :
        SRPC_net N ->
        NetMod.get n N = pq I P O ->
        Deq (s, R) v I I' ->
        not (List.In (s', R, v') I').
      Proof. intros. specialize (H n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma SRPC_net_in_net_R_in_lock [N n s v I P O] :
        SRPC_net N ->
        NetMod.get n N = pq I P O ->
        List.In (s, R, v) I ->
        exists c, SRPC_pq (Lock c s) (NetMod.get n N).
      Proof. intros. specialize (H n) as [srpc H]. rewrite H0 in *. consider (exists c, srpc = Lock c s); eattac.
      Qed.

      Lemma SRPC_net_in_net_Q_out_lock [N n s v I P O] :
        SRPC_net N ->
        NetMod.get n N = pq I P O ->
        List.In (s, Q, v) O ->
        exists c, SRPC_pq (Lock c s) (NetMod.get n N).
      Proof.
        intros. specialize (H n) as [srpc H]. rewrite H0 in *. consider (exists c, srpc = Lock c s); eattac.
      Qed.

      Lemma SRPC_net_in_net_Q_out_last [N n s v I P O] :
        SRPC_net N ->
        NetMod.get n N = pq I P O ->
        ~ (List.In (s, Q, v) (List.removelast O)).
      Proof. intros. specialize (H n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma SRPC_net_in_net_Q_out_uniq [N n c v v' I P O O'] :
        SRPC_net N ->
        NetMod.get n N = pq I P O ->
        Deq (c, R) v O O' ->
        ~ (List.In (c, R, v') O').
      Proof. intros. specialize (H n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma SRPC_net_in_net_R_Q [N n s v v' I P O] :
        SRPC_net N ->
        NetMod.get n N = pq I P O ->
        List.In (s, R, v) I -> not (List.In (s, Q, v') O).
      Proof. intros. specialize (H n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma SRPC_net_in_net_Q_R [N n s v v' I P O] :
        SRPC_net N ->
        NetMod.get n N = pq I P O ->
        List.In (s, Q, v) O -> not (List.In (s, R, v') I).
      Proof. intros. specialize (H n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma SRPC_net_in_net_Q_excl_R [N n c v v' I P O] :
        SRPC_net N ->
        NetMod.get n N = pq I P O ->
        List.In (c, Q, v) I ->
        ~ List.In (c, R, v') O.
      Proof. intros. specialize (H n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma SRPC_net_in_net_Q_excl_c [N n c v I P O] :
        SRPC_net N ->
        NetMod.get n N = pq I P O ->
        List.In (c, Q, v) I ->
        ~ proc_client c P.
      Proof. intros. specialize (H n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma SRPC_net_in_net_R_excl_Q [N n c v v' I P O] :
        SRPC_net N ->
        NetMod.get n N = pq I P O ->
        List.In (c, R, v) O ->
        ~ List.In (c, Q, v') I.
      Proof. intros. specialize (H n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma SRPC_net_in_net_R_excl_c [N n c v I P O] :
        SRPC_net N ->
        NetMod.get n N = pq I P O ->
        List.In (c, Q, v) I ->
        ~ proc_client c P.
      Proof. intros. specialize (H n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma SRPC_net_in_net_c_excl_Q [N n c v I P O] :
        SRPC_net N ->
        NetMod.get n N = pq I P O ->
        proc_client c P ->
        ~ List.In (c, Q, v) I.
      Proof. intros. specialize (H n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma SRPC_net_in_net_c_excl_R [N n c v I P O] :
        SRPC_net N ->
        NetMod.get n N = pq I P O ->
        proc_client c P ->
        ~ List.In (c, R, v) O.
      Proof. intros. specialize (H n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.
    End Inversions.


    #[export] Hint Resolve
      SRPC_net_AnySrpc
      SRPC_net_in_net_Q_in
      SRPC_net_in_net_R_in
      SRPC_net_in_net_R_in_lock
      SRPC_net_in_net_Q_out_lock
      SRPC_net_in_net_Q_out_last
      SRPC_net_in_net_Q_out_uniq
      SRPC_net_in_net_R_Q
      SRPC_net_in_net_Q_R
      SRPC_net_in_net_Q_excl_R
      SRPC_net_in_net_Q_excl_c
      SRPC_net_in_net_R_excl_Q
      SRPC_net_in_net_R_excl_c
      SRPC_net_in_net_c_excl_Q
      SRPC_net_in_net_c_excl_R
      : LTS.


    (* If n0 is locked on n1, then n1 handles the query of n0 *)
    Definition locks_sound N := forall n0 n1,
        net_lock_on N n0 n1 ->
        pq_client n0 (NetMod.get n1 N).


    (* If n1 handles a query from n0, then n0 is locked on n1   *)
    Definition locks_complete N := forall n0 n1,
        pq_client n0 (NetMod.get n1 N) -> net_lock_on N n0 n1.


    Inductive net_sane (N : PNet) : Prop :=
    | NetSane
        (H_Sane_SRPC : SRPC_net N)
        (H_lock_sound : locks_sound N)
        (H_lock_complete : locks_complete N)
      : net_sane N.


    Lemma net_sane_SRPC [N : PNet] : net_sane N -> SRPC_net N.
    Proof. intros. kill H. auto. Qed.

    Lemma net_sane_lock_client [N S n0 n1] : net_sane N -> NetMod.get n1 N = S -> net_lock_on N n0 n1 -> pq_client n0 S.
    Proof. intros. kill H. auto. Qed.

    Lemma net_sane_client_lock [N S n0 n1] : net_sane N -> NetMod.get n1 N = S -> pq_client n0 S -> net_lock_on N n0 n1.
    Proof. intros. kill H. auto. Qed.


    #[export] Hint Resolve net_sane_SRPC net_sane_lock_client net_sane_client_lock : LTS.


    (* This is to allow the condition from LocksStatic be used in Immediate hints. *)
    Lemma net_sane_AnySRPC' (N : PNet) : net_sane N -> forall n, AnySRPC_pq (NetMod.get n N).
    Proof. intros. kill H. specialize (H_Sane_SRPC n) as [? H]. kill H. attac. Qed.
    #[export] Hint Extern 0 (forall n, AnySRPC_pq (NetMod.get n _)) => simple apply net_sane_AnySRPC'; eassumption : LTS.


    Ltac2 rec solve_mut_exclusive (full : bool) :=
      lazy_match! goal with
      | [|- mut_exclusive _ []] => constructor
      | [|- mut_exclusive _ (_::_)] =>
          constructor >
            [ let h := Fresh.in_goal @H in
              intros $h;
              simpl app;
              if full then solve_mut_exclusive full else ()
            | solve_mut_exclusive full
            ]
      | [|- Forall _ []] => constructor
      | [|- Forall not (_::_)] =>
          constructor >
            [ let h := Fresh.in_goal @H in
              intros $h
            | solve_mut_exclusive full
            ]
      end.


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


    Ltac2 rec strip_exists h :=
      lazy_match! (Constr.type (hyp h)) with
      | ex ?body =>
          match (Constr.Unsafe.kind body) with
          | Constr.Unsafe.Lambda arg val =>
              let hh := hyp h in
              let arg_n := match Constr.Binder.name arg with
                           | None => Fresh.in_goal @x
                           | Some n => Fresh.in_goal n
                           end in
              destruct $hh as [$arg_n $h];
              strip_exists h
          | _ => Control.throw Init.Assertion_failure
          end
      | ?t =>
          t
      end.


    Lemma trans_invariant_SRPC_net_tau [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      SRPC_net N0 ->
      SRPC_net N1.

    Proof with (eattac).
      unfold SRPC_net.
      intros T Hsrpc0 n'.

      smash_eq n n'.
      2: specialize (Hsrpc0 n'); rewrite (NV_stay T) in Hsrpc0; auto.

      kill T.
      ltac1:(simpl_net).
      specialize (Hsrpc0 n) as [srpc0 Hsrpc0].
      destruct (NetMod.get n N0) as [I0 P0 O0].
      destruct S as [I1 P1 O1].

      assert (AnySRPC P0) as Hsrpc_any by (kill Hsrpc0; eattac).

      have (pq I0 P0 O0 =( Tau )=> pq I1 P1 O1).

      kill H > [destruct n0 as [n' [|]] | destruct n0 as [n' [|]] | ]; hsimpl in *.
      - (* Recv Q *)
        kill Hsrpc0.
        unshelve eapply SRPC_recv_Q in Hsrpc_any as [Hsrpc0 Hsrpc1]. 2: attac.
        apply (SRPC_inv Hsrpc0) in Hsrpc; subst.

        rename n' into c.
        exists (Work c).

        constructor; eauto with LTS; intros.
        + destruct (Name.eq_dec c0 c); subst; attac.
          eapply (Deq_Deq_swap _ HDeq) in H as [I'' [HDeq0' HDeq1']].
          attac.
        + eapply (Deq_Deq_swap _ HDeq) in H as [I'' [HDeq0' HDeq1']].
          attac.
        + apply In_Deq in H.
          hsimpl in H.
          eapply (Deq_Deq_swap _ HDeq) in H.
          hsimpl in H.
          apply Deq_In in H.
          eapply H_R_in_lock in H.
          attac.
        + apply H_Q_out_lock in H as [c' H].
          bullshit.
        + eapply (Deq_incl HDeq) in H.
          bullshit.
        + bullshit.
        + kill H.
        + consider (exists v, List.In (c, Q, v) I0) by eattac.
          assert (proc_client c (cont v)) by eattac.
          assert (forall c', proc_client c' (cont v) -> c = c').
          {
            intros * PC.
            destruct PC as [srpcb Hsrpc'].
            apply (SRPC_inv Hsrpc1) in Hsrpc'.
            kill Hsrpc1.
          }

          specialize (H_query_uniq c0).
          destruct_mut_exclusive @H_query_uniq.

          solve_mut_exclusive true;
            try (ltac1:(replace c0 with c in * by auto));
            repeat (match! goal with
                    | [h : exists _, _ |- _] => strip_exists h; ()
                    | [h : List.In _ I1 |- _] =>
                        apply (Deq_incl HDeq) in $h; bullshit
                    end); bullshit.

      - (* Recv R *)
        kill Hsrpc0.
        unshelve eapply SRPC_recv_R in Hsrpc_any as [c [Hsrpc0 Hsrpc1]]. 2: attac.
        apply (SRPC_inv Hsrpc0) in Hsrpc; subst.

        rename n' into s.
        exists (Work c).

        constructor; eauto with LTS; intros.
        + eapply (Deq_Deq_swap _ HDeq) in H.
          attac.
        + eapply (Deq_Deq_swap _ HDeq) in H.
          attac.
        + destruct (Name.eq_dec s0 s); subst.
          1: bullshit.
          apply (Deq_incl HDeq) in H.
          eapply H_R_in_lock in H as [? ?].
          kill H.
        + assert (s0 = s) by (eapply H_Q_out_lock in H as [? ?]; kill H). subst.
          apply Deq_In in HDeq.
          bullshit.
        + bullshit.
        + kill H.
        + specialize (H_query_uniq c0).

          assert (forall c' v, List.In (c', Q, v) I1 -> List.In (c', Q, v) I0)
            by (intros; eapply Deq_incl; eauto).
          assert (proc_client c (cont v)) by eattac.
          assert (proc_client c (PRecv h)) by eattac.
          assert (forall c', proc_client c' (cont v) -> c = c').
          {
            intros * PC.
            destruct PC as [srpcb Hsrpc'].
            apply (SRPC_inv Hsrpc1) in Hsrpc'.
            kill Hsrpc1.
          }
          destruct_mut_exclusive @H_query_uniq.

          solve_mut_exclusive true;
            try (ltac1:(replace c0 with c in * by auto));
            repeat (match! goal with
                    | [h : exists _, _ |- _] => strip_exists h; ()
                    | [h : List.In _ I1 |- _] => apply H in $h
                    end); bullshit.
      - (* Send Q *)
        kill Hsrpc0.
        eapply SRPC_send_Q in Hsrpc_any as [c [Hsrpc0 Hsrpc1]]. 2: attac.
        apply (SRPC_inv Hsrpc0) in Hsrpc; subst.

        rename n' into s.
        exists (Lock c s).

        constructor; eauto with LTS; intros.
        + eapply H_R_in_lock in H as [? ?].
          kill H.
        + apply in_app_or in H as [H|H].
          * apply H_Q_out_lock in H as [? ?].
            kill H.
          * kill H.
            kill H0.
            eattac.
        + intros HIn.
          rewrite removelast_last in HIn.
          apply H_Q_out_lock in HIn as [? ?].
          kill H.
        + assert (forall v0, ~ List.In (c0, R, v0) [(s, Q, v)]) by (intros v0' Hx; kill Hx).
          specialize (Deq_app_or_l H (H1 v0)) as [O'' [HDeq' HEq']].
          subst.
          intros HIn.
          apply in_app_or in HIn as [HIn|HIn]; bullshit.
        + apply H_R_in_lock in H as [? ?].
          kill H.
        + intros Hx.
          apply H_R_in_lock in Hx as [? ?].
          kill H1.
        + kill H.
          eattac.
        + specialize (H_query_uniq c0).
          remember (O0 ++ [(s, Q, v)]) as O1.
          assert (forall c' v', List.In (c', R, v') O0 -> List.In (c', R, v') O1) by attac.
          assert (forall c' v', List.In (c', R, v') O1 -> List.In (c', R, v') O0)
            by (intros; subst; apply in_app_or in H1; kill H1; eauto; kill H2).
          assert (proc_client c P1) by eattac.
          assert (proc_client c (PSend (s, Q) v P1)) by eattac.
          assert (forall c', proc_client c' P1 -> c = c').
          {
            intros * PC.
            destruct PC as [srpcb Hsrpc'].
            apply (SRPC_inv Hsrpc1) in Hsrpc'.
            kill Hsrpc1.
          }
          destruct_mut_exclusive @H_query_uniq.

          solve_mut_exclusive true;
            try (ltac1:(replace c0 with c in * by auto));
            repeat (match! goal with
                    | [h : exists _, _ |- _] => strip_exists h; ()
                    | [h : List.In _ I1 |- _] => apply H in $h
                    end); doubt.

      - (* Send R *)
        kill Hsrpc0.
        unshelve eapply SRPC_send_R in Hsrpc_any as [Hsrpc0 Hsrpc1]. 2: attac.
        apply (SRPC_inv Hsrpc0) in Hsrpc; subst.

        rename n' into c.
        exists Free.

        constructor; eauto with LTS; intros.
        + eapply H_R_in_lock in H as [? ?].
          kill H.
        + apply in_app_or in H as [H|H].
          * apply H_Q_out_lock in H as [? ?].
            kill H.
          * kill H.
        + intros HIn.
          rewrite removelast_last in HIn.
          apply H_Q_out_lock in HIn as [? ?].
          kill H.
        + destruct (Name.eq_dec c0 c); subst.
          * assert (forall v, ~ List.In (c, R, v) O0).
            {
              intros.
              specialize (H_query_uniq c).
              destruct_mut_exclusive @H_query_uniq.
              intros Hx.
              eattac.
            }
            specialize (Deq_app_or_r H (H1 _)) as [O'' [HDeq' HEq]].
            subst.
            kill HDeq'.
            hsimpl in *.
            eattac.
          * assert (forall v0, ~ List.In (c0, R, v0) [(c, R, v)]) by (intros v'' HIn'; kill HIn').
            specialize (Deq_app_or_l H (H1 _)) as [O'' [HDeq' HEq]].
            subst.
            eapply (H_R_out_uniq) in HDeq'.
            specialize (H1 v').
            intros Hx.
            apply in_app_or in Hx as [?|?]; attac.
        + apply H_R_in_lock in H as [? ?].
          kill H.
        + intros Hx.
          apply H_R_in_lock in Hx as [? ?].
          kill H1.
        + kill H.
        + remember (O0 ++ [(c, R, v)]) as O1.
          assert (forall c' v', List.In (c', R, v') O0 -> List.In (c', R, v') O1) by (intros; subst; eattac).
          assert (proc_client c (PSend (c, R) v P1)) by eattac.
          assert (forall c', ~ proc_client c' P1)
            by (intros c' Hc; kill Hc; apply (SRPC_inv Hsrpc1) in H2; bullshit).
          specialize (H_query_uniq c0) as HM.
          destruct_mut_exclusive @HM.

          solve_mut_exclusive true;
            try (ltac1:(replace c0 with c in * by auto));
            repeat (match! goal with
                    | [h : exists _, _ |- _] => strip_exists h; ()
                    | [h : List.In _ I1 |- _] => apply H in $h
                    end); doubt.

          * assert (forall v, ~ List.In (c0, R, v) O0) by attac 1.
            apply in_app_or in H10 as [?|?]; attac.
          * specialize (H_query_uniq c).
            destruct_mut_exclusive @H_query_uniq.
            apply in_app_or in H8 as [?|?]; attac.
      - (* Tau *)
        kill Hsrpc0.
        unshelve eapply SRPC_tau in Hsrpc_any as [c [Hsrpc0 Hsrpc1]]. 2: attac.
        apply (SRPC_inv Hsrpc0) in Hsrpc; subst.

        exists (Work c).
        constructor; eattac.

        specialize (H_query_uniq c0).
        destruct_mut_exclusive @H_query_uniq.

        assert (forall c', proc_client c' P1 -> c = c').
        {
          intros * PC.
          destruct PC as [srpcb Hsrpc'].
          apply (SRPC_inv Hsrpc1) in Hsrpc'.
          kill Hsrpc1.
        }

        solve_mut_exclusive true;
          try (ltac1:(replace c0 with c in * by auto));
          Control.enter (
              fun () => match! goal with
                    | [h : exists _, _ |- _] => strip_exists h; bullshit
                    end
            ).

        Unshelve. bullshit. bullshit. bullshit. bullshit. bullshit.
    Qed.


    Lemma out_flush_proc [N0 N1 path] n :
      Forall (fun a => match a with NComm n' _ _ _ => True | _ => False end) path ->
      (N0 =[path]=> N1) ->
      match NetMod.get n N0, NetMod.get n N1 with pq _ P0 _, pq _ P1 _ => P0 = P1 end.

    Proof.
      generalize dependent N0.
      induction path; intros.
      - kill H0.
        destruct (NetMod.get n N1).
        auto.
      - hsimpl in *.
        destruct a; kill H.

        ehave (_ =[path]=> N1).
        specialize (IHpath N2 ltac2:(attac) ltac2:(attac)).

        enough (match NetMod.get n N0 with
                | pq _ P0 _ => match NetMod.get n N2 with
                              | pq _ P1 _ => P0 = P1
                              end
                end
               ).
        {
          destruct (NetMod.get n N0).
          destruct (NetMod.get n N2).
          attac.
        }

        clear IHpath.


        kill H0. hsimpl in *.
        destruct (NetMod.get n N0) eqn:?, (NetMod.get n N1) eqn:?.
        destruct (NetMod.get n0 N0) eqn:?, (NetMod.get n0 N1) eqn:?.
        destruct (NetMod.get n1 N0) eqn:?, (NetMod.get n1 N1) eqn:?.


        smash_eq n0 n1 n; hsimpl in *.
        all: ltac1:(autorewrite with LTS in * ); attac.
    Qed.


    Lemma out_flush_len [N0 N1 n path L] :
      Forall (fun a => match a with NComm n' _ _ _ => n = n' | _ => False end) path ->
      (N0 =[path]=> N1) ->
      net_lock N1 L n ->
      length path = match NetMod.get n N0 with pq _ _ O0 => length O0 end.

    Proof.
      generalize dependent N0.
      induction path; intros.
      - kill H0.
        kill H1.
        auto.
      - hsimpl in *.
        destruct a; kill H.
        specialize (IHpath _ H3 H2 H1).
        rewrite IHpath.
        kill H0.

        hsimpl in *.
        smash_eq n0 n1; hsimpl in *; attac.
        + consider (NetMod.get n0 N0 =(_)=> _); attac.
        + consider (NetMod.get n0 N0 =(_)=> _); attac.
    Qed.


    Lemma net_sane_handler_uniq [N n0 n1 n1'] :
      net_sane N ->
      pq_client n0 (NetMod.get n1 N) ->
      pq_client n0 (NetMod.get n1' N) ->
      n1' = n1.

    Proof.
      intros HNs Hc1 Hc1'.
      kill HNs.

      assert (forall n, AnySRPC_pq (NetMod.get n N)) as Hsrpc_N by eattac.

      eapply H_lock_complete in Hc1 as HL.
      eapply H_lock_complete in Hc1' as HL'.

      apply lock_singleton in HL; eauto.
      eapply lock_SRPC_Lock_pq in HL as [c Hsrpc]; eauto.

      apply lock_singleton in HL'; eauto.
      eapply lock_SRPC_Lock_pq in HL' as [c' Hsrpc']; eauto.

      destruct (NetMod.get n0 N) as [I0 P0 O0] eqn:HEq0.

      apply (SRPC_inv Hsrpc) in Hsrpc'.
      kill Hsrpc'.
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

      kill T; kill Hc.
      - destruct n.
        destruct t0.
        + specialize (SRPC_recv_Q H ltac:(attac)) as [Hsrpc0 Hsrpc1].
          smash_eq c n; eauto with LTS.

          enough (exists v', List.In (c, Q, v') I1) by eattac.
          exists v0.
          unshelve (eapply (Deq_neq_In _ HDeq)); eattac.
        + enough (exists v', List.In (c, Q, v') I1) by eattac.
          exists v0.
          unshelve (eapply (Deq_neq_In _ HDeq)); eattac.
      - destruct n.
        destruct t0.
        + specialize (SRPC_recv_Q H ltac:(attac)) as [Hsrpc0 Hsrpc1].
          smash_eq c n; eauto with LTS.
          hsimpl in *.
          consider (proc_client c (PRecv h)).
          absurd (Free = Busy _); attac.

        + have (P0 =( Recv (n, R) v )=> P1).
          hsimpl in *.
          consider (proc_client _ _).
          enough (proc_client c (cont v)) by attac.
          econstructor.
          enough (SRPC (Work c) (cont v)) by attac.
          consider (SRPC _ (PRecv _)) by attac.
          eapply HRecv; eattac.
      - attac.
      - attac.
      - destruct n.
        destruct t0.
        + specialize (SRPC_send_Q H ltac:(attac)) as [c' [Hsrpc0 Hsrpc1]].
          assert (proc_client c' P0) by attac.
          consider (c' = c); attac.
        + assert (proc_client n P0).
          {
            specialize (SRPC_send_R H ltac:(attac)) as [Hsrpc0 Hsrpc1].
            attac.
          }
          assert (n = c) by eattac.
          subst.
          eattac.
      - eattac.
      - eattac.
      - specialize (SRPC_tau H ltac:(attac)) as [c' [Hsrpc0 Hsrpc1]].
        have (proc_client c' P0).
        have (proc_client c P0).
        consider (c' = c) by eattac.
        attac.
      - eattac.
    Qed.


    Theorem SRPC_net_no_self_reply [N0 N1 : PNet] [n0 n1 v] :
      net_sane N0 ->
      (N0 =(NComm n0 n1 R v)=> N1) ->
      n0 <> n1.

    Proof.
      intros Hs0 T.

      kill T.
      rename H into T_s.
      rename H0 into T_r.

      kill T_s; rename H into T_s.
      kill T_r; rename H into T_r.

      destruct (NetMod.get n0 N0) as [Is0 Ps0 Os0] eqn:HEqNs0.
      destruct S as [Is1 Ps1 Os1] eqn:HEqNs1.
      destruct S0 as [Ir1 Pr1 Or1] eqn:HEqNr1.

      intros HEq.
      subst.

      assert (exists N1 a, (N0 =(a)=> N1) /\ NetMod.get n1 N1 = pq Ir1 Pr1 Or1) as (N1 & a & TN & HEqN1).
      {
        exists (NetMod.put n1 (pq Ir1 Pr1 Or1) (NetMod.put n1 (pq Is1 Ps1 Os1) N0)).
        exists (NComm n1 n1 R v).
        split.
        - ltac1:(simpl_net).
          econstructor; constructor; eauto.
          rewrite HEqNs0.
          eauto.
          ltac1:(simpl_net).
          auto.
        - ltac1:(simpl_net).
          auto.
          ltac1:(simpl_net).
          auto.
      }

      assert (net_lock_on N0 n1 n1) as HL.
      {
        kill T_s.
        kill T_r.
        enough (pq_client n1 (NetMod.get n1 N0)) as Hc by (kill Hs0; auto).
        ltac1:(simpl_net).
        rewrite HEqNs0.
        econstructor 3.
        attac.
      }
      ltac1:(simpl_net).
      kill Hs0.
      specialize (@dep_self_deadset N0 ltac:(attac) n1 ltac:(attac)) as [DS [HInDS HDS]].

      specialize (deadset_stay1 HDS HInDS TN HEqNs0) as HEq.
      hsimpl in HEq.
      compat_hsimpl in *.

      clear - T_s0. induction O1; bullshit. (* TODO .... *)
    Qed.


    Lemma trans_invariant_net_sane_tau [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      net_sane N0 ->
      net_sane N1.

    Proof.
      intros T HNs0.
      kill HNs0.
      constructor.
      - apply trans_invariant_SRPC_net_tau in T; eauto.
      - intros n0 n1 HL.
        (* n0 is locked on n1 after someone's Tau. Whoever that was, the lock must not be new *)

        assert (net_lock_on N0 n0 n1) as HL0.
        {
          smash_eq n0 n.
          - kill T.
            unfold net_lock_on in *.
            unfold net_lock in *.
          (* hsimpl in HL. TODO FIXME NOT WORKING  *)
            ltac1:(simpl_net).
            hsimpl in HL.
            assert (AnySRPC_pq &S) as Hsrpc_S by eauto with LTS.
            edestruct (SRPC_pq_get_lock Hsrpc_S HL0); eauto with LTS.
            assert (x = n1).
            {
              specialize (pq_lock_incl HL0 H0) as Hincl.
              apply Hincl in HL.
              kill HL.
            }
            subst.

            hsimpl in HL0.
            have (AnySRPC_pq (NetMod.get n0 N0)).
            exists [n1].
            split; eattac.
            destruct (NetMod.get n0 N0) as [I P O].
            kill HL0.
            assert (Decisive P0) by attac.
            kill H; try (destruct n); try (destruct t0).
            + edestruct (SRPC_recv_Q) as [Hsrpc0 Hsrpc1]; re_have (eauto with LTS).
              hsimpl in *.
              consider (exists c, SRPC (Lock c n1) (cont v)) by (apply lock_SRPC_Lock; attac).
              absurd (Lock c n1 = Work n).
              intros Hx; kill Hx.
              eapply SRPC_inv; eattac.
            + edestruct (SRPC_recv_R) as [s [Hsrpc0 Hsrpc1]]; re_have (eauto with LTS).
              hsimpl in *.
              consider (exists c, SRPC (Lock c n1) (cont v)) by (apply lock_SRPC_Lock; attac).
              absurd (Lock c n1 = Work s).
              intros Hx; kill Hx.
              eapply SRPC_inv; eattac.
            + bullshit.
            + bullshit.
            + edestruct (SRPC_tau) as [s [Hsrpc0 Hsrpc1]]; attac.
              hsimpl in *.
              consider (exists c, SRPC (Lock c n1) P0) by (apply lock_SRPC_Lock; attac).
              absurd (Lock c n1 = Work s).
              intros Hx; kill Hx.
              eapply SRPC_inv; eattac.
          - unfold net_lock_on in *.
            unfold net_lock in *.
            rewrite (NV_stay T); auto.
        }

        apply H_lock_sound in HL0.

        smash_eq n n1.
        + kill T.
          ltac1:(simpl_net).
          destruct (NetMod.get n N0) eqn:HE.
          eapply pq_client_invariant_tau; eattac.
        + replace (NetMod.get n1 N1) with (NetMod.get n1 N0) by (rewrite (NV_stay T) in *; eauto).
          auto.

      - intros n0 n1 HL1.

        enough (pq_client n0 (NetMod.get n1 N0)) as HL0.
        {
          apply H_lock_complete in HL0.
          unfold net_lock_on in *.

          assert (n <> n0) as HNEq.
          {
            intros HEq; subst.
            hsimpl in HL0.
            unfold net_lock in HL2.
            kill T.
            specialize (pq_lock_recv HL2 H) as bs.
            bullshit.
          }

          assert (NetMod.get n0 N1 = NetMod.get n0 N0) by (rewrite (NV_stay T) in *; eauto).
          unfold net_lock in *.
          rewrite H in *.
          auto.
        }

        smash_eq n1 n.
        + kill T.
          ltac1:(simpl_net).
          assert (AnySRPC_pq (NetMod.get n1 N0)) as Hsrpc_0 by attac.
          assert (AnySRPC_pq &S) as Hsrpc_1 by attac.
          kill HL1; kill H; eattac; try (destruct n); try (destruct t0).
          * apply Deq_split in HDeq.
            hsimpl in HDeq.
            econstructor 1 with (v:=v).
            apply in_app_or in H0 as [?|?]; eattac.
          * apply Deq_split in HDeq.
            hsimpl in HDeq.
            econstructor 1 with (v:=v).
            apply in_app_or in H0 as [?|?]; eattac.
          * smash_eq n0 n.
            1: eattac.
            econstructor 1 with (v:=v).
            assert ((n, Q) <> (n0, Q)) as HNEq by bullshit.
            edestruct (SRPC_recv_Q) as [Hsrpc0 Hsrpc1]; eattac.
            kill H0.
            apply (SRPC_inv Hsrpc1) in H.
            kill H.
          * edestruct (SRPC_recv_R) as [c [Hsrpc0 Hsrpc1]]; eattac.
            kill H0.
            apply (SRPC_inv Hsrpc1) in H.
            kill H.
            ltac1:(dependent destruction H3).
            constructor. econstructor. attac.
          * edestruct (SRPC_send_Q) as [c [Hsrpc0 Hsrpc1]]; eattac.
            kill H0.
            apply (SRPC_inv Hsrpc1) in H.
            kill H.
            eattac.
          * edestruct (SRPC_send_R) as [Hsrpc0 Hsrpc1]; eattac.
            kill H0.
            apply (SRPC_inv Hsrpc1) in H.
            kill H.
          * edestruct (SRPC_tau) as [c [Hsrpc0 Hsrpc1]]; eattac.
            kill H0.
            apply (SRPC_inv Hsrpc1) in H.
            kill H.
            eattac.
          * hsimpl in *.
            econstructor 3.
            apply in_app_or in H0 as [?|?]; eattac.
          * edestruct (SRPC_send_R) as [Hsrpc0 Hsrpc1]; eattac.
            hsimpl in *.
            apply in_app_or in H0 as [?|?]; eattac.
        + assert (NetMod.get n1 N1 = NetMod.get n1 N0) by (rewrite (NV_stay T) in *; eauto).
          unfold net_lock_on in *.
          unfold net_lock in *.
          rewrite H in *.
          auto.
    Qed.

    Lemma trans_invariant_SRPC_net_comm [n0 n1 t v] [N0 N1 : PNet] :
      (N0 =(NComm n0 n1 t v)=> N1) ->
      net_sane N0 ->
      SRPC_net N1.

    Proof using Type.
      unfold SRPC_net.
      intros T Hs0 n'.

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

      all: assert (exists srpc, SRPC_pq_in_net srpc (NetMod.get n0 N0)) as Hsrpc_s by auto.
      2,3: assert (exists srpc, SRPC_pq_in_net srpc (NetMod.get n1 N0)) as Hsrpc_r by auto.

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
          eapply SRPC_net_get_lock_In in HL; eauto with LTS.
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
        eapply SRPC_net_no_self_reply; eattac.

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
          eapply SRPC_net_get_lock_In in HL; eauto with LTS.
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
          eapply SRPC_net_get_lock_In in HL; eauto with LTS.
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
            eapply SRPC_net_get_lock_In in HL; eauto with LTS.
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


    Theorem SRPC_net_reply_lock [N0 N1 : PNet] [n0 n1 v] :
      net_sane N0 ->
      (N0 =(NComm n0 n1 R v)=> N1) ->
      net_lock_on N0 n1 n0.

    Proof.
      intros Hs0 T.

      assert (n0 <> n1) as HNEq by (eauto using SRPC_net_no_self_reply with LTS).

      kill Hs0.

      kill T.
      apply H_lock_complete.
      compat_hsimpl in *.
      rewrite `(NetMod.get n0 N0 = _).
      attac.
    Qed.


    Theorem SRPC_net_query_new_lock [N0 N1 : PNet] [n0 n1 v] :
      net_sane N0 ->
      (N0 =(NComm n0 n1 Q v)=> N1) ->
      net_lock_on N1 n0 n1.

    Proof.
      intros Hs0 T.

      kill Hs0.
      kill T.
      compat_hsimpl in *.

      specialize (H_Sane_SRPC n0) as [srpc Hsrpc].
      kill Hsrpc.
      hsimpl in *.
      edestruct H_Q_out_lock as [c HEq].
      1: left; eauto.
      subst.
      exists [n1].
      split.
      1: attac.

      unfold net_lock in *.

      assert (O1 = []).
      {
        destruct O1; auto.
        simpl in H_Q_out_last.
        exfalso.
        eapply H_Q_out_last.
        eauto.
      }
      subst.

      smash_eq n0 n1; hsimpl in *; hsimpl in |- *.
      - constructor; attac.
        + apply SRPC_Decisive. eattac.
        + apply in_app_or in H0 as [?|?].
          2: kill H.
          eapply H_Q_R; eattac.
      - constructor.
        + eapply SRPC_Decisive. eattac.
        + eapply SRPC_Lock_lock; eattac.
        + intros.
          kill H.
          eapply H_Q_R.
          eattac.
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

      assert (SRPC_net N1) as HsrpcN1
          by (eauto using trans_invariant_SRPC_net_comm).

      destruct t.
      - (* Query *)

        assert (net_lock_on N1 n0 n1) as HL
            by eauto using SRPC_net_query_new_lock with LTS.

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

        assert (n0 <> n1) by (eapply SRPC_net_no_self_reply; eauto).

        assert (net_lock_on N0 n1 n0) as HL
            by eauto using SRPC_net_reply_lock with LTS.

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

              assert (SRPC_pq_in_net (Lock c' s) (pq I1 P1 [(n1, R, v)])) as Hsrpc'.
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
               assert (SRPC_net N0) as HsrpcN0 by eauto with LTS.
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

  End NetSRPC.

End Locks.
