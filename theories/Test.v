(* -*- company-coq-local-symbols: (("pi" . ?π) ("btw" . ?🤔)); -*- *)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Std.

From Ltac2 Require Fresh.
From Ltac2 Require Import Control.
From Ltac2 Require Import Message.
From Ltac2 Require Import Std.
From Ltac2 Require Import Printf.

Import Ltac2.Notations.

From Coq Require Import String.
From Coq Require Import Strings.String.

Inductive MARK (s : string) (P : Prop) := MARK_ (p : P).


Definition CASE_lock_str : string. refine '("use tac" : string). Qed.
Lemma CASE_lock : forall (P : Prop), MARK CASE_lock_str P -> P. intros. inversion H. auto. Qed.

Definition CASE_remember_str : string. refine '("remember me" : string). Qed.
Lemma unmark_remember : forall (P : Prop), MARK CASE_remember_str P -> P. intros. inversion H. auto. Qed.
Lemma mark_remember : forall (P : Prop), P -> MARK CASE_remember_str P. intros. constructor. auto. Qed.

Ltac2 lock () := apply CASE_lock.
Ltac2 Notation "lock" := lock ().


Ltac2 unlock () :=
  lazy_match! goal with
  | [|- MARK CASE_lock_str _] => apply MARK_
  | [|-_] => ()
  end.

Ltac2 check_case (p : pattern) :=
  lazy_match! goal with
  | [h : MARK CASE_remember_str (?x = ?v) |- _] =>
      let matches := Pattern.matches p v in
      List.iter (fun (i, v) => pose ($i := $v)) matches;
      clear $h
  end.

Ltac2 Notation "case" p(pattern) := check_case p; unlock ().

Ltac2 switch (c : constr) :=
  lock;
  let t := Constr.type c in
  let i := Fresh.in_goal @LALALA in
  remember $t as XDDD eqn:$i;
  let ih := hyp i in
  try (rewrite $ih in *);
  apply mark_remember in LALALA.

Ltac2 Notation "switch" c(constr) := switch c.

Goal forall n m, n <= m -> False.
  intros.

  switch H.

  (* remember (n <= m) as XDDD eqn:LALALA. *)
  (* rewrite LALALA in *. *)
  (* apply mark_remember in LALALA. *)

  inversion H; subst.
  - case (?a <= ?a).
    assert (a = m) by auto.
    admit.
  - check_case (?a <= S ?b).
