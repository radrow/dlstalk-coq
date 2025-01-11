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
  - case (?a <= S ?b).
