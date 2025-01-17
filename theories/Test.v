Close Scope nat.

From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Bool.
From Coq Require Import Structures.Equalities.

Module Empty. End Empty. (* `<+` identity *)


Module Type Singleton.
  Parameter Inline t : Set.
  Parameter one : forall x0 x1 : t, x0 = x1.
End Singleton.


Module Type CHANNEL_CONF.
  Parameter Inline Val : Set.

  Declare Module Name : Singleton.
  Declare Module Tag : Singleton.
End CHANNEL_CONF.

Module Type CHANNEL_PARAMS := CHANNEL_CONF.

Module Type CHANNEL_F(Import Params : CHANNEL_PARAMS).
  #[global] Definition Name := Name.t.
  #[global] Definition Tag := Tag.t.

  #[global] Definition NChan : Set := (Name * Tag)%type.
  #[global] Hint Transparent NChan : core.

  Fact NChan_eq : forall (n0 n1 : NChan), n0 = n1.
  intros. destruct n0, n1. f_equal; eauto using Name.one, Tag.one. Qed.
End CHANNEL_F.

Module Type CHANNEL := CHANNEL_PARAMS <+ CHANNEL_F.


Module Type QUE_CONF.
  Include CHANNEL_CONF.
End QUE_CONF.

Module Type QUE_PARAMS(Conf : QUE_CONF).
  Declare Module Export Channel : CHANNEL_F(Conf).
End QUE_PARAMS.

Module Type QUE_F(Import Conf : QUE_CONF)(Import Params : QUE_PARAMS(Conf)).
  Inductive Que := Q (nc : NChan).
  Lemma Que_eq : forall q0 q1 : Que, q0 = q1.
    intros. destruct q0, q1; f_equal; auto using NChan_eq. Qed.
End QUE_F.

Module Type QUE(Conf : QUE_CONF) := Conf <+ QUE_PARAMS <+ QUE_F.


Module Type PROC_CONF.
  Include QUE_CONF.
End PROC_CONF.

Module Type PROC_PARAMS(Conf : PROC_CONF).
  Declare Module Export Que : QUE(Conf).
End PROC_PARAMS.

Module Type PROC_F(Import Conf : PROC_CONF)(Import Params : PROC_PARAMS(Conf)).
  Inductive Proc : Set := P (Q : Que).

  Lemma Proc_eq : forall p0 p1 : Proc, p0 = p1.
    intros. destruct p0, p1. f_equal. apply Que_eq. Qed.
End PROC_F.

Module Type PROC(Conf : PROC_CONF) := Conf <+ PROC_PARAMS <+ PROC_F.


Module Type MON_CONF.
  Parameter Inline Msg : Set.
  Axiom Msg_eq : forall m0 m1 : Msg, m0 = m1.
End MON_CONF.

Module Type MON_PARAMS(Conf : MON_CONF).
  Declare Module Export ProcConf : PROC_CONF.
  Declare Module Export Proc : PROC(ProcConf).
End MON_PARAMS.

Module Type MON_F(Import Conf : MON_CONF)(Import Params : MON_PARAMS(Conf)).
  Inductive Mon := M (m : Msg) (p : Proc).
  Lemma Mon_eq : forall m0 m1 : Mon, m0 = m1.
    intros. destruct m0, m1; f_equal; eauto using Msg_eq, Proc_eq. Qed.
End MON_F.

Module Type MON(Conf : MON_CONF) := Conf <+ MON_PARAMS <+ MON_F.


Module Type NET_MOD(Name : Singleton).
  Parameter t : Name.t -> Type -> Type.

  Section Node.
    Context {Node : Type}.
    Context {n : Name.t}.
    Parameter Node_eq : forall x0 x1 : t n Node, x0 = x1.
    Parameter get : t n Node -> Node.
    Parameter put : Node -> t n Node.
  End Node.
End NET_MOD.


Module Type NET_CONF.
  Include CHANNEL_PARAMS.
  Declare Module NetMod : NET_MOD(Name).
End NET_CONF.

Module Type NET_PARAMS(Conf : NET_CONF).
End NET_PARAMS.

Module Type NET_F(Import Conf : NET_CONF)(Import Params : NET_PARAMS(Conf)).
  Section General.
    Context [Node : Set].
    Inductive N := n (n : Name.t) (x : NetMod.t n Node).
    Lemma N_eq : forall (x0 x1 : N), x0 = x1.
      intros. destruct x0, x1. assert (n0 = n1). eapply Name.one. subst.
      f_equal. apply NetMod.Node_eq. Qed.
  End General.
End NET_F.

Module Type NET(Conf : NET_CONF) := Conf <+ NET_PARAMS <+ NET_F.

Module NetTactics(Conf : NET_CONF)(Import Net : NET(Conf)).
  Ltac net_tac := idtac.
End NetTactics.


Inductive Tag_ := T.

Module Tag_ <: Singleton.
  Definition t := Tag_.
  Lemma one : forall x0 x1 : t, x0 = x1. intros. destruct x0, x1. auto. Qed.
End Tag_.

Module Type PROC_CONF_WITH_TAG := PROC_CONF with Module Tag := Tag_.
Module Type PROC_WITH_TAG(Conf : PROC_CONF_WITH_TAG) := PROC(Conf).


Module Type LOCKS_CONF := PROC_CONF_WITH_TAG.

Module Type LOCKS_PARAMS(Conf : LOCKS_CONF).
  Declare Module Export Proc : PROC(Conf).
End LOCKS_PARAMS.

Require Import Coq.Program.Equality.
Module Type LOCKS_F(Import Conf : LOCKS_CONF)(Import Params : LOCKS_PARAMS(Conf)).
  Inductive L : Tag -> Set := l (p : Proc) : L T.
  Lemma L_eq : forall t (l0 l1 : L t), l0 = l1.
    intros. inversion l0. subst. destruct l0. dependent destruction l1.
    f_equal. eapply Proc_eq.
  Qed.
End LOCKS_F.

Module Type LOCKS(Conf : LOCKS_CONF) := Conf <+ LOCKS_PARAMS <+ LOCKS_F.


Module Type NET_CONF_WITH_TAG := NET_CONF with Module Tag := Tag_.

(* Module Type NET_WITH_TAG(Conf : NET_CONF_WITH_TAG) := NET(Conf). *)


Module Type NET_LOCKS_CONF := NET_CONF_WITH_TAG.
Module Type NET_LOCKS_PARAMS(Conf : NET_LOCKS_CONF).
  Declare Module Export Locks : LOCKS(Conf).
  Declare Module Export Net : NET(Conf).
End NET_LOCKS_PARAMS.

Module Type NET_LOCKS_F(Import Conf : NET_LOCKS_CONF)(Import Params : NET_LOCKS_PARAMS(Conf)).
  Inductive NL := nl (n : @N Tag) (l : L T).

  Lemma NL_eq : forall n0 n1 : NL, n0 = n1.
    intros. destruct n0, n1. f_equal. apply N_eq. apply L_eq. Qed.

  Module Type LOCKS_UNIQ.
    Section Sec.
      Variable noname : forall (n : Name), False.
      Lemma uniq : forall x : NL, False.
        intros. destruct x. destruct l0. destruct p. destruct Q0. destruct nc. auto. Qed.
    End Sec.

  End LOCKS_UNIQ.
End NET_LOCKS_F.

Module Type NET_LOCKS(Conf : NET_LOCKS_CONF) := Conf <+ NET_LOCKS_PARAMS <+ NET_LOCKS_F.


Module Type SRPC_CONF := LOCKS_CONF.

Module Type SRPC_PARAMS(Conf : SRPC_CONF).
  Declare Module Export Locks : LOCKS(Conf).
End SRPC_PARAMS.

Module Type SRPC_F(Import Conf : SRPC_CONF)(Import Params : SRPC_PARAMS(Conf)).
  Inductive S := s (l : L T).
  Lemma S_eq : forall s0 s1 : S, s0 = s1.
    intros. destruct s0, s1. f_equal. apply L_eq. Qed.
End SRPC_F.

Module Type SRPC(Conf : SRPC_CONF) := Conf <+ SRPC_PARAMS <+ SRPC_F.


Module Type SRPC_NET_CONF := NET_LOCKS_CONF.
Module Type SRPC_NET_PARAMS(Conf : SRPC_NET_CONF).
  Declare Module Export Srpc : SRPC(Conf).
  Declare Module Export NetLocks : NET_LOCKS(Conf).
End SRPC_NET_PARAMS.

Module Type SRPC_NET_F(Import Conf : SRPC_NET_CONF)(Import Params : SRPC_NET_PARAMS(Conf)).
  Inductive SN := sn (n : @N S).
  Definition noname : forall (n : Name), False. Admitted.
End SRPC_NET_F.

Module Type SRPC_NET(Conf : SRPC_NET_CONF) := Conf <+ SRPC_NET_PARAMS <+ SRPC_NET_F.


Module Type TRANSP_CONF.
  Include NET_LOCKS_CONF.
  Include MON_CONF.
End TRANSP_CONF.

Module Type TRANSP_PARAMS(Conf : TRANSP_CONF).
  Declare Module Export Net : NET(Conf).
  Declare Module Export Mon : MON(Conf) with Module ProcConf := Conf.
End TRANSP_PARAMS.

Module Type TRANSP_F(Import Conf : TRANSP_CONF)(Import Params : TRANSP_PARAMS(Conf)).
  Definition Nm_to_Np (x : @N Mon) : @N Proc :=
    match x with n f nn => match NetMod.get nn with
                            (M a b) => n f (NetMod.put b)
                          end end.

End TRANSP_F.

Module Type TRANSP(Conf : TRANSP_CONF) := Conf <+ TRANSP_PARAMS <+ TRANSP_F.


Module MonConf(Import ChanConf : CHANNEL_CONF) <: MON_CONF.
  Definition Msg := Tag.t.
  Definition Msg_eq := Tag.one.
End MonConf.


Module Type DETECT_CONF.
  Include SRPC_NET_CONF.
  Include MON_CONF
    with Definition Msg := Tag.t
            with Definition Msg_eq := Tag.one.
End DETECT_CONF.

Module Type DETECT_PARAMS(Conf : DETECT_CONF).
  Declare Module Export SrpcNet : SRPC_NET(Conf).
  Declare Module Export Transp : TRANSP(Conf).
End DETECT_PARAMS.

Module Type COMPL_F(Import Conf : DETECT_CONF)(Import Params : DETECT_PARAMS(Conf)).
  Include LOCKS_UNIQ.
  Lemma im_uniq : forall x : NL, False.
    intros. apply noname.
    destruct x. destruct l0. destruct p. destruct Q0. destruct nc. apply n1. Qed.
  Lemma im_uniq' : forall x : Name, False.
    intros. apply noname. unfold Name in *. change ProcConf.Name.t with Locks.Proc.Que.Channel.Name in x.
    destruct x. destruct l0. destruct p. destruct Q0. destruct nc. apply n1. Qed.
