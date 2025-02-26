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

Require Import DlStalk.Network.
Require Import DlStalk.SRPC.
Require Import DlStalk.Locks.
Require Import DlStalk.NetLocks.

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


Module Type SRPC_NET_CONF := NET_LOCKS_CONF.

Module Type SRPC_NET_PARAMS(Conf : SRPC_NET_CONF).
  Declare Module Export Srpc : SRPC(Conf).
  Declare Module Export NetLocks : NET_LOCKS(Conf) with Module Locks := Locks.
End SRPC_NET_PARAMS.

Module Type SRPC_NET_F(Import Conf : SRPC_NET_CONF)(Import Params : SRPC_NET_PARAMS(Conf)).
  Include LOCKS_UNIQ.
  Import SrpcDefs.

  (* TODO: these to Transp *)
  Lemma pq_I_net_inv : forall I P O n [N : PNet],
      NetMod.get n N = pq I P O ->
      pq_I (NetMod.get n N) = I.
  Proof. intros. rewrite H. attac. Qed.
  Lemma pq_P_net_inv : forall I P O n N,
      NetMod.get n N = pq I P O ->
      pq_P (NetMod.get n N) = P.
  Proof. intros. rewrite H. attac. Qed.
  Lemma pq_O_net_inv : forall I P O n N,
      NetMod.get n N = pq I P O ->
      pq_O (NetMod.get n N) = O.
  Proof. intros. rewrite H. attac. Qed.

  #[export] Hint Rewrite -> pq_I_net_inv pq_P_net_inv pq_O_net_inv using spank : LTS LTS_concl.
  #[export] Hint Resolve pq_I_net_inv pq_P_net_inv pq_O_net_inv : LTS LTS_concl.


    Definition SRPC_net N := forall n, AnySRPC_pq (NetMod.get n N).

    Lemma SRPC_net_get [N n] : SRPC_net N -> AnySRPC_pq (NetMod.get n N).
    Proof. attac. Qed.

    #[export] Hint Resolve SRPC_net_get : LTS.


    Lemma SRPC_net_lock [N n0 n1] :
      SRPC_net N ->
      net_lock_on N n0 n1 ->
      exists c, SRPC_pq (Lock c n1) (NetMod.get n0 N).

    Proof.
      unfold net_lock_on, net_lock.
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
      unfold lock_neq_nil_type, net_lock.
      intros.

      consider (exists s, pq_lock [s] (NetMod.get n N)) by eauto using SRPC_pq_get_lock.
      destruct L; doubt.

      assert (incl [s] []) by eauto using pq_lock_incl.
      bs (In s []).
    Qed.

    #[export] Hint Resolve SRPC_net_lock_neq_nil : LTS.


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
        + bs.
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


    Lemma SRPC_net_tau_no_lock [N0 N1 n0 n1 a] :
      SRPC_net N0 ->
      (N0 =(NTau n0 a)=> N1) ->
      ~ net_lock_on N1 n0 n1.

    Proof.
      intros.
      enough (forall L, ~ pq_lock L (NetMod.get n0 N1)) by (unfold net_lock_on, net_lock in *; intros ?; eattac); intros.

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
      - enough (forall L, ~ pq_lock L (NetMod.get n N1)) by (unfold net_lock_on, net_lock in *; intros ?; eattac); intros.
        eauto using SRPC_tau_no_lock_r with LTS.
      - unfold net_lock_on, net_lock in *.
        now rewrite `(NetMod.get n0 N0 = _) in *.
    Qed.


    Lemma SRPC_net_lock_on_tau_derive [N0 N1 n0 n1 n a] :
      SRPC_net N0 ->
      net_lock_on N1 n0 n1 ->
      (N0 =(NTau n a)=> N1) ->
      net_lock_on N0 n0 n1.

    Proof.
      intros.
      smash_eq n0 n.
      - bs (~ net_lock_on N1 n0 n1) by eauto using SRPC_net_tau_no_lock with LTS.
      - unfold net_lock_on, net_lock in *.
        replace (NetMod.get n0 N0) with (NetMod.get n0 N1); eattac.
    Qed.


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
      - bs (List.In (c, Q, v) (I00 ++ I01)) by eattac.
      - bs (List.In (c, Q, v') (I00 ++ I01)) by eattac.
      - bs (List.In (c, Q, v') (I00 ++ I01)) by eattac.
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
      - bs (List.In (s', R, v') (I00 ++ I01)) by eattac.
      - smash_eq s s'; attac.
        bs (List.In (s, R, v) (I00 ++ I01)) by eattac.
      - bs (List.In (s', R, v) (I00 ++ I01)) by eattac.
      - bs (List.In (s', R, v') (I00 ++ I01)) by eattac.
      - bs (List.In (s', R, v') (I00 ++ I01)) by eattac.
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
      - bs (List.In (s', R, v') (I00 ++ I01)) by eattac.
      - bs (List.In (s, R, v) (I00 ++ I01)) by eattac.
      - bs (List.In (s', R, v') (I00 ++ I01)) by eattac.
      - bs (List.In (s', R, v') (I00 ++ I01)) by eattac.
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
      bs.
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
      - bs (List.In (c, R, v) (O00 ++ O01)) by eattac.
      - bs (List.In (c, R, v') (O00 ++ O01)) by eattac.
      - bs (List.In (c, R, v') (O00 ++ O01)) by eattac.
    Qed.

    #[export] Hint Resolve SRPC_sane__Q_in_inv_l SRPC_sane__Q_in_inv_r SRPC_sane__R_in_inv_l SRPC_sane__R_in_inv_r SRPC_sane__R_out_inv_l SRPC_sane__R_out_inv_r : LTS.

    #[export] Hint Rewrite -> SRPC_sane__Q_in_inv_eq SRPC_sane__R_in_inv_eq_v SRPC_sane__R_in_inv_eq_s SRPC_sane__R_in_lock_inv SRPC_sane__Q_out_lock_inv SRPC_sane__Q_out_last_nil_inv SRPC_sane__Q_out_last_inv SRPC_sane__R_out_inv_eq_v using spank : LTS LTS_concl.


    (** If an SRPC service is locked after an action, then it's either a send (todo: from its output *)
  (*   queue) or a non-unlocking message *)
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

        destruct (NAME.eq_dec n' n); subst; auto.
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
      bs (In (s, R, v) (pq_I (pq I0 P0 (O1)))) by eattac.
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


    (* Lemma SRPC_sane_net_sane : forall N0, SRPC_sane_net N0 -> SRPC_net N0. *)
    (* Proof. repeat (intros ?). specialize (`(SRPC_sane_net _) n). attac. Qed. *)

    (* #[export] Hint Resolve SRPC_sane_net_sane : LTS. (* TODO is this needed? *) *)


    Lemma net_sane_SRPC_sane [N : PNet] : net_sane N -> SRPC_sane_net N.
    Proof. intros. kill H. intros ?. eauto with LTS. Qed.

    Lemma net_sane_SRPC [N : PNet] : net_sane N -> SRPC_net N.
    Proof. intros. kill H. intros ?. destruct (H_Sane_SRPC n). eauto with LTS. Qed.

    Lemma net_sane_lock_client [N S n0 n1] : net_sane N -> NetMod.get n1 N = S -> net_lock_on N n0 n1 -> pq_client n0 S.
    Proof. intros. kill H. auto. Qed.

    Lemma net_sane_client_lock [N S n0 n1] : net_sane N -> NetMod.get n1 N = S -> pq_client n0 S -> net_lock_on N n0 n1.
    Proof. intros. kill H. auto. Qed.


    #[export] Hint Resolve net_sane_SRPC_sane net_sane_SRPC net_sane_lock_client net_sane_client_lock : LTS.


    (* This is to allow the condition from LocksStatic be used in Immediate hints. *)
    Lemma net_sane_AnySRPC' (N : PNet) : net_sane N -> forall n, AnySRPC_pq (NetMod.get n N).
    Proof. intros. kill H. specialize (H_Sane_SRPC n) as [? H]. kill H. attac. Qed.
    #[export] Hint Extern 0 (forall n, AnySRPC_pq (NetMod.get n _)) => simple apply net_sane_AnySRPC'; eassumption : LTS.



    Section Inversions.
      (* These hints should not quadrate with SRPC_pq variants because net_sane does not expose *)
  (*     SRPC_sane *)

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
        List.In (c, R, v) O ->
        ~ proc_client c P.
      Proof. intros. kill H; specialize (H_Sane_SRPC n) as [srpc H]. rewrite H0 in *. intros ?. absurd (In (c, R, v) &O); eauto with LTS.
      Qed.

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
        bs (~ In (s, Q, v0) ((s, Q, v0) :: removelast (p :: O1))).
      - simpl in *.
        assert (~ ((c, &t, v) = (c0, R, v') \/ In (c0, R, v') O1)) by eauto.
        eattac.
      - simpl in *.
        consider ( ~ ((c, &t, v) = (c0, R, v0) \/ In (c0, R, v0) O1)).
    Qed.


    Lemma net_sane_send_R_sender_no_lock [N0 N1 n0 n1 n v] :
      SRPC_sane_net N0 ->
      (N0 =(NComm n0 n1 R v)=> N1) ->
      ~ net_lock_on N1 n0 n.

    Proof.
      intros.
      remember (NComm n0 n1 R v) as na.
      induction `(N0 =(na)=> N1) using (net_ind_of n0); hsimpl in *; doubt.
      - enough (forall L, ~ pq_lock L (NetMod.get n1 N1)) by (unfold net_lock_on, net_lock in *; intros ?; eattac); intros.
        enough (~ pq_lock L S0) by eauto using pq_recv_no_new_lock.
        consider (exists srpc, SRPC_sane srpc (NetMod.get n1 N0)) by eauto with LTS.
        eauto using SRPC_sane_send_R_no_lock_r with LTS.
      - enough (forall L, ~ pq_lock L (NetMod.get n0 N1)) by (unfold net_lock_on, net_lock in *; intros ?; eattac); intros.
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
      1: { eauto using net_sane_send_R_sender_no_lock with LTS. }

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

      enough (net_lock_on N0 n n) by bs (n <> n) by eauto using net_lock_on_no_send.

      enough (pq_client n (NetMod.get n N0)) by attac.

      consider (_ =(NComm n n R v)=> _); compat_hsimpl in *; attac.
    Qed.


    Lemma net_sane_new_lock_comm_Q_inv_sender [n0 n1 m0 m1 t v] [N0 N1 : PNet] :
      net_sane N0 ->
      (N0 =(NComm m0 m1 t v)=> N1) ->
      ~ net_lock_on N0 n0 n1 ->
      net_lock_on N1 n0 n1 ->
      n0 = m0.

    Proof.
      intros.
      remember (NComm m0 m1 &t v) as na.
      induction `(N0 =(_)=> _) using (net_ind_of n0); hsimpl in *; doubt.
      - compat_hsimpl in *.
        unfold net_lock_on, net_lock in *.
        exfalso; apply `(~ (exists L, _)).
        hsimpl in *; exists L; attac.
        rewrite `(NetMod.get m1 N0 = _) in *.
        rewrite `(NetMod.get m1 N1 = _) in *.
        consider (exists srpc, SRPC_sane srpc (pq I0 P0 O0)) by eattac.
        consider (pq_lock _ _) by assumption.
        constructor; eauto.
        intros n v0 **.
        assert (~ In (n, R, v0) (I0 ++ [(m0, &t, v)])) by auto.
        attac.
      - unfold net_lock_on, net_lock in *.
        rewrite `(NetMod.get n0 N0 = _) in *.
        bs.
    Qed.

    Lemma net_sane_new_lock_comm_Q_inv_tag [n0 n1 m0 m1 t v] [N0 N1 : PNet] :
      net_sane N0 ->
      (N0 =(NComm m0 m1 t v)=> N1) ->
      ~ net_lock_on N0 n0 n1 ->
      net_lock_on N1 n0 n1 ->
      t = Q.

    Proof.
      intros.
      destruct t; auto; exfalso.
      consider (n0 = m0) by eauto using net_sane_new_lock_comm_Q_inv_sender.
      assert (m0 <> m1) by eauto using net_sane_no_self_reply.

      assert (pq_lock [n1] (NetMod.get m0 N1)) by attac.
      assert (~ pq_lock [n1] (NetMod.get m0 N0)) by attac.

      consider (_ =(_)=> _); hsimpl in *.

      consider (exists srpc, SRPC_sane srpc (NetMod.get m0 N0)) by attac.
      absurd (~ pq_lock [n1] &S); eauto using SRPC_sane_send_R_no_lock_r with LTS.
    Qed.

    Lemma net_sane_new_lock_comm_Q_inv_receiver [n0 n1 m0 m1 t v] [N0 N1 : PNet] :
      net_sane N0 ->
      (N0 =(NComm m0 m1 t v)=> N1) ->
      ~ net_lock_on N0 n0 n1 ->
      net_lock_on N1 n0 n1 ->
      n1 = m1.

    Proof.
      intros.
      smash_eq n1 m1; exfalso.
      consider (n0 = m0) by eauto using net_sane_new_lock_comm_Q_inv_sender.
      consider (&t = Q) by  eauto using net_sane_new_lock_comm_Q_inv_tag.

      assert (pq_lock [n1] (NetMod.get m0 N1)) by attac.
      assert (~ pq_lock [n1] (NetMod.get m0 N0)) by attac.

      consider (exists srpc, SRPC_sane srpc (NetMod.get m0 N0)) by attac.

      consider (_ =(_)=> _); hsimpl in *.
      smash_eq m0 m1; hsimpl in *.
      - assert (pq_lock [n1] S0) by eauto using pq_recv_Q_derive_lock.
        assert (pq_lock [m0] S0) by eauto using SRPC_sane_send_Q_lock.
        enough (m0 = n1) by bs.
        enough (In n1 [m0]) by attac.
        enough (incl [n1] [m0]) by attac.
        eauto using pq_lock_incl.
      - assert (pq_lock [n1] S0) by eauto using pq_recv_Q_derive_lock.
        assert (pq_lock [m1] S0) by eauto using SRPC_sane_send_Q_lock.
        enough (m1 = n1) by bs.
        enough (In n1 [m1]) by attac.
        enough (incl [n1] [m1]) by attac.
        eauto using pq_lock_incl.
    Qed.

    (* TODO CONSISTENT NAMES *)
    Lemma net_sane_new_lock_send_Q [n0 n1] [a] [N0 N1 : PNet] :
      net_sane N0 ->
      (N0 =(a)=> N1) ->
      ~ net_lock_on N0 n0 n1 ->
      net_lock_on N1 n0 n1 ->
      exists v, a = NComm n0 n1 Q v.

    Proof.
      intros.
      destruct a as [? | m0 m1 ? v].
      - absurd (net_lock_on N0 n0 n1);
          eauto using
            SRPC_net_lock_on_tau_derive with LTS.
      - assert (&t = Q) by eauto using net_sane_new_lock_comm_Q_inv_tag.
        assert (n0 = m0) by eauto using net_sane_new_lock_comm_Q_inv_sender.
        assert (n1 = m1) by eauto using net_sane_new_lock_comm_Q_inv_receiver.
        attac.
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
      eauto using net_sane_send_R_lock_l.
    Qed.


    Lemma trans_invariant_net_sane_tau__Q_in [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      net_sane N0 ->
      SRPC_sane_Q_in (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, SRPC_sane srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      destruct S as [I1 P1 O1]; hsimpl in *.
      consider (_ =(Tau)=> _); doubt.
      destruct `(Que.Channel.NChan) as [? [|]]; hsimpl in *; simpl in *; repeat (intros ?); doubt.
      - smash_eq n0 c; attac.
        consider (exists I1', Deq (c, Q) v0 I0 I1' /\ Deq (n0, Q) v I1' I') by (eapply Deq_Deq_swap; attac).
        bs.

      - consider (exists I1', Deq (c, Q) v0 I0 I1' /\ Deq (n0, R) v I1' I') by (eapply Deq_Deq_swap; eattac).
        bs.
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
      consider (_ =(Tau)=> _); doubt.
      destruct `(NChan) as [? [|]]; repeat (intros ?); hsimpl in *; simpl in *.
      - consider (exists I1', Deq (s, R) v0 I0 I1' /\ Deq (n0, Q) v I1' I') by (eapply Deq_Deq_swap; attac).
        bs.
      - consider (exists I1', Deq (s, R) v0 I0 I1' /\ Deq (n0, Q) v I1' I') by (eapply Deq_Deq_swap; attac).
        bs.
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
        intros ?.
        assert (In (n, R, v0) &I \/ In (n, R, v0) [(n, Q, v)]) as [|] by eattac.
        all: bs.

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
      repeat (intros ?).

      assert (List.In (s, R, v) I0) by (consider (_ =(Tau)=> _); eapply Deq_neq_In; eattac; intros ?; eattac).
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
      repeat (intros ?).
      consider (_ =(Tau)=> _); destruct `(NChan) as [? [|]] eqn:?; subst; doubt.
      - consider (exists c, srpc0 = Lock c s) by eattac.
        exists c; consider (SRPC_sane _ _); attac.
      - assert (exists c, srpc0 = Lock c s) by eattac.
        assert (exists c', srpc0 = Lock c' n1) by eattac.
        hsimpl in *.
        bs.
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
        bs.

      - assert (exists c, SRPC (Lock c n0) P0).
        {
          consider (exists c, srpc0 = Lock c n0) by eattac.
          consider (SRPC_sane _ _); eattac.
        }
        consider (exists c, SRPC (Work c) P0) by attac.
        hsimpl in *; bs.
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
      repeat (intros ?).
      consider (_ =(Tau)=> _); destruct `(NChan) as [? [|]] eqn:?; subst; doubt.
      - assert (List.In (s, Q, v) O0).
        {
          hsimpl in *. simpl in *.
          rewrite removelast_app in * by attac.
          simpl in *.
          rewrite app_nil_r in *. (* coq bug *)
          attac.
        }
        assert (exists c, SRPC (Lock c s) P0) by (consider (SRPC_sane _ _); eattac).
        assert (exists c, SRPC (Work c) P0) by (eattac).
        hsimpl in *; bs.

      - assert (List.In (s, Q, v) O0).
        {
          hsimpl in *. simpl in *.
          rewrite removelast_app in * by attac.
          simpl in *.
          rewrite app_nil_r in *. (* coq bug *)
          attac.
        }
        assert (exists c, SRPC (Lock c s) P0) by (consider (SRPC_sane _ _); eattac).
        assert (exists c, SRPC (Work c) P0) by (eattac).
        hsimpl in *.
        bs.
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
      destruct S as [I1 P1 O1]; compat_hsimpl in *; repeat (intros ?); simpl in *.
      consider (_ =(Tau)=> _); destruct `(NChan) as [? [|]] eqn:?; subst; doubt.
      - consider (exists O0', Deq (c, R) v O0 O0' /\ O' = O0' ++ [(n1, Q, v0)]) by (eapply Deq_app_or_l; eattac).
        enough (List.In (c, R, v') O0') by eattac.
        assert (List.In (c, R, v') O0' \/ List.In (c, R, v') [(n1, Q, v0)]) as [|] by eattac; attac.
      - smash_eq c n1.
        + assert (proc_client c P0) by eattac.
          enough (exists v, List.In (c, R, v) O0) by eattac.
          hsimpl in *.
          destruct (Deq_dec' O0 (c, R)).
          1: { attac. }
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
      consider (_ =(Tau)=> _); doubt.
      destruct `(NChan) as [? [|]] eqn:?; repeat (intros ?); subst; doubt.
      - assert (exists c, SRPC (Lock c s) P0) by (consider (SRPC_sane _ _); eattac).
        assert (exists c', SRPC (Work c') P0) by eattac.
        hsimpl in *; bs.
      - assert (exists c, SRPC (Lock c s) P0) by (consider (SRPC_sane _ _); eattac).
        assert (exists c', SRPC (Work c') P0) by eattac.
        hsimpl in *; bs.
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
      consider (_ =(Tau)=> _); doubt.
      destruct `(NChan) as [? [|]] eqn:?; repeat (intros ?); subst; doubt.
      - assert (exists c, SRPC (Lock c s) P0) by (consider (SRPC_sane _ _); eattac).
        assert (exists c', SRPC (Work c') P0) by eattac.
        hsimpl in *; bs.
      - assert (exists c, SRPC (Lock c s) P0) by (consider (SRPC_sane _ _); eattac).
        assert (exists c', SRPC (Work c') P0) by eattac.
        hsimpl in *; bs.
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
      consider (_ =(Tau)=> _);
        destruct `(NChan) as [? [|]] eqn:?; repeat (intros ?); subst; doubt.
      - consider (exists c', SRPC (Work c') P1) by eattac.
        bs (Lock c s = Work c').
      - consider (exists c', SRPC (Work c') P1) by eattac.
        bs (Lock c s = Work c').
      - consider (exists c', SRPC (Lock c' n2) P1) by eattac.
        consider (Lock c s = Lock c' n2) by eattac.
        hsimpl in *.
        destruct O0; doubt; hsimpl in *; eattac.
      - assert (SRPC Free P1) by eattac.
        bs (Lock c s = Free) by eattac.
      - consider (exists c', SRPC (Work c') P1) by eattac.
        bs (Lock c s = Work c').
      - consider (exists c', SRPC (Work c') P1) by eattac.
        bs (Lock c s = Work c').
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
      consider (_ =(Tau)=> _); hsimpl in *; try (destruct `(Que.Channel.NChan) as [? [|]] eqn:?); repeat (intros ?); subst; consider (proc_client _ _); doubt.
      - assert (SRPC (Work n1) (cont v)) by eattac.
        destruct `(SRPC_Handle_State _).
        + assert (SRPC (Work n1) (cont v)) by eattac.
          consider (Work n1 = Work c) by attac.
          bs.
        + bs (Work n1 = Lock c s) by attac.
      - consider (exists c', SRPC (Lock c' n1) (PRecv h) /\ SRPC (Work c') (cont v)) by eauto using SRPC_recv_R with LTS.
        destruct `(SRPC_Handle_State _).
        + assert (SRPC (Work c) (cont v)) by eattac.
          consider (Work c' = Work c) by attac.
          enough (proc_client c (cont v)); eattac.
        + bs (Work c' = Lock c s) by attac.
      - consider (exists c', SRPC (Work c') (PSend (n1, Q) v P1) /\ SRPC (Lock c' n1) P1) by eauto using SRPC_send_Q with LTS.
        destruct `(SRPC_Handle_State _).
        + bs (Work c = Lock c' n1) by attac.
        + consider (Lock c' n1 = Lock c s) by attac.
          eenough (proc_client c _); eattac.
      - consider (SRPC (Work n1) _ /\ SRPC Free _) by eattac.
        destruct `(SRPC_Handle_State _).
        + bs (Work c = Free) by attac.
        + bs (Lock c s = Free) by attac.
      - consider (exists c', SRPC (Work c') (PTau P1) /\ SRPC (Work c') P1) by eauto using SRPC_tau with LTS.
        destruct `(SRPC_Handle_State _).
        + consider (Work c' = Work c) by attac.
          attac.
        + bs (Work c' = Lock c s) by attac.
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
      destruct S as [I1 P1 O1']; hsimpl in *; simpl in *.
      consider (_ =(Tau)=> _); doubt; hsimpl in *.
      destruct `(NChan) as [? [|]] eqn:?; repeat (intros ?); subst; doubt.
      - consider (exists c', SRPC (Work c') (PSend (n1, Q) v P1) /\ SRPC (Lock c' n1) P1) by eauto using SRPC_send_Q with LTS.
        enough (List.In (c, R, v') O0 \/ List.In (c, R, v') [(n1, Q, v)]) as [|]; eattac.
      - consider (SRPC (Work n1) _ /\ SRPC Free _) by eauto using SRPC_send_R with LTS.
        assert (List.In (c, R, v') O0 \/ List.In (c, R, v') [(n1, R, v)]) as [|]; eattac.
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
      consider (_ =(Tau)=> _); repeat (intros ?);
        destruct `(NChan) as [? [|]] eqn:?; subst; consider (proc_client _ _); doubt.
        - assert (SRPC (Work n1) _) by eattac.
        destruct `(SRPC_Handle_State _).
        + assert (SRPC (Work n1) _) by eattac.
          consider (Work n1 = Work c) by attac.
          bs.
        + bs (Work n1 = Lock c s) by attac.
      - consider (exists c', SRPC (Lock c' n1) P0 /\ SRPC (Work c') P1) by eauto using SRPC_recv_R.
        destruct `(SRPC_Handle_State _).
        + assert (SRPC (Work c) P1) by eattac.
          consider (Work c' = Work c) by attac.
          enough (proc_client c P0); eattac.
        + bs (Work c' = Lock c s) by attac.
      - consider (exists c', SRPC (Work c') P0 /\ SRPC (Lock c' n1) P1) by eauto using SRPC_send_Q.
        destruct `(SRPC_Handle_State _).
        + bs (Work c = Lock c' n1) by attac.
        + consider (Lock c' n1 = Lock c s) by attac.
          assert (List.In (c, R, v0) O0 \/ List.In (c, R, v0) [(s, Q, v)]) as [|]; (hsimpl in *|-; eattac).
      - consider (SRPC (Work n1) P0 /\ SRPC Free P1) by eattac.
        destruct `(SRPC_Handle_State _).
        + bs (Work c = Free) by attac.
        + bs (Lock c s = Free) by attac.
      - consider (exists c', SRPC (Work c') P0 /\ SRPC (Work c') P1) by eauto using SRPC_tau.
        destruct `(SRPC_Handle_State _).
        + consider (Work c' = Work c) by attac.
          attac.
        + bs (Work c' = Lock c s) by attac.
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
        bs (Free = Busy `(_)).

      - consider (exists c', SRPC (Lock c' n) P /\ SRPC (Work c') P1) by eauto using SRPC_recv_R.
        smash_eq c c'; attac.

        consider (proc_client c (PRecv &handle)).
        bs.

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
          bs (Free = Busy `(_)) by eattac.
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
        bs (pq_O (pq I2 P2 ((n1, Q, v) :: O2)) = []) by eauto using SRPC_sane_R_in_out_nil.

      - enough (s = n1) by eattac.
        consider (exists c, srpc0 = Lock c s) by attac.
        hsimpl in *.
        assert (SRPC_pq (Lock c s) (pq I2 P2 ((n1, Q, v)::O2))) by attac.
        consider (Lock n' n1 = Lock c s) by attac.

      - hsimpl in *.
        assert (~ In (s, Q, v0) (removelast (pq_O (pq I2 P2 ((n1, Q, v) :: O2))))) by eauto using SRPC_sane_Q_out_last_inv.
        destruct O2; attac.
      - hsimpl in *.
        assert (Deq (c, R) v0 ((n1, Q, v)::O2) ((n1, Q, v)::O')) by attac.
        attac.
      - compat_hsimpl in *; attac.
      - attac.
      - hsimpl in *.
        enough (O2 = []) by bs.
        eapply SRPC_sane__Q_out_last_nil_inv with (O0:=[]);
          eauto; simpl in *; eauto.
      - attac.
      - attac.
      - attac.
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
        1: { bs (In (n1, R, v0) O01) by attac. }
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
        bs (n0 <> n0) by eauto using net_lock_on_no_send.
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
          assert (In (c, Q, v') I'' \/ In (c, Q, v') [(n0, Q, v)]) as [|] by attac; bs.
      - assert (~ In (s, R, v0) [(n0, Q, v)]) by attac.
        consider (exists I'', Deq (s, R) v0 I10 I'' /\ I' = I'' ++ [(n0, Q, v)]) by eauto using Deq_app_or_l.
        assert (~ In (s, R, v') I'') by attac.
        intros ?.
        assert (In (s', R, v') I'' \/ In (s', R, v') [(n0, Q, v)]) as [|] by attac; bs.
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


    Lemma SRPC_sane_SRPC_proc_inv [srpc S P] :
      SRPC_sane srpc S ->
      pq_P S = P ->
      SRPC srpc P.

    Proof.
      intros.
      destruct S as [? ? ?]. hsimpl in *.
      eenough (SRPC_pq srpc (pq _ P _)); attac.
    Qed.

    #[export] Hint Resolve SRPC_sane_SRPC_proc_inv : LTS.


    Lemma SRPC_sane_lock_no_R [S srpc L n v I] :
      SRPC_sane srpc S ->
      pq_lock L S ->
      I = pq_I S ->
      ~ In (n, R, v) I.

    Proof.
      intros.
      assert (SRPC_pq srpc &S) by attac.
      consider (exists s, pq_lock [s] &S) by eauto 4 using SRPC_pq_get_lock with LTS.
      consider (exists c, SRPC_pq (Lock c s) &S) by eauto using lock_SRPC_Lock_pq with LTS.
      destruct S as [I0 P0 O0]; hsimpl in *.
      intros ?.
      smash_eq n s.
      - hsimpl in *; bs.
      - assert (SRPC (Lock c s) P0) by attac.
        consider (exists c', srpc = Lock c' n) by eauto using SRPC_sane_R_in_lock_inv.
        bs (Lock c' n = Lock c s) by attac.
    Qed.

    Lemma net_sane_lock_no_R [n0 n1 m1 v N I] :
      net_sane N ->
      net_lock_on N n0 n1 ->
      I = pq_I (NetMod.get n0 N) ->
      ~ In (m1, R, v) I.

    Proof.
      intros.
      consider (pq_lock [n1] (NetMod.get n0 N)).
      consider (exists srpc, SRPC_sane srpc (NetMod.get n0 N)) by attac.
      eauto using SRPC_sane_lock_no_R with LTS.
    Qed.

    #[export] Hint Resolve net_sane_lock_no_R : LTS.


    Lemma net_sane_R_derive_lock [n0 n1 m0 m1 N0 N1 v] :
      net_sane N0 ->
      (N0 =(NComm n1 n0 R v)=> N1) ->
      net_lock_on N1 m0 m1 ->
      net_lock_on N0 m0 m1.

    Proof.
      intros.

      assert (n0 <> m0) by (intros ?; attac; bs (~ net_lock_on N1 m0 m1) by eauto using net_sane_send_R_receiver_no_lock with LTS).

      smash_eq n1 m0.
      - consider (_ =(_)=> _); smash_eq n0 n1; hsimpl in *.
        unfold net_lock_on, net_lock in *.
        hsimpl in *.
        exists L. split > [attac|].

        consider (exists srpc, SRPC_sane srpc (NetMod.get n1 N0)) by attac.
        bs (~ pq_lock L &S) by eauto using SRPC_sane_send_R_no_lock_r.
      - assert (NetMod.get m0 N0 = NetMod.get m0 N1) by attac.
        eapply net_lock_on_move_eq; eauto.
    Qed.


    Lemma net_sane_Q_bad_sender_derive_lock [n0 n1 m0 m1 N0 N1 v] :
      net_sane N0 ->
      (N0 =(NComm n0 n1 Q v)=> N1) ->
      n0 <> m0 ->
      net_lock_on N1 m0 m1 ->
      net_lock_on N0 m0 m1.

    Proof.
      intros.

      unfold net_lock_on, net_lock in *; hsimpl in *.
      exists L. split > [attac|].

      smash_eq n0 n1; hsimpl in *.
      1: {attac. }

      smash_eq m0 n1.
      2: { attac. }

      consider (_ =(_)=> _); hsimpl in *.
      eauto using pq_recv_Q_derive_lock.
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
      assert (forall s v, ~ In (s, R, v) I10) by (eauto using net_sane_lock_no_R, eq_sym with LTS).

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
        bs (n0 <> n0) by eauto using net_lock_on_no_send.
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
        + assert (forall v, ~ In (n0, Q, v) I0) by bs.
          consider (exists I1', Deq (n0, Q) v0 [(n0, Q, v)] I1' /\ I' = I0 ++ I1')
            by eauto using Deq_app_or_r with LTS.
          consider (Deq (n0, Q) v0 [(n0, Q, v)] I1'); doubt.
          compat_hsimpl in *; auto.
        + assert (~ In (c, Q, v0) [(n0, Q, v)]) by bs.
          consider (exists I1', Deq (c, Q) v0 I0 I1' /\ I' = I1' ++ [(n0, Q, v)])
            by eauto using Deq_app_or_l with LTS.
          assert (~ In (c, Q, v') I1') by eauto with LTS.
          intros ?.
          assert (In (c, Q, v') I1' \/ In (c, Q, v') [(n0, Q, v)]) as [|] by attac; bs.
    - assert (~ In (s, R, v0) [(n0, Q, v)]) by bs.
      consider (exists I1', Deq (s, R) v0 I0 I1' /\ I' = I1' ++ [(n0, Q, v)])
        by eauto using Deq_app_or_l with LTS.
      assert (~ In (s, R, v') I1') by eauto with LTS.

      intros ?.
      assert (In (s', R, v') I1' \/ In (s', R, v') [(n0, Q, v)]) as [|] by attac; bs.
    - assert (In (s, R, v0) I0 \/ In (s, R, v0) [(n0, Q, v)]) as [|] by attac; doubt.
      bs (pq_O (pq I0 P1 ((n0, Q, v) :: O1)) = []) by eauto using SRPC_sane_R_in_out_nil.

    - enough (s = n0) by eattac.
      consider (exists c, srpc = Lock c s) by attac.
      assert (SRPC_pq (Lock c s) (pq I0 P1 ((n0, Q, v)::O1))) by attac.
      consider (Lock n' n0 = Lock c s) by attac.
    - assert (~ In (s, Q, v0) (removelast (pq_O (pq I0 P1 ((n0, Q, v) :: O1))))) by eauto using SRPC_sane_Q_out_last_inv.
      destruct O1; attac.
    - assert (Deq (c, R) v0 ((n0, Q, v)::O1) ((n0, Q, v)::O')) by attac.
      attac.
    - bs (O1 = []) by (eapply SRPC_sane__Q_out_last_nil_inv with (O0:=[]); eauto; simpl in *; eauto).
    - assert (~ In (s, R, v') I0) by attac.
      intros ?.
      apply `(~ In _ _).
      assert (In (s, R, v') I0 \/ In (s, R, v') [(n0, Q, v)]) as [|]; attac.
    - bs (O1 = []) by (eapply SRPC_sane__Q_out_last_nil_inv with (O0:=[]); eauto; simpl in *; eauto).
    - assert (In (c, Q, v0) I0 \/ In (c, Q, v0) [(n0, Q, v)]) as [|] by attac; doubt.
      unfold net_lock_on, net_lock in *; hsimpl in *.
      bs.
    - assert (In (c, Q, v0) I0 \/ In (c, Q, v0) [(n0, Q, v)]) as [|] by attac; doubt.
      unfold net_lock_on, net_lock in *; hsimpl in *.
      bs.
    - unfold net_lock_on, net_lock in *; hsimpl in *.
      bs.
    Qed.


    Lemma trans_invariant_net_sane__net_sane_comm__self [n0 t v] [N0 N1 : PNet] :
      (N0 =(NComm n0 n0 t v)=> N1) ->
      net_sane N0 ->
      exists srpc, SRPC_sane srpc (NetMod.get n0 N1).

    Proof.
      intros.
      destruct t.
      - eauto using trans_invariant_net_sane__net_sane_comm__self_Q.
      - bs (n0 <> n0) by eauto using net_sane_no_self_reply.
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
    Qed.

    Lemma trans_invariant_net_sane_comm__locks_sound_Q [n0 n1 v] [N0 N1 : PNet] :
      (N0 =(NComm n0 n1 Q v)=> N1) ->
      net_sane N0 ->
      locks_sound N1.

    Proof.
      intros * ? ? m0 m1 ?.
      assert (net_lock_on N1 n0 n1) by eauto using net_sane_send_Q_new_lock.
      assert (~ net_lock_on N0 n0 n1) by (bs (n0 <> n0) by eauto using net_lock_on_no_send).
      assert (~ pq_client n0 (NetMod.get n1 N0)) by attac.

      smash_eq n0 m0.
      1: { assert (SRPC_net N1) by attac.
           consider (m1 = n1) by (eapply SRPC_net_lock_uniq; eauto).
           consider (_ =(_)=> _); compat_hsimpl in *.
           attac.
      }

      assert (net_lock_on N0 m0 m1) by eauto using net_sane_Q_bad_sender_derive_lock.

      consider (_ =(_)=> _); hsimpl in *.
      consider (pq_client m0 (NetMod.get m1 N0)) by attac; compat_hsimpl in *.
      - smash_eq_on m1 n1 n0; subst; compat_hsimpl; attac.
      - smash_eq_on m1 n1 n0; subst; compat_hsimpl; attac.
      - smash_eq_on m1 n1 n0; subst; compat_hsimpl; attac.
    Qed.

    Lemma trans_invariant_net_sane_comm__locks_sound_R [n0 n1 v] [N0 N1 : PNet] :
      (N0 =(NComm n0 n1 R v)=> N1) ->
      net_sane N0 ->
      locks_sound N1.

    Proof.
      intros * ? ? m1 m0 ?.
      assert (net_lock_on N0 n1 n0) by eauto using net_sane_send_R_lock_l.
      assert (~ net_lock_on N1 n1 n0) by eauto using net_sane_send_R_receiver_no_lock.

      assert (n0 <> n1) by eauto using net_sane_no_self_reply.

      smash_eq n1 m1.
      1: { bs (n0 = m0) by eauto using SRPC_net_no_relock with LTS. }

      assert (net_lock_on N0 m1 m0) by eauto using net_sane_R_derive_lock.

      consider (_ =(_)=> _); hsimpl in *.
      consider (pq_client m1 (NetMod.get m0 N0)) by attac; compat_hsimpl in *.
      - smash_eq_on m0 n1 n0; subst; compat_hsimpl; attac.
      - smash_eq_on m0 n1 n0; subst; compat_hsimpl; attac.
      - smash_eq_on m0 n1 n0; subst; compat_hsimpl; attac.
    Qed.

    Lemma trans_invariant_net_sane_comm__locks_sound [n0 n1 t v] [N0 N1 : PNet] :
      (N0 =(NComm n0 n1 t v)=> N1) ->
      net_sane N0 ->
      locks_sound N1.

    Proof.
      destruct t.
      - eauto using trans_invariant_net_sane_comm__locks_sound_Q.
      - eauto using trans_invariant_net_sane_comm__locks_sound_R.
    Qed.


    Lemma trans_invariant_net_sane_comm__locks_complete_Q [n0 n1 v] [N0 N1 : PNet] :
      (N0 =(NComm n0 n1 Q v)=> N1) ->
      net_sane N0 ->
      locks_complete N1.

    Proof.
      intros * ? ? m0 m1 ?.
      assert (net_lock_on N1 n0 n1) by eauto using net_sane_send_Q_new_lock.
      assert (~ net_lock_on N0 n0 n1) by bs (n0 <> n0) by eauto using net_lock_on_no_send.
      assert (~ net_lock_on N0 n0 m1) by bs (n0 <> n0) by eauto using net_lock_on_no_send.

      assert (~ pq_lock [n1] (NetMod.get n0 N0)) by attac. clear H3.
      assert (pq_lock [n1] (NetMod.get n0 N1)) by attac. clear H4.

      assert (SRPC_sane_net N1) by eauto using trans_invariant_net_sane_comm__SRPC_sane.

      assert (pq_client n0 (NetMod.get n1 N1)) by (consider (_ =(_)=> _); compat_hsimpl in *; attac).

      smash_eq n1 m1.
      2: {
        assert (pq_client m0 (NetMod.get m1 N0)).
        {
          consider (_ =(_)=> _); compat_hsimpl in *.
          smash_eq n1 n0; attac.
          smash_eq m1 n0; attac.
          consider (pq_client m0 _); attac.
        }
        assert (net_lock_on N0 m0 m1) by attac.
        eauto using net_lock_on_Q_preserve.
      }

      enough (pq_lock [n1] (NetMod.get m0 N1)) by attac.

      smash_eq n0 m0.
      smash_eq n1 m0.
      2: {
        replace (NetMod.get m0 N1) with (NetMod.get m0 N0)
        by (eapply act_particip_stay with (a := NComm n0 n1 Q v); attac).
        enough (net_lock_on N0 m0 n1) by attac.
        enough (pq_client m0 (NetMod.get n1 N0)) by attac.
        consider (_ =(_)=> _); compat_hsimpl in *.
        consider (pq_client m0 _); attac.
        - assert (In (m0, Q, v0) I0 \/ In (m0, Q, v0) [(n0, Q, v)]) as [|]; attac.
          smash_eq n0 n1; compat_hsimpl in *.
          + rewrite `(NetMod.get n0 N0 = _); attac.
          + rewrite `(NetMod.get n1 N0 = _); attac.
        - smash_eq n0 n1; compat_hsimpl in *.
          + rewrite `(NetMod.get n0 N0 = _); attac.
          + rewrite `(NetMod.get n1 N0 = _); attac.
        - smash_eq n0 n1; compat_hsimpl in *.
          + rewrite `(NetMod.get n0 N0 = _); attac.
          + rewrite `(NetMod.get n1 N0 = _); attac.
      }

      (* maybe I need a script for this... *)
      destruct (NetMod.get n0 N0) as [In00 Pn00 On00] eqn:?.
      destruct (NetMod.get n0 N1) as [In01 Pn01 On01] eqn:?.
      destruct (NetMod.get n1 N0) as [In10 Pn10 On10] eqn:?.
      destruct (NetMod.get n1 N1) as [In11 Pn11 On11] eqn:?.

      consider (On01 = []) by consider (pq_lock _ (pq _ _ On01)).

      consider (_ =(_)=> _); smash_eq n0 n1; compat_hsimpl in *.
      hsimpl in *.

      enough (pq_lock [n1] (NetMod.get n1 N0)).
      {
        rewrite `(NetMod.get n1 N0 = _) in *.
        consider (pq_lock [n1] _); constructor; attac.
        intros ?.
        assert (In (n, R, v0) In10 \/ In (n, R, v0) [(n0, Q, v)]) as [|]; eattac.
      }

      enough (pq_client n1 (NetMod.get n1 N0)) by attac.
      consider (pq_client n1 _); attac.
      assert (In (n1, Q, v0) In10 \/ In (n1, Q, v0) [(n0, Q, v)]) as [|]; attac.
    Qed.


    Lemma trans_invariant_net_sane_comm__locks_complete_R [n0 n1 v] [N0 N1 : PNet] :
      (N0 =(NComm n0 n1 R v)=> N1) ->
      net_sane N0 ->
      locks_complete N1.

    Proof.
      intros * ? ? m1 m0 ?.

      assert (net_lock_on N0 n1 n0) by eauto using net_sane_send_R_lock_l.
      assert (~ net_lock_on N1 n1 n0) by eauto using net_sane_send_R_receiver_no_lock.

      assert (pq_lock [n0] (NetMod.get n1 N0)) by attac. clear H2.
      assert (~ pq_lock [n0] (NetMod.get n1 N1)) by attac. clear H3.
      enough (pq_lock [m0] (NetMod.get m1 N1)) by attac.

      assert (n0 <> n1) by eauto using net_sane_no_self_reply.
      assert (pq_client n1 (NetMod.get n0 N0)) by attac.

      assert (SRPC_sane_net N1) by eauto using trans_invariant_net_sane_comm__SRPC_sane.

      (* maybe I need a script for this... *)
      destruct (NetMod.get n0 N0) as [In00 Pn00 On00] eqn:?.
      destruct (NetMod.get n0 N1) as [In01 Pn01 On01] eqn:?.
      destruct (NetMod.get n1 N0) as [In10 Pn10 On10] eqn:?.
      destruct (NetMod.get n1 N1) as [In11 Pn11 On11] eqn:?.
      destruct (NetMod.get m0 N0) as [Im00 Pm00 Om00] eqn:?.
      destruct (NetMod.get m0 N1) as [Im01 Pm01 Om01] eqn:?.
      destruct (NetMod.get m1 N0) as [Im10 Pm10 Om10] eqn:?.
      destruct (NetMod.get m1 N1) as [Im11 Pm11 Om11] eqn:?.

      consider (On10 = []) by consider (pq_lock _ (pq _ _ On10)).

      consider (_ =(_)=> _); compat_hsimpl in *.
      smash_eq m0 m1 n0 n1; compat_hsimpl in *|-.
      - enough (pq_lock [m0] (NetMod.get m0 N0)) by bs.
        enough (pq_client m0 (NetMod.get m0 N0)) by attac.
        rewrite `(NetMod.get m0 N0 = _).
        consider (pq_client m0 _); attac.
      - constructor.
        + attac.
        + enough (pq_lock [m0] (NetMod.get m0 N0)) by bs.
          enough (pq_client m0 (NetMod.get m0 N0)) by attac.
          rewrite `(NetMod.get m0 N0 = _).
          consider (pq_client m0 (pq _ _ [])); attac.
          assert (In (m0, Q, v0) Im10 \/ In (m0, Q, v0) [(n0, R, v)]) as [|]; eattac.
        + intros. hsimpl in *.
          intros ?.
          assert (In (n, R, v0) Im10 \/ In (n, R, v0) [(n0, R, v)]) as [|]; eattac.
          assert (AnySRPC_pq (pq Im10 Pm01 [])) by attac.
          consider (exists c, SRPC_pq (Lock c n0) (pq Im10 Pm01 [])) by eauto using lock_SRPC_Lock_pq.
          consider (exists c', SRPC_pq (Lock c' n) (pq Im10 Pm01 [])).
          {
            consider (exists srpc, SRPC_sane srpc (pq Im10 Pm01 [])) by attac.
            consider (exists c', srpc = Lock c' n) by attac.
            exists c'; eauto using SRPC_sane_SRPC_inv.
          }

          bs (Lock c' n = Lock c n0).
      - enough (pq_lock [m0] (NetMod.get m0 N0)) by bs.
        enough (pq_client m0 (NetMod.get m0 N0)) by attac.
        rewrite `(NetMod.get m0 N0 = _).
        consider (pq_client m0 _); attac.
      - exfalso.
        consider (exists srpc, SRPC_sane srpc (NetMod.get m0 N0)) by attac.
        rewrite `(NetMod.get m0 N0 = _) in *.
        consider (pq_client m1 (pq _ _ Om01)).
        + bs.
        + absurd (proc_client m1 Pm01); auto.
          eauto using net_sane_in_net_R_excl_c with LTS.
        + assert (Deq (m1, R) v ((m1, R, v)::Om01) Om01); attac.
      - enough (pq_client m1 (NetMod.get m0 N0)) by (rewrite <- `(NetMod.get m1 N0 = _); attac).
        consider (pq_client m1 _); attac.
      - enough (pq_lock [m0] (NetMod.get m1 N0)) by bs.
        enough (pq_client m1 (NetMod.get m0 N0)) by attac.
        consider (pq_client m1 _); attac.
        assert (In (m1, Q, v0) Im00 \/ In (m1, Q, v0) [(m1, R, v)]) as [|]; attac.
      - enough (pq_client m1 (NetMod.get m0 N0)) by (rewrite <- `(NetMod.get m1 N0 = _); attac).
        consider (pq_client m1 _); attac.
        assert (In (m1, Q, v0) Im00 \/ In (m1, Q, v0) [(n0, R, v)]) as [|]; attac.
      - enough (pq_lock [m0] (NetMod.get m1 N0)) by bs.
        enough (pq_client m1 (NetMod.get m0 N0)) by attac.
        attac.
      - constructor; attac.
        + enough (pq_lock [m0] (NetMod.get m1 N0)); attac.
        + intros ?.
          assert (In (n, R, v0) Im10 \/ In (n, R, v0) [(n0, R, v)]) as [|]; attac.
          assert (AnySRPC_pq (pq Im10 Pm10 [])) by attac.
          consider (exists c, SRPC_pq (Lock c n0) (pq Im10 Pm10 [])) by eauto using lock_SRPC_Lock_pq.
          consider (exists c', SRPC_pq (Lock c' n) (pq Im10 Pm10 [])).
          {
            consider (exists srpc, SRPC_sane srpc (pq Im10 Pm10 [])) by attac.
            consider (exists c', srpc = Lock c' n) by eattac.
            exists c'; eauto using SRPC_sane_SRPC_inv.
          }

          bs (Lock c' n = Lock c n0).
      - rewrite <- `(NetMod.get m1 _ = _).
        attac.
        (* TODO compress those cases *)
    Qed.

    Lemma trans_invariant_net_sane_comm__locks_complete [n0 n1 t v] [N0 N1 : PNet] :
      (N0 =(NComm n0 n1 t v)=> N1) ->
      net_sane N0 ->
      locks_complete N1.

    Proof.
      destruct t.
      - eauto using trans_invariant_net_sane_comm__locks_complete_Q.
      - eauto using trans_invariant_net_sane_comm__locks_complete_R.
    Qed.


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


    Theorem trans_invariant_net_sane : trans_invariant net_sane always.

    Proof.
      unfold trans_invariant.
      intros.
      destruct a.
      - eauto using trans_invariant_net_sane_tau.
      - eauto using trans_invariant_net_sane_comm.
    Qed.


    #[export] Hint Resolve trans_invariant_net_sane : inv.
    #[export] Hint Extern 0 (net_sane _) => solve_invariant : LTS.
End SRPC_NET_F.

Module Type SRPC_NET(Conf : SRPC_NET_CONF) := Conf <+ SRPC_NET_PARAMS <+ SRPC_NET_F.
