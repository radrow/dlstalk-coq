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
  Lemma serv_i_net_inv : forall I P O n [N : Net],
      NetMod.get n N = serv I P O ->
      serv_i (NetMod.get n N) = I.
  Proof. intros. rewrite H. attac. Qed.
  Lemma serv_p_net_inv : forall I P O n N,
      NetMod.get n N = serv I P O ->
      serv_p (NetMod.get n N) = P.
  Proof. intros. rewrite H. attac. Qed.
  Lemma serv_o_net_inv : forall I P O n N,
      NetMod.get n N = serv I P O ->
      serv_o (NetMod.get n N) = O.
  Proof. intros. rewrite H. attac. Qed.

  #[export] Hint Rewrite -> serv_i_net_inv serv_p_net_inv serv_o_net_inv using spank : LTS LTS_concl.
  #[export] Hint Resolve serv_i_net_inv serv_p_net_inv serv_o_net_inv : LTS LTS_concl.


    Definition SRPC_net N := forall n, AnySRPC_serv (NetMod.get n N).

    Lemma SRPC_net_get [N n] : SRPC_net N -> AnySRPC_serv (NetMod.get n N).
    Proof. attac. Qed.

    #[export] Hint Resolve SRPC_net_get : LTS.


    Lemma SRPC_lock_set [N n0 n1] :
      SRPC_net N ->
      lock N n0 n1 ->
      exists c, SRPC_serv (Locked c n1) (NetMod.get n0 N).

    Proof.
      unfold lock, lock_set.
      intros; hsimpl in *.

      consider (exists s, serv_lock [s] (NetMod.get n0 N)) by eauto using SRPC_serv_get_lock.
      enough (n1 = s) by (subst; eauto using lock_SRPC_Locked_serv with LTS).

      enough (In n1 [s]) by attac.
      enough (incl L [s]) by attac.
      eauto using serv_lock_incl.
    Qed.


    Lemma SRPC_net_invariant : trans_invariant SRPC_net always.

    Proof.
      unfold trans_invariant, SRPC_net.
      intros.

      consider (exists path, Path_of n [a] path) by eauto using path_of_exists.
      enough (NetMod.get n N0 =[path]=> NetMod.get n N1) by attac.
      eauto using path_of_ptrans with LTS.
    Qed.

    #[export] Hint Resolve SRPC_net_invariant : inv.
    #[export] Hint Extern 10 (SRPC_net _) => solve_invariant : LTS.


    Lemma SRPC_lock_set_uniq [N] :
      SRPC_net N ->
      lock_uniq_type N.

    Proof.
      unfold SRPC_net, lock_uniq_type.
      intros.
      assert (AnySRPC_serv (NetMod.get n N)) by eauto with LTS.
      consider (exists c0, SRPC_serv (Locked c0 m0) (NetMod.get n N)) by eauto using SRPC_lock_set.
      consider (exists c1, SRPC_serv (Locked c1 m1) (NetMod.get n N)) by eauto using SRPC_lock_set.
      enough (Locked c0 m0 = Locked c1 m1) by attac.
      eauto with LTS.
    Qed.

    #[export] Hint Resolve SRPC_lock_set_uniq : LTS.


    Lemma SRPC_lock_set_neq_nil [N] :
      SRPC_net N ->
      lock_neq_nil_type N.

    Proof.
      unfold lock_neq_nil_type, lock_set.
      intros.

      consider (exists s, serv_lock [s] (NetMod.get n N)) by eauto using SRPC_serv_get_lock.
      destruct L; doubt.

      assert (incl [s] []) by eauto using serv_lock_incl.
      bs (In s []).
    Qed.

    #[export] Hint Resolve SRPC_lock_set_neq_nil : LTS.


    Lemma SRPC_net_get_lock [N n0 n1] :
      SRPC_net N ->
      lock N n0 n1 ->
      serv_lock [n1] (NetMod.get n0 N).

    Proof.
      intros.
      enough (lock_set N [n1] n0) by eauto with LTS.
      eauto using lock_singleton with LTS.
    Qed.

    #[export] Hint Resolve SRPC_net_get_lock : LTS.


    Lemma SRPC_net_no_relock [N0 N1 a n n0 n1] :
      SRPC_net N0 ->
      lock N0 n n0 ->
      lock N1 n n1 ->
      (N0 =(a)=> N1) ->
      n0 = n1.

    Proof.
      intros.
      assert (AnySRPC_serv (NetMod.get n N0)) by attac.
      assert (AnySRPC_serv (NetMod.get n N1)) by attac.
      assert (serv_lock [n0] (NetMod.get n N0)) by attac.
      assert (serv_lock [n1] (NetMod.get n N1)) by attac.

      destruct a.
      - smash_eq n n2; compat_hsimpl in * |-; hsimpl in * |-.
        + bs.
        + enough (In n0 [n1]) by attac.
          enough (incl [n0] [n1]) by attac.
          attac.
      - assert (n <> n2) by eauto using lock_no_send.
        smash_eq n n3.
        + hsimpl in * |-; hsimpl in * |-.
          eauto using SRPC_serv_no_relock.
        + replace (NetMod.get n N1) with (NetMod.get n N0).
          * enough (In n0 [n1]) by attac.
            enough (incl [n0] [n1]) by attac.
            attac.
          * eapply (@act_particip_stay Serv PAct); attac.
    Qed.


    Lemma SRPC_net_tau_no_lock [N0 N1 n0 n1 a] :
      SRPC_net N0 ->
      (N0 =(NTau n0 a)=> N1) ->
      ~ lock N1 n0 n1.

    Proof.
      intros.
      enough (forall L, ~ serv_lock L (NetMod.get n0 N1)) by (unfold lock, lock_set in *; intros ?; eattac); intros.

      remember (NTau n0 a) as na.
      induction H0 using (net_ind_of n0); hsimpl in *; doubt.
      eauto using SRPC_tau_no_lock_r with LTS.
    Qed.


    Lemma SRPC_net_no_lock_tau_preserve [N0 N1 n0 n1 n a] :
      SRPC_net N0 ->
      ~ lock N0 n0 n1 ->
      (N0 =(NTau n a)=> N1) ->
      ~ lock N1 n0 n1.

    Proof.
      intros.

      remember (NTau n a) as na.
      induction H1 using (net_ind_of n0); hsimpl in *; doubt.
      - enough (forall L, ~ serv_lock L (NetMod.get n N1)) by (unfold lock, lock_set in *; intros ?; eattac); intros.
        eauto using SRPC_tau_no_lock_r with LTS.
      - unfold lock, lock_set in *.
        now rewrite `(NetMod.get n0 N0 = _) in *.
    Qed.


    Lemma SRPC_lock_tau_derive [N0 N1 n0 n1 n a] :
      SRPC_net N0 ->
      lock N1 n0 n1 ->
      (N0 =(NTau n a)=> N1) ->
      lock N0 n0 n1.

    Proof.
      intros.
      smash_eq n0 n.
      - bs (~ lock N1 n0 n1) by eauto using SRPC_net_tau_no_lock with LTS.
      - unfold lock, lock_set in *.
        replace (NetMod.get n0 N0) with (NetMod.get n0 N1); eattac.
    Qed.


    (** [c] is the client of this process *)
    Definition proc_client (c : Name) (P : Proc) : Prop :=
      exists (srpcb : SRPC_Busy_State c), SRPC (Busy srpcb) P.


    Lemma mk_proc_client [c P] [srpcb : SRPC_Busy_State c] :
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
    Inductive serv_client (c : Name) : Serv -> Prop  :=
    | PQH_in [I P O v] :
      List.In (c, Q, v) I ->
      serv_client c (serv I P O)

    | PQH_proc [I P O] :
      proc_client c P  ->
      serv_client c (serv I P O)

    | PQH_out [I P O v] :
      List.In (c, R, v) O ->
      serv_client c (serv I P O)
    .

    #[export] Hint Constructors serv_client : LTS.


    Fact serv_client_app_I_r [c I P O] I' :
      serv_client c (serv I P O) -> serv_client c (serv (I ++ I') P O).
    Proof. intros. kill H; eattac. Qed.

    Fact serv_client_app_I_l [c I P O] I' :
      serv_client c (serv I P O) -> serv_client c (serv (I' ++ I) P O).
    Proof. intros. kill H; eattac. Qed.

    Fact serv_client_app_O_r [c I P O] O' :
      serv_client c (serv I P O) -> serv_client c (serv I P (O ++ O')).
    Proof. intros. kill H; eattac. Qed.

    Fact serv_client_app_O_l [c I P O] O' :
      serv_client c (serv I P O) -> serv_client c (serv I P (O' ++ O)).
    Proof. intros. kill H; eattac. Qed.

    #[export] Hint Resolve serv_client_app_I_l serv_client_app_I_r serv_client_app_O_l serv_client_app_O_r : LTS.


    Definition service_wf_Q_in (S : Serv) := forall c v v' I', Deq (c, Q) v (serv_i S) I' -> ~ List.In (c, Q, v') I'.
    Definition service_wf_R_in (S : Serv) := forall s s' v v' I', Deq (s, R) v (serv_i S) I' -> ~ List.In (s', R, v') I'.
    Definition service_wf_R_in_lock (S : Serv) := forall s v, List.In (s, R, v) (serv_i S) -> exists c, SRPC_serv (Locked c s) S.
    Definition service_wf_Q_out_lock (S : Serv) := forall s v, List.In (s, Q, v) (serv_o S) -> exists c, SRPC_serv (Locked c s) S.
    Definition service_wf_Q_out_last (S : Serv) := forall s v, ~ List.In (s, Q, v) (List.removelast (serv_o S)).
    Definition service_wf_R_out_uniq (S : Serv) := forall c v v' O', Deq (c, R) v (serv_o S) O' -> ~ List.In (c, R, v') O'.
    Definition service_wf_R_Q (S : Serv) := forall s v v', List.In (s, R, v) (serv_i S) -> ~ List.In (s, Q, v') (serv_o S).
    Definition service_wf_Q_R (S : Serv) := forall s v v', List.In (s, Q, v) (serv_o S) -> ~ List.In (s, R, v') (serv_i S).
    Definition service_wf_lock_Q (S : Serv) := forall c s, SRPC_serv (Locked c s) S -> serv_o S <> [] -> exists v, List.In (s, Q, v) (serv_o S).

    Definition service_wf_in_Q_no_client (S : Serv) := forall c v, List.In (c, Q, v) (serv_i S) -> ~ proc_client c (serv_p S).
    Definition service_wf_in_Q_no_out_R (S : Serv) := forall c v v', List.In (c, Q, v) (serv_i S) -> ~ List.In (c, R, v') (serv_o S).
    Definition service_wf_client_no_out_R (S : Serv) := forall c v, proc_client c (serv_p S) -> ~ List.In (c, R, v) (serv_o S).


    #[export] Hint Transparent service_wf_Q_in service_wf_R_in service_wf_R_in_lock service_wf_Q_out_lock service_wf_Q_out_last service_wf_R_out_uniq service_wf_R_Q service_wf_Q_R service_wf_lock_Q service_wf_in_Q_no_client service_wf_in_Q_no_out_R service_wf_client_no_out_R : LTS.

    #[export] Hint Unfold service_wf_Q_in service_wf_R_in service_wf_R_in_lock service_wf_Q_out_lock service_wf_Q_out_last service_wf_R_out_uniq service_wf_R_Q service_wf_Q_R service_wf_lock_Q service_wf_in_Q_no_client service_wf_in_Q_no_out_R service_wf_client_no_out_R : SRPC.


    (** A much stronger version of SRPC_serv which holds in any network with the same premises *)
    Inductive service_wf (srpc : SRPC_State) (S : Serv) : Prop :=
      SPRC_serv_net_

        (Hsrpc : SRPC_serv srpc S)

        (H_Q_in : service_wf_Q_in S)

        (H_R_in : service_wf_R_in S)

        (H_R_in_lock : service_wf_R_in_lock S)

        (H_Q_out_lock : service_wf_Q_out_lock S)

        (H_Q_out_last : service_wf_Q_out_last S)

        (H_R_out_uniq : service_wf_R_out_uniq S)

        (H_R_Q : service_wf_R_Q S)

        (H_Q_R : service_wf_Q_R S)

        (H_lock_Q : service_wf_lock_Q S)

        (H_in_Q_no_client : service_wf_in_Q_no_client S)

        (H_in_Q_no_out_R : service_wf_in_Q_no_out_R S)

        (H_client_no_out_R : service_wf_client_no_out_R S)

        : service_wf srpc S.


    Lemma service_wf_SRPC_inv [srpc : SRPC_State] [S] :
      service_wf srpc S -> SRPC_serv srpc S.

    Proof. intros. kill H. Qed.

    Lemma service_wf_Q_in_inv [srpc : SRPC_State] [c v v' I I' P O] :
      service_wf srpc (serv I P O) ->
      Deq (c, Q) v I I' ->
      not (List.In (c, Q, v') I').
    Proof. intros. kill H. attac 1. Qed.

    Lemma service_wf_R_in_inv [srpc : SRPC_State] [s s' v v' I I' P O] :
      service_wf srpc (serv I P O) ->
      Deq (s, R) v I I' ->
      not (List.In (s', R, v') I').
    Proof. intros. kill H. attac 1. Qed.

    Lemma service_wf_R_in_lock_inv [srpc : SRPC_State] [s v I P O] :
      service_wf srpc (serv I P O) ->
      List.In (s, R, v) I ->
      exists c, srpc = Locked c s.
    Proof. intros. kill H. assert (exists c, SRPC_serv (Locked c s) (serv &I P &O)); eattac 1. Qed.

    Lemma service_wf_Q_out_lock_inv [srpc : SRPC_State] [s v I P O] :
      service_wf srpc (serv I P O) ->
      List.In (s, Q, v) O ->
      exists c, srpc = Locked c s.
    Proof. intros. kill H. assert (exists c, SRPC_serv (Locked c s) (serv &I P &O)); eattac 1. Qed.

    Lemma service_wf_Q_out_last_inv [srpc : SRPC_State] [s v I P O] :
      service_wf srpc (serv I P O) ->
       ~ (List.In (s, Q, v) (List.removelast O)).
    Proof. intros. kill H. eattac 1. Qed.

    Lemma service_wf_Q_out_uniq_inv [srpc : SRPC_State] [c v v' I P O O'] :
      service_wf srpc (serv I P O) ->
      Deq (c, R) v O O' ->
      ~ (List.In (c, R, v') O').
    Proof. intros. kill H. eattac 1. Qed.

    Lemma service_wf_R_Q_inv [srpc : SRPC_State] [s v v' I P O] :
      service_wf srpc (serv I P O) ->
      List.In (s, R, v) I -> not (List.In (s, Q, v') O).
    Proof. intros. kill H. eattac 1. Qed.

    Lemma service_wf_Q_R_inv [srpc : SRPC_State] [s v v' I P O] :
      service_wf srpc (serv I P O) ->
      List.In (s, Q, v) O -> not (List.In (s, R, v') I).
    Proof. intros. kill H. eattac 1. Qed.

    Lemma service_wf_lock_Q_inv [c s I P O] :
      service_wf (Locked c s) (serv I P O) ->
      O <> [] ->
      exists v, List.In (s, Q, v) O.
    Proof. intros. kill H. eattac 1. Qed.

    Lemma service_wf_Q_excl_R_inv [srpc : SRPC_State] [c v v' I P O] :
      service_wf srpc (serv I P O) ->
      List.In (c, Q, v) I ->
      ~ List.In (c, R, v') O.
    Proof. intros. kill H. eattac 1. Qed.

    Lemma service_wf_Q_excl_c_inv [srpc : SRPC_State] [c v I P O] :
      service_wf srpc (serv I P O) ->
      List.In (c, Q, v) I ->
      ~ proc_client c P.
    Proof. intros. kill H. eattac 1. Qed.

    Lemma service_wf_R_excl_Q_inv [srpc : SRPC_State] [c v v' I P O] :
      service_wf srpc (serv I P O) ->
      List.In (c, R, v) O ->
      ~ List.In (c, Q, v') I.
    Proof. intros. kill H. eattac 1. Qed.

    Lemma service_wf_R_excl_c_inv [srpc : SRPC_State] [c v I P O] :
      service_wf srpc (serv I P O) ->
      List.In (c, Q, v) I ->
      ~ proc_client c P.
    Proof. intros. kill H. eattac 1. Qed.

    Lemma service_wf_c_excl_Q_inv [srpc : SRPC_State] [c v I P O] :
      service_wf srpc (serv I P O) ->
      proc_client c P ->
      ~ List.In (c, Q, v) I.
    Proof. intros. kill H. eattac 1. Qed.

    Lemma service_wf_c_excl_R_inv [srpc : SRPC_State] [c v I P O] :
      service_wf srpc (serv I P O) ->
      proc_client c P ->
      ~ List.In (c, R, v) O.
    Proof. intros. kill H. eattac 1. Qed.


    #[export] Hint Resolve
      service_wf_SRPC_inv
      service_wf_Q_in_inv
      service_wf_R_in_inv
      service_wf_R_in_lock_inv
      service_wf_Q_out_lock_inv
      service_wf_Q_out_last_inv
      service_wf_Q_out_uniq_inv
      service_wf_R_Q_inv
      service_wf_Q_R_inv
      service_wf_lock_Q_inv
      service_wf_Q_excl_R_inv
      service_wf_Q_excl_c_inv
      service_wf_R_excl_Q_inv
      service_wf_R_excl_c_inv
      service_wf_c_excl_Q_inv
      service_wf_c_excl_R_inv
      : LTS.



    (* TODO why... *)
    Lemma eq_some_neq_none [T] : forall (x : T) a, a = Some x -> a <> None. Proof. eattac. Qed.
    Hint Resolve eq_some_neq_none : LTS.


    Lemma service_wf__Q_in_inv_l [srpc] [S] [I0 I1 c v v'] :
      service_wf srpc S ->
      serv_i S = I0 ++ I1 ->
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

    Lemma service_wf__Q_in_inv_r [srpc] [S] [I0 I1 c v v'] :
      service_wf srpc S ->
      serv_i S = I0 ++ I1 ->
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

    Lemma service_wf__Q_in_inv_eq [srpc] [S] [I0 c v v'] :
      service_wf srpc S ->
      serv_i S = I0 ->
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

    Lemma service_wf__R_in_inv_l [srpc] [S] [I0 I1 s s' v v'] :
      service_wf srpc S ->
      serv_i S = I0 ++ I1 ->
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

    Lemma service_wf__R_in_inv_r [srpc] [S] [I0 I1 s s' v v'] :
      service_wf srpc S ->
      serv_i S = I0 ++ I1 ->
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

    Lemma service_wf__R_in_inv_eq_v [srpc] [S] [I0 s s' v v'] :
      service_wf srpc S ->
      serv_i S = I0 ->
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

    Lemma service_wf__R_in_inv_eq_s [srpc] [S] [I0 s s' v v'] :
      service_wf srpc S ->
      serv_i S = I0 ->
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


    Lemma service_wf__R_in_lock_inv [c s s'] [S] [I0] [v] :
      service_wf (Locked c s) S ->
      serv_i S = I0 ->
      List.In (s', R, v) I0 ->
      s' = s.
    Proof.
      intros.
      destruct S.
      consider (exists c', (Locked c s) = (Locked c' s')) by eattac.
    Qed.

    Lemma service_wf__Q_out_lock_inv [c s s'] [S] [O0] [v] :
      service_wf (Locked c s) S ->
      serv_o S = O0 ->
      List.In (s', Q, v) O0 ->
      s' = s.
    Proof.
      intros.
      destruct S.
      consider (exists c', (Locked c s) = (Locked c' s')) by eattac.
    Qed.

    Lemma service_wf__Q_out_last_inv [srpc] [S] [O0 O1 s v] :
      service_wf srpc S ->
      O1 <> [] ->
      serv_o S = O0 ++ O1 ->
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

    Lemma service_wf__Q_out_last_nil_inv [srpc] [S] [O0 O1 s v] :
      service_wf srpc S ->
      serv_o S = O0 ++ (s, Q, v) :: O1 ->
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


    Lemma service_wf__R_out_inv_l [srpc] [S] [O0 O1 c v v'] :
      service_wf srpc S ->
      serv_o S = O0 ++ O1 ->
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

    Lemma service_wf__R_out_inv_r [srpc] [S] [O0 O1 c v v'] :
      service_wf srpc S ->
      serv_o S = O0 ++ O1 ->
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

    Lemma service_wf__R_out_inv_eq_v [srpc] [S] [O0 c v v'] :
      service_wf srpc S ->
      serv_o S = O0 ->
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

    #[export] Hint Resolve service_wf__Q_in_inv_l service_wf__Q_in_inv_r service_wf__R_in_inv_l service_wf__R_in_inv_r service_wf__R_out_inv_l service_wf__R_out_inv_r : LTS.

    #[export] Hint Rewrite -> service_wf__Q_in_inv_eq service_wf__R_in_inv_eq_v service_wf__R_in_inv_eq_s service_wf__R_in_lock_inv service_wf__Q_out_lock_inv service_wf__Q_out_last_nil_inv service_wf__Q_out_last_inv service_wf__R_out_inv_eq_v using spank : LTS LTS_concl.


    (** If an SRPC service is locked after an action, then it's either a send (todo: from its output *)
  (*   queue) or a non-unlocking message *)
    Lemma service_wf_send_lock [srpc n a S0 S1] :
      service_wf srpc S0 -> (*  TODO : to net and remove n'<>n *)
      serv_lock [n] S1 ->
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
        assert (AnySRPC_serv (serv I0 P0 [])) as Hsrpc0' by attac.
        apply (SRPC_send_lock `(AnySRPC P0) `(proc_lock [n] P1) `(P0 =( Recv n0 v )=> P1)).
      - apply (Enq_nil HEnq).

      - destruct n0 as [n' t].

        destruct t; auto.
        exfalso.

        kill Hsrpc0.

        assert (AnySRPC_serv (serv I1 P1 [(n', R, v)])) as Hsrpc0' by attac.

        specialize (lock_SRPC_Locked `(AnySRPC P1) `(proc_lock [n] P1)) as [c Hsrpc_L].

        apply (SRPC_inv Hsrpc) in Hsrpc_L. subst.
        edestruct H_lock_Q; eauto; doubt.

      - assert (AnySRPC P0) as Hsrpc by (kill Hsrpc0; eattac).
        apply (SRPC_send_lock Hsrpc  `(proc_lock [n] P1) `(P0 =( Tau )=> P1)).
    Qed.


    Lemma service_wf_R_in_out_nil [srpc : SRPC_State] [s v S] :
      service_wf srpc S ->
      In (s, R, v) (serv_i S) ->
      serv_o S = [].
    Proof.
      intros.
      destruct S as [I0 P0 O0].
      simpl in *.
      consider (exists c, srpc = Locked c s) by attac.
      destruct O0; auto.
      assert (p::O0 <> []) by attac.
      remember (p::O0) as O1; clear HeqO1.
      consider (exists v', In (s, Q, v') (serv_o (serv I0 P0 O1))) by attac.
      bs (In (s, R, v) (serv_i (serv I0 P0 (O1)))) by eattac.
    Qed.


    Lemma service_wf_send_R_no_lock_r [srpc S0 S1 n v L] :
      service_wf srpc S0 ->
      (S0 =(Send (n, R) v)=> S1) ->
      ~ serv_lock L S1.

    Proof.
      intros; intros ?.
      consider (exists s, serv_lock [s] S1) by eauto using SRPC_serv_get_lock with LTS.
      consider (exists c, SRPC_serv (Locked c s) S1) by eauto using lock_SRPC_Locked_serv with LTS.
      consider (_ =(_)=> _); simpl in *.
      consider (serv_lock _ _).
      assert (SRPC_serv srpc (serv I0 P0 [(n, R, v)])) by eattac; simpl in *.
      consider (srpc = Locked c s) by eauto using SRPC_inv.
      consider (exists v', In (s, Q, v') [(n, R, v)]) by eattac.
    Qed.


    Lemma service_wf_send_Q_lock [srpc S0 S1 n v] :
      service_wf srpc S0 ->
      (S0 =(Send (n, Q) v)=> S1) ->
      serv_lock [n] S1.

    Proof.
      intros.
      assert (SRPC_serv srpc S0) by attac.
      consider (_ =(_)=> _).
      assert (service_wf srpc (serv I0 P0 ([] ++ (n, Q, v) :: O1))) by auto.
      consider (O1 = []) by (eapply service_wf__Q_out_last_nil_inv with (O0:=[]); unfold serv_o; eauto).
      consider (exists c, srpc = Locked c n) by eauto with LTS.
      simpl in *.
      eattac.
    Qed.


    Lemma service_wf_send_Q_SRPC_lock [srpc S0 S1 s v] :
      service_wf srpc S0 ->
      (S0 =(Send (s, Q) v)=> S1) ->
      exists c, srpc = Locked c s.

    Proof.
      intros.
      assert (AnySRPC_serv S1) by eattac.
      assert (serv_lock [s] S1) by eauto using service_wf_send_Q_lock.
      consider (exists c, SRPC_serv (Locked c s) S1) by eauto using lock_SRPC_Locked_serv.
      attac.
    Qed.


    Lemma service_wf_new_lock_send_Q [srpc S0 S1 a L] :
      service_wf srpc S0 ->
      ~ serv_lock L S0 ->
      serv_lock L S1 ->
      (S0 =(a)=> S1) ->
      exists n v, a = Send (n, Q) v /\ In n L.

    Proof.
      intros.
      destruct a.
      - destruct n as [n [|]].
        + assert (serv_lock [n] S1) by eauto using service_wf_send_Q_lock.
          exists n, v.
          split; auto.
          enough (incl [n] L) by attac.
          eauto with LTS.
        + absurd (serv_lock L S1); eauto using service_wf_send_R_no_lock_r.
      - absurd (serv_lock L S1); eauto using serv_recv_no_new_lock.
      - absurd (serv_lock L S1); eauto using SRPC_tau_no_lock_r with LTS.
    Qed.


    (* Every process is individually well_formed *)
    Definition service_wf_net N := forall n, exists srpc, service_wf srpc (NetMod.get n N).


    (* If n0 is locked on n1, then n1 handles the query of n0 *)
    Definition locks_sound N := forall n0 n1,
        lock N n0 n1 ->
        serv_client n0 (NetMod.get n1 N).


    (* If n1 handles a query from n0, then n0 is locked on n1   *)
    Definition locks_complete N := forall n0 n1,
        serv_client n0 (NetMod.get n1 N) -> lock N n0 n1.


    Inductive well_formed (N : Net) : Prop :=
    | WF
        (H_wf_SRPC : service_wf_net N)
        (H_lock_sound : locks_sound N)
        (H_lock_complete : locks_complete N)
      : well_formed N.


    (* Lemma service_wf_well_formed : forall N0, service_wf_net N0 -> SRPC_net N0. *)
    (* Proof. repeat (intros ?). specialize (`(service_wf_net _) n). attac. Qed. *)

    (* #[export] Hint Resolve service_wf_well_formed : LTS. (* TODO is this needed? *) *)


    Lemma well_formed_service_wf [N : Net] : well_formed N -> service_wf_net N.
    Proof. intros. kill H. intros ?. eauto with LTS. Qed.

    Lemma well_formed_SRPC [N : Net] : well_formed N -> SRPC_net N.
    Proof. intros. kill H. intros ?. destruct (H_wf_SRPC n). eauto with LTS. Qed.

    Lemma well_formed_lock_client [N S n0 n1] : well_formed N -> NetMod.get n1 N = S -> lock N n0 n1 -> serv_client n0 S.
    Proof. intros. kill H. auto. Qed.

    Lemma well_formed_client_lock [N S n0 n1] : well_formed N -> NetMod.get n1 N = S -> serv_client n0 S -> lock N n0 n1.
    Proof. intros. kill H. auto. Qed.


    #[export] Hint Resolve well_formed_service_wf well_formed_SRPC well_formed_lock_client well_formed_client_lock : LTS.


    (* This is to allow the condition from LocksStatic be used in Immediate hints. *)
    Lemma well_formed_AnySRPC' (N : Net) : well_formed N -> forall n, AnySRPC_serv (NetMod.get n N).
    Proof. intros. kill H. specialize (H_wf_SRPC n) as [? H]. kill H. attac. Qed.
    #[export] Hint Extern 0 (forall n, AnySRPC_serv (NetMod.get n _)) => simple apply well_formed_AnySRPC'; eassumption : LTS.



    Section Inversions.
      (* These hints should not quadrate with SRPC_serv variants because well_formed does not expose *)
  (*     service_wf *)

      Lemma well_formed_service_wf_ [N S n] :
        well_formed N ->
        NetMod.get n N = S ->
        exists srpc, service_wf srpc S.
      Proof.
        intros. kill H. specialize (H_wf_SRPC n) as [srpc H]. eauto with LTS.
      Qed.

      Lemma well_formed_AnySrpc [N S n] :
        well_formed N ->
        NetMod.get n N = S ->
        AnySRPC_serv S.
      Proof.
        intros. kill H. specialize (H_wf_SRPC n) as [srpc H]. eauto with LTS.
      Qed.

      Lemma well_formed_in_net_Q_in [N n c v v' I I' P O] :
        well_formed N ->
        NetMod.get n N = serv I P O ->
        Deq (c, Q) v I I' ->
        not (List.In (c, Q, v') I').
      Proof. intros. kill H. specialize (H_wf_SRPC n) as [srpc [*]]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma well_formed_in_net_R_in [N n s s' v v' I I' P O] :
        well_formed N ->
        NetMod.get n N = serv I P O ->
        Deq (s, R) v I I' ->
        not (List.In (s', R, v') I').
      Proof. intros. kill H; specialize (H_wf_SRPC n) as [srpc [*]]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma well_formed_in_net_R_in_lock [N n s v I P O] :
        well_formed N ->
        NetMod.get n N = serv I P O ->
        List.In (s, R, v) I ->
        exists c, SRPC_serv (Locked c s) (NetMod.get n N).
      Proof. intros. kill H; specialize (H_wf_SRPC n) as [srpc H]. rewrite H0 in *. consider (exists c, srpc = Locked c s); eattac.
      Qed.

      Lemma well_formed_in_net_Q_out_lock [N n s v I P O] :
        well_formed N ->
        NetMod.get n N = serv I P O ->
        List.In (s, Q, v) O ->
        exists c, SRPC_serv (Locked c s) (NetMod.get n N).
      Proof.
        intros. kill H; specialize (H_wf_SRPC n) as [srpc H]. rewrite H0 in *. consider (exists c, srpc = Locked c s); eattac.
      Qed.

      Lemma well_formed_in_net_Q_out_last [N n s v I P O] :
        well_formed N ->
        NetMod.get n N = serv I P O ->
        ~ (List.In (s, Q, v) (List.removelast O)).
      Proof. intros. kill H; specialize (H_wf_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma well_formed_in_net_Q_out_uniq [N n c v v' I P O O'] :
        well_formed N ->
        NetMod.get n N = serv I P O ->
        Deq (c, R) v O O' ->
        ~ (List.In (c, R, v') O').
      Proof. intros. kill H; specialize (H_wf_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma well_formed_in_net_R_Q [N n s v v' I P O] :
        well_formed N ->
        NetMod.get n N = serv I P O ->
        List.In (s, R, v) I -> not (List.In (s, Q, v') O).
      Proof. intros. kill H; specialize (H_wf_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma well_formed_in_net_Q_R [N n s v v' I P O] :
        well_formed N ->
        NetMod.get n N = serv I P O ->
        List.In (s, Q, v) O -> not (List.In (s, R, v') I).
      Proof. intros. kill H; specialize (H_wf_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma well_formed_in_net_Q_excl_R [N n c v v' I P O] :
        well_formed N ->
        NetMod.get n N = serv I P O ->
        List.In (c, Q, v) I ->
        ~ List.In (c, R, v') O.
      Proof. intros. kill H; specialize (H_wf_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma well_formed_in_net_Q_excl_c [N n c v I P O] :
        well_formed N ->
        NetMod.get n N = serv I P O ->
        List.In (c, Q, v) I ->
        ~ proc_client c P.
      Proof. intros. kill H; specialize (H_wf_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma well_formed_in_net_R_excl_Q [N n c v v' I P O] :
        well_formed N ->
        NetMod.get n N = serv I P O ->
        List.In (c, R, v) O ->
        ~ List.In (c, Q, v') I.
      Proof. intros. kill H; specialize (H_wf_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma well_formed_in_net_R_excl_c [N n c v I P O] :
        well_formed N ->
        NetMod.get n N = serv I P O ->
        List.In (c, R, v) O ->
        ~ proc_client c P.
      Proof. intros. kill H; specialize (H_wf_SRPC n) as [srpc H]. rewrite H0 in *. intros ?. absurd (In (c, R, v) &O); eauto with LTS.
      Qed.

      Lemma well_formed_in_net_c_excl_Q [N n c v I P O] :
        well_formed N ->
        NetMod.get n N = serv I P O ->
        proc_client c P ->
        ~ List.In (c, Q, v) I.
      Proof. intros. kill H; specialize (H_wf_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.

      Lemma well_formed_in_net_c_excl_R [N n c v I P O] :
        well_formed N ->
        NetMod.get n N = serv I P O ->
        proc_client c P ->
        ~ List.In (c, R, v) O.
      Proof. intros. kill H; specialize (H_wf_SRPC n) as [srpc H]. rewrite H0 in *. eauto with LTS. Qed.
    End Inversions.


    #[export] Hint Resolve
      well_formed_service_wf_
      well_formed_AnySrpc
      well_formed_in_net_Q_in
      well_formed_in_net_R_in
      well_formed_in_net_R_in_lock
      well_formed_in_net_Q_out_lock
      well_formed_in_net_Q_out_last
      well_formed_in_net_Q_out_uniq
      well_formed_in_net_R_Q
      well_formed_in_net_Q_R
      well_formed_in_net_Q_excl_R
      well_formed_in_net_Q_excl_c
      well_formed_in_net_R_excl_Q
      well_formed_in_net_R_excl_c
      well_formed_in_net_c_excl_Q
      well_formed_in_net_c_excl_R
      : LTS.


    Lemma service_wf_send_invariant [srpc S0 S1 nc v] :
      service_wf srpc S0 ->
      (S0 =(send nc v)=> S1) ->
      service_wf srpc S1.

    Proof.
      intros.
      destruct S0 as [I0 P0 O0]; compat_hsimpl in *.
      destruct nc as [c t].
      consider (service_wf _ _).
      constructor; ltac1:(autounfold with SRPC in * ); simpl; intros; try (solve [simpl in *; eauto]).
      - clear - H_Q_out_last.
        intros ?.
        apply `(~ In (s, Q, v0) (removelast (serv_o (serv I0 P0 ((c, &t, v) :: O1))))).
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


    Lemma well_formed_send_R_sender_no_lock [N0 N1 n0 n1 n v] :
      service_wf_net N0 ->
      (N0 =(NComm n0 n1 R v)=> N1) ->
      ~ lock N1 n0 n.

    Proof.
      intros.
      remember (NComm n0 n1 R v) as na.
      induction `(N0 =(na)=> N1) using (net_ind_of n0); hsimpl in *; doubt.
      - enough (forall L, ~ serv_lock L (NetMod.get n1 N1)) by (unfold lock, lock_set in *; intros ?; eattac); intros.
        enough (~ serv_lock L S0) by eauto using serv_recv_no_new_lock.
        consider (exists srpc, service_wf srpc (NetMod.get n1 N0)) by eauto with LTS.
        eauto using service_wf_send_R_no_lock_r with LTS.
      - enough (forall L, ~ serv_lock L (NetMod.get n0 N1)) by (unfold lock, lock_set in *; intros ?; eattac); intros.
        consider (exists srpc, service_wf srpc (NetMod.get n0 N0)) by eauto with LTS.
        eauto using service_wf_send_R_no_lock_r with LTS.
    Qed.


    Lemma well_formed_send_R_lock_l [N0 N1 n0 n1 v] :
      well_formed N0 ->
      (N0 =(NComm n1 n0 R v)=> N1) ->
      lock N0 n0 n1.

    Proof.
      intros.
      enough (serv_client n0 (NetMod.get n1 N0)) by attac.
      consider (_ =(_)=> _); hsimpl in *.
      destruct (NetMod.get n1 N0) as [I0 P0 O0] eqn:?.
      compat_hsimpl in *.
      eattac.
    Qed.


    Lemma well_formed_send_R_receiver_no_lock [N0 N1 n0 n1 n v] :
      well_formed N0 ->
      (N0 =(NComm n1 n0 R v)=> N1) ->
      ~ lock N1 n0 n.

    Proof.
      intros.

      assert (lock N0 n0 n1) by eauto using well_formed_send_R_lock_l.

      smash_eq n1 n.
      - eauto using lock_reply_unlock with LTS.
      - intros ?.
        absurd (n1 = n); eauto using SRPC_net_no_relock with LTS.
    Qed.


    Lemma well_formed_send_R_no_unlock [N0 N1 n0 n1 m0 m1 v] :
      well_formed N0 ->
      ~ lock N0 m0 m1 ->
      (N0 =(NComm n1 n0 R v)=> N1) ->
      ~ lock N1 m0 m1.

    Proof.
      intros.

      smash_eq m0 n0.
      1: { eauto using well_formed_send_R_receiver_no_lock. }

      smash_eq m0 n1.
      1: { eauto using well_formed_send_R_sender_no_lock with LTS. }

      remember (NComm n1 n0 R v) as na.
      induction `(N0 =(_)=> _) using (net_ind_of m0); hsimpl in *; doubt.

      unfold lock, lock_set in *.
      now rewrite `(NetMod.get m0 N0 = _) in *.
    Qed.


    Theorem well_formed_no_self_reply [N0 N1 : Net] [n0 n1 v] :
      well_formed N0 ->
      (N0 =(NComm n0 n1 R v)=> N1) ->
      n0 <> n1.

    Proof.
      intros.
      intros ?; subst.
      rename n1 into n.

      enough (lock N0 n n) by bs (n <> n) by eauto using lock_no_send.

      enough (serv_client n (NetMod.get n N0)) by attac.

      consider (_ =(NComm n n R v)=> _); compat_hsimpl in *; attac.
    Qed.


    Lemma well_formed_new_lock_comm_Q_inv_sender [n0 n1 m0 m1 t v] [N0 N1 : Net] :
      well_formed N0 ->
      (N0 =(NComm m0 m1 t v)=> N1) ->
      ~ lock N0 n0 n1 ->
      lock N1 n0 n1 ->
      n0 = m0.

    Proof.
      intros.
      remember (NComm m0 m1 &t v) as na.
      induction `(N0 =(_)=> _) using (net_ind_of n0); hsimpl in *; doubt.
      - compat_hsimpl in *.
        unfold lock, lock_set in *.
        exfalso; apply `(~ (exists L, _)).
        hsimpl in *; exists L; attac.
        rewrite `(NetMod.get m1 N0 = _) in *.
        rewrite `(NetMod.get m1 N1 = _) in *.
        consider (exists srpc, service_wf srpc (serv I0 P0 O0)) by eattac.
        consider (serv_lock _ _) by assumption.
        constructor; eauto.
        intros n v0 **.
        assert (~ In (n, R, v0) (I0 ++ [(m0, &t, v)])) by auto.
        attac.
      - unfold lock, lock_set in *.
        rewrite `(NetMod.get n0 N0 = _) in *.
        bs.
    Qed.

    Lemma well_formed_new_lock_comm_Q_inv_tag [n0 n1 m0 m1 t v] [N0 N1 : Net] :
      well_formed N0 ->
      (N0 =(NComm m0 m1 t v)=> N1) ->
      ~ lock N0 n0 n1 ->
      lock N1 n0 n1 ->
      t = Q.

    Proof.
      intros.
      destruct t; auto; exfalso.
      consider (n0 = m0) by eauto using well_formed_new_lock_comm_Q_inv_sender.
      assert (m0 <> m1) by eauto using well_formed_no_self_reply.

      assert (serv_lock [n1] (NetMod.get m0 N1)) by attac.
      assert (~ serv_lock [n1] (NetMod.get m0 N0)) by attac.

      consider (_ =(_)=> _); hsimpl in *.

      consider (exists srpc, service_wf srpc (NetMod.get m0 N0)) by attac.
      absurd (~ serv_lock [n1] &S); eauto using service_wf_send_R_no_lock_r with LTS.
    Qed.

    Lemma well_formed_new_lock_comm_Q_inv_receiver [n0 n1 m0 m1 t v] [N0 N1 : Net] :
      well_formed N0 ->
      (N0 =(NComm m0 m1 t v)=> N1) ->
      ~ lock N0 n0 n1 ->
      lock N1 n0 n1 ->
      n1 = m1.

    Proof.
      intros.
      smash_eq n1 m1; exfalso.
      consider (n0 = m0) by eauto using well_formed_new_lock_comm_Q_inv_sender.
      consider (&t = Q) by  eauto using well_formed_new_lock_comm_Q_inv_tag.

      assert (serv_lock [n1] (NetMod.get m0 N1)) by attac.
      assert (~ serv_lock [n1] (NetMod.get m0 N0)) by attac.

      consider (exists srpc, service_wf srpc (NetMod.get m0 N0)) by attac.

      consider (_ =(_)=> _); hsimpl in *.
      smash_eq m0 m1; hsimpl in *.
      - assert (serv_lock [n1] S0) by eauto using serv_recv_Q_derive_lock.
        assert (serv_lock [m0] S0) by eauto using service_wf_send_Q_lock.
        enough (m0 = n1) by bs.
        enough (In n1 [m0]) by attac.
        enough (incl [n1] [m0]) by attac.
        eauto using serv_lock_incl.
      - assert (serv_lock [n1] S0) by eauto using serv_recv_Q_derive_lock.
        assert (serv_lock [m1] S0) by eauto using service_wf_send_Q_lock.
        enough (m1 = n1) by bs.
        enough (In n1 [m1]) by attac.
        enough (incl [n1] [m1]) by attac.
        eauto using serv_lock_incl.
    Qed.

    (* TODO CONSISTENT NAMES *)
    Lemma well_formed_new_lock_send_Q [n0 n1] [a] [N0 N1 : Net] :
      well_formed N0 ->
      (N0 =(a)=> N1) ->
      ~ lock N0 n0 n1 ->
      lock N1 n0 n1 ->
      exists v, a = NComm n0 n1 Q v.

    Proof.
      intros.
      destruct a as [? | m0 m1 ? v].
      - absurd (lock N0 n0 n1);
          eauto using
            SRPC_lock_tau_derive with LTS.
      - assert (&t = Q) by eauto using well_formed_new_lock_comm_Q_inv_tag.
        assert (n0 = m0) by eauto using well_formed_new_lock_comm_Q_inv_sender.
        assert (n1 = m1) by eauto using well_formed_new_lock_comm_Q_inv_receiver.
        attac.
    Qed.


    Lemma well_formed_handler_uniq [N n0 n1 n1'] :
      well_formed N ->
      serv_client n0 (NetMod.get n1 N) ->
      serv_client n0 (NetMod.get n1' N) ->
      n1' = n1.

    Proof.
      intros.
      consider (lock N n0 n1 /\ lock N n0 n1') by attac.
      enough (lock_uniq_type N) by attac.
      eauto using SRPC_lock_set_uniq with LTS.
    Qed.


    Lemma well_formed_recv_R_SRPC [n0 n1 v] [N0 N1 : Net] :
      well_formed N0 ->
      (N0 =(NComm n0 n1 R v)=> N1) ->
      exists n', service_wf (Locked n' n0) (NetMod.get n1 N0).

    Proof.
      intros.
      consider (exists srpc, service_wf srpc (NetMod.get n1 N0)) by attac.
      assert (SRPC_serv srpc (NetMod.get n1 N0)) by attac.

      enough (exists n', srpc = Locked n' n0) by attac.
      enough (exists n', SRPC_serv (Locked n' n0) (NetMod.get n1 N0)) by attac.
      enough (serv_lock [n0] (NetMod.get n1 N0)) by eauto using lock_SRPC_Locked_serv with LTS.
      enough (lock_set N0 [n0] n1) by attac.
      enough (lock N0 n1 n0) by eauto using lock_singleton with LTS.
      eauto using well_formed_send_R_lock_l.
    Qed.


    Lemma well_formed_invariant_tau__Q_in [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      well_formed N0 ->
      service_wf_Q_in (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, service_wf srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      destruct S as [I1 P1 O1]; hsimpl in *.
      consider (_ =(Tau)=> _); doubt.
      destruct `(Que.Channel.NameTag) as [? [|]]; hsimpl in *; simpl in *; repeat (intros ?); doubt.
      - smash_eq n0 c; attac.
        consider (exists I1', Deq (c, Q) v0 I0 I1' /\ Deq (n0, Q) v I1' I') by (eapply Deq_Deq_swap; attac).
        bs.

      - consider (exists I1', Deq (c, Q) v0 I0 I1' /\ Deq (n0, R) v I1' I') by (eapply Deq_Deq_swap; eattac).
        bs.
    Qed.


    Lemma well_formed_invariant_tau__R_in [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      well_formed N0 ->
      service_wf_R_in (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, service_wf srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      destruct S as [I1 P1 O1]; compat_hsimpl in *.
      consider (_ =(Tau)=> _); doubt.
      destruct `(NameTag) as [? [|]]; repeat (intros ?); hsimpl in *; simpl in *.
      - consider (exists I1', Deq (s, R) v0 I0 I1' /\ Deq (n0, Q) v I1' I') by (eapply Deq_Deq_swap; attac).
        bs.
      - consider (exists I1', Deq (s, R) v0 I0 I1' /\ Deq (n0, Q) v I1' I') by (eapply Deq_Deq_swap; attac).
        bs.
    Qed.


    Theorem well_formed_reply_lock [N0 N1 : Net] [n0 n1 v] :
      well_formed N0 ->
      (N0 =(NComm n0 n1 R v)=> N1) ->
      lock N0 n1 n0.

    Proof.
      intros Hs0 T.

      assert (n0 <> n1) as HNEq by (eauto using well_formed_no_self_reply with LTS).

      kill Hs0.

      kill T.
      apply H_lock_complete.
      compat_hsimpl in *.
      rewrite `(NetMod.get n0 N0 = _).
      attac.
    Qed.

    Theorem well_formed_send_Q_new_lock [N0 N1 : Net] [n0 n1 v] :
      well_formed N0 ->
      (N0 =(NComm n0 n1 Q v)=> N1) ->
      lock N1 n0 n1.

    Proof.
      intros Hs0 T.
      consider (_ =(_)=> _).

      consider (NetMod.get n0 N0 =(send (n1, Q) v)=> NetMod.get n0 N0') by eattac.
      consider (exists srpc, service_wf srpc (NetMod.get n0 N0)) by eattac.

      enough (serv_lock [n1] (NetMod.get n0 N1)) by eattac.
      enough (serv_lock [n1] (NetMod.get n0 N0')).
      - smash_eq n0 n1.
        consider (N0' ~(n0 @ _)~> _).
        2: { replace (NetMod.get n0 N0') with (NetMod.get n0 N1); attac. }

        compat_hsimpl in *.
        hsimpl in *.

        consider (serv_lock _ _).
        attac.
        intros ?.
        assert (In (n, R, v0) &I \/ In (n, R, v0) [(n, Q, v)]) as [|] by eattac.
        all: bs.

      - assert (NetMod.get n0 N0 =(send (n1, Q) v)=> NetMod.get n0 N0')
          by eattac.
        eauto using service_wf_send_Q_lock.
    Qed.


    Lemma well_formed_invariant_tau__R_in_lock [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      well_formed N0 ->
      service_wf_R_in_lock (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, service_wf srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      repeat (intros ?).

      assert (List.In (s, R, v) I0) by (consider (_ =(Tau)=> _); eapply Deq_neq_In; eattac; intros ?; eattac).
      consider (exists c, srpc0 = Locked c s) by eauto using service_wf_R_in_lock_inv.
      exists c.
      assert (SRPC (Locked c s) P0) by (consider (service_wf _ _); eattac).
      destruct S as [I1 P1 O1].
      enough (SRPC (Locked c s) P1) by attac.
      consider (_ =(Tau)=> _); hsimpl in *; doubt.
      destruct n0 as [? [|]]; doubt.
    Qed.


    Lemma well_formed_invariant_tau__Q_out_lock [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      well_formed N0 ->
      service_wf_Q_out_lock (NetMod.get n N1).
    Proof.
      attac.
      consider (exists srpc0, service_wf srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (service_wf _ _); eattac).
      destruct S as [I1 P1 O1]; compat_hsimpl in *; simpl in *.
      repeat (intros ?).
      consider (_ =(Tau)=> _); destruct `(NameTag) as [? [|]] eqn:?; subst; doubt.
      - consider (exists c, srpc0 = Locked c s) by eattac.
        exists c; consider (service_wf _ _); attac.
      - assert (exists c, srpc0 = Locked c s) by eattac.
        assert (exists c', srpc0 = Locked c' n1) by eattac.
        hsimpl in *.
        bs.
      - enough (n1 = s) by eattac.
        assert (List.In (s, Q, v) O0 \/ List.In (s, Q, v) [(n1, Q, v0)]) as [|] by (hsimpl in * |-; eattac).
        2: { eattac. }

        assert (exists c, SRPC (Locked c s) P0) by (consider (service_wf _ _); eattac).
        assert (exists c, SRPC (Working c) P0) by eattac.
        attac.

      - assert (exists c, SRPC (Locked c s) P0).
        {
          assert (List.In (s, Q, v) O0 \/ List.In (s, Q, v) [(n1, R, v0)]) as [|] by (hsimpl in * |-; eattac).
          2: { eattac. }
          consider (exists c, srpc0 = Locked c s) by eattac.
          consider (service_wf _ _); eattac.
        }
        consider (exists c, SRPC (Working c) P0) by attac.

        hsimpl in *.
        bs.

      - assert (exists c, SRPC (Locked c n0) P0).
        {
          consider (exists c, srpc0 = Locked c n0) by eattac.
          consider (service_wf _ _); eattac.
        }
        consider (exists c, SRPC (Working c) P0) by attac.
        hsimpl in *; bs.
    Qed.


    Lemma well_formed_invariant_tau__Q_out_last [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      well_formed N0 ->
      service_wf_Q_out_last (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, service_wf srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (service_wf _ _); eattac).
      destruct S as [I1 P1 O1]; compat_hsimpl in *; simpl in *.
      repeat (intros ?).
      consider (_ =(Tau)=> _); destruct `(NameTag) as [? [|]] eqn:?; subst; doubt.
      - assert (List.In (s, Q, v) O0).
        {
          hsimpl in *. simpl in *.
          rewrite removelast_app in * by attac.
          simpl in *.
          rewrite app_nil_r in *. (* coq bug *)
          attac.
        }
        assert (exists c, SRPC (Locked c s) P0) by (consider (service_wf _ _); eattac).
        assert (exists c, SRPC (Working c) P0) by (eattac).
        hsimpl in *; bs.

      - assert (List.In (s, Q, v) O0).
        {
          hsimpl in *. simpl in *.
          rewrite removelast_app in * by attac.
          simpl in *.
          rewrite app_nil_r in *. (* coq bug *)
          attac.
        }
        assert (exists c, SRPC (Locked c s) P0) by (consider (service_wf _ _); eattac).
        assert (exists c, SRPC (Working c) P0) by (eattac).
        hsimpl in *.
        bs.
    Qed.


    Lemma well_formed_invariant_tau__R_out_uniq [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      well_formed N0 ->
      service_wf_R_out_uniq (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, service_wf srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (service_wf _ _); eattac).
      destruct S as [I1 P1 O1]; compat_hsimpl in *; repeat (intros ?); simpl in *.
      consider (_ =(Tau)=> _); destruct `(NameTag) as [? [|]] eqn:?; subst; doubt.
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

    Lemma well_formed_invariant_tau__R_Q [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      well_formed N0 ->
      service_wf_R_Q (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, service_wf srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (service_wf _ _); eattac).
      destruct S as [I1 P1 O1]; compat_hsimpl in *; simpl in *.
      consider (_ =(Tau)=> _); doubt.
      destruct `(NameTag) as [? [|]] eqn:?; repeat (intros ?); subst; doubt.
      - assert (exists c, SRPC (Locked c s) P0) by (consider (service_wf _ _); eattac).
        assert (exists c', SRPC (Working c') P0) by eattac.
        hsimpl in *; bs.
      - assert (exists c, SRPC (Locked c s) P0) by (consider (service_wf _ _); eattac).
        assert (exists c', SRPC (Working c') P0) by eattac.
        hsimpl in *; bs.
    Qed.


    Lemma well_formed_invariant_tau__Q_R [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      well_formed N0 ->
      service_wf_Q_R (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, service_wf srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (service_wf _ _); eattac).
      destruct S as [I1 P1 O1]; compat_hsimpl in *; simpl in *.
      consider (_ =(Tau)=> _); doubt.
      destruct `(NameTag) as [? [|]] eqn:?; repeat (intros ?); subst; doubt.
      - assert (exists c, SRPC (Locked c s) P0) by (consider (service_wf _ _); eattac).
        assert (exists c', SRPC (Working c') P0) by eattac.
        hsimpl in *; bs.
      - assert (exists c, SRPC (Locked c s) P0) by (consider (service_wf _ _); eattac).
        assert (exists c', SRPC (Working c') P0) by eattac.
        hsimpl in *; bs.
    Qed.

    Lemma well_formed_invariant_tau__lock_Q [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      well_formed N0 ->
      service_wf_lock_Q (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, service_wf srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (service_wf _ _); eattac).
      destruct S as [I1 P1 O1']; compat_hsimpl in *; simpl in *.
      destruct O1' as [|[[? ?] ?] O1]; doubt.
      consider (_ =(Tau)=> _);
        destruct `(NameTag) as [? [|]] eqn:?; repeat (intros ?); subst; doubt.
      - consider (exists c', SRPC (Working c') P1) by eattac.
        bs (Locked c s = Working c').
      - consider (exists c', SRPC (Working c') P1) by eattac.
        bs (Locked c s = Working c').
      - consider (exists c', SRPC (Locked c' n2) P1) by eattac.
        consider (Locked c s = Locked c' n2) by eattac.
        hsimpl in *.
        destruct O0; doubt; hsimpl in *; eattac.
      - assert (SRPC Ready P1) by eattac.
        bs (Locked c s = Ready) by eattac.
      - consider (exists c', SRPC (Working c') P1) by eattac.
        bs (Locked c s = Working c').
      - consider (exists c', SRPC (Working c') P1) by eattac.
        bs (Locked c s = Working c').
    Qed.

    Lemma well_formed_invariant_tau__in_Q_no_client [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      well_formed N0 ->
      service_wf_in_Q_no_client (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, service_wf srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (service_wf _ _); eattac).
      destruct S as [I1 P1 O1']; compat_hsimpl in *; simpl in *.
      consider (_ =(Tau)=> _); hsimpl in *; try (destruct `(Que.Channel.NameTag) as [? [|]] eqn:?); repeat (intros ?); subst; consider (proc_client _ _); doubt.
      - assert (SRPC (Working n1) (cont v)) by eattac.
        destruct `(SRPC_Busy_State _).
        + assert (SRPC (Working n1) (cont v)) by eattac.
          consider (Working n1 = Working c) by attac.
          bs.
        + bs (Working n1 = Locked c s) by attac.
      - consider (exists c', SRPC (Locked c' n1) (PRecv h) /\ SRPC (Working c') (cont v)) by eauto using SRPC_recv_R with LTS.
        destruct `(SRPC_Busy_State _).
        + assert (SRPC (Working c) (cont v)) by eattac.
          consider (Working c' = Working c) by attac.
          enough (proc_client c (cont v)); eattac.
        + bs (Working c' = Locked c s) by attac.
      - consider (exists c', SRPC (Working c') (PSend (n1, Q) v P1) /\ SRPC (Locked c' n1) P1) by eauto using SRPC_send_Q with LTS.
        destruct `(SRPC_Busy_State _).
        + bs (Working c = Locked c' n1) by attac.
        + consider (Locked c' n1 = Locked c s) by attac.
          eenough (proc_client c _); eattac.
      - consider (SRPC (Working n1) _ /\ SRPC Ready _) by eattac.
        destruct `(SRPC_Busy_State _).
        + bs (Working c = Ready) by attac.
        + bs (Locked c s = Ready) by attac.
      - consider (exists c', SRPC (Working c') (STau P1) /\ SRPC (Working c') P1) by eauto using SRPC_tau with LTS.
        destruct `(SRPC_Busy_State _).
        + consider (Working c' = Working c) by attac.
          attac.
        + bs (Working c' = Locked c s) by attac.
    Qed.

    Lemma well_formed_invariant_tau__in_Q_no_out_R [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      well_formed N0 ->
      service_wf_in_Q_no_out_R (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, service_wf srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (service_wf _ _); eattac).
      destruct S as [I1 P1 O1']; hsimpl in *; simpl in *.
      consider (_ =(Tau)=> _); doubt; hsimpl in *.
      destruct `(NameTag) as [? [|]] eqn:?; repeat (intros ?); subst; doubt.
      - consider (exists c', SRPC (Working c') (PSend (n1, Q) v P1) /\ SRPC (Locked c' n1) P1) by eauto using SRPC_send_Q with LTS.
        enough (List.In (c, R, v') O0 \/ List.In (c, R, v') [(n1, Q, v)]) as [|]; eattac.
      - consider (SRPC (Working n1) _ /\ SRPC Ready _) by eauto using SRPC_send_R with LTS.
        assert (List.In (c, R, v') O0 \/ List.In (c, R, v') [(n1, R, v)]) as [|]; eattac.
    Qed.

    Lemma well_formed_invariant_tau__client_no_out_R [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      well_formed N0 ->
      service_wf_client_no_out_R (NetMod.get n N1).

    Proof.
      attac.
      consider (exists srpc0, service_wf srpc0 (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?; hsimpl in *.
      assert (AnySRPC P0) by (consider (service_wf _ _); eattac).
      destruct S as [I1 P1 O1']; compat_hsimpl in *; simpl in *.
      consider (_ =(Tau)=> _); repeat (intros ?);
        destruct `(NameTag) as [? [|]] eqn:?; subst; consider (proc_client _ _); doubt.
        - assert (SRPC (Working n1) _) by eattac.
        destruct `(SRPC_Busy_State _).
        + assert (SRPC (Working n1) _) by eattac.
          consider (Working n1 = Working c) by attac.
          bs.
        + bs (Working n1 = Locked c s) by attac.
      - consider (exists c', SRPC (Locked c' n1) P0 /\ SRPC (Working c') P1) by eauto using SRPC_recv_R.
        destruct `(SRPC_Busy_State _).
        + assert (SRPC (Working c) P1) by eattac.
          consider (Working c' = Working c) by attac.
          assert (proc_client c P0) by eattac.
          bs.
        + bs (Working c' = Locked c s) by attac.
      - consider (exists c', SRPC (Working c') P0 /\ SRPC (Locked c' n1) P1) by eauto using SRPC_send_Q.
        destruct `(SRPC_Busy_State _).
        + bs (Working c = Locked c' n1) by attac.
        + consider (Locked c' n1 = Locked c s) by attac.
          assert (List.In (c, R, v0) O0 \/ List.In (c, R, v0) [(s, Q, v)]) as [|]; (hsimpl in *|-; eattac).
      - consider (SRPC (Working n1) P0 /\ SRPC Ready P1) by eattac.
        destruct `(SRPC_Busy_State _).
        + bs (Working c = Ready) by attac.
        + bs (Locked c s = Ready) by attac.
      - consider (exists c', SRPC (Working c') P0 /\ SRPC (Working c') P1) by eauto using SRPC_tau.
        destruct `(SRPC_Busy_State _).
        + consider (Working c' = Working c) by attac.
          attac.
        + bs (Working c' = Locked c s) by attac.
    Qed.


    Lemma well_formed_invariant_tau__service_wf [n N0 N1] :
      N0 ~(n @ Tau)~> N1 ->
      well_formed N0 ->
      service_wf_net N1.

    Proof.
      intros.
      intros n'.

      smash_eq n n'.
      2: {
        replace (NetMod.get n' N1) with (NetMod.get n' N0) by eauto using NV_stay with LTS.
        eattac.
      }

      consider (exists srpc0 : SRPC_State, service_wf srpc0 (NetMod.get n N0)) by attac.
      consider (exists srpc1, SRPC_serv srpc1 (NetMod.get n N1))
        by (hsimpl in *; assert (AnySRPC_serv (NetMod.get n N0)) by eattac; enough (AnySRPC_serv &S); eattac).

      exists srpc1.
      constructor;

      eauto using
        well_formed_invariant_tau__Q_in,
        well_formed_invariant_tau__R_in,
        well_formed_invariant_tau__R_in_lock,
        well_formed_invariant_tau__Q_out_lock,
        well_formed_invariant_tau__Q_out_last,
        well_formed_invariant_tau__R_out_uniq,
        well_formed_invariant_tau__R_Q,
        well_formed_invariant_tau__Q_R,
        well_formed_invariant_tau__lock_Q,
        well_formed_invariant_tau__in_Q_no_client,
        well_formed_invariant_tau__in_Q_no_out_R,
        well_formed_invariant_tau__client_no_out_R.
    Qed.


    Lemma serv_client_invariant_tau [c] :
      trans_invariant (fun S => AnySRPC_serv S /\ serv_client c S) (eq Tau).

    Proof.
      unfold trans_invariant.
      intros * T Hc Eq.
      subst.
      destruct Hc as [Hsrpc Hc].
      split.
      1: eauto with LTS.

      consider (serv_client c N0); consider (_ =(Tau)=> _);
        try (solve [eattac]);
        try (destruct `(NameTag) as [n [|]]); doubt.

      - consider (SRPC Ready P /\ SRPC (Working n) P1) by eauto using SRPC_recv_Q.
        smash_eq c n; eauto with LTS.
        enough (exists v', List.In (c, Q, v') I1) by eattac.
        exists v.
        unshelve eapply (Deq_neq_In _ `(Deq _ _ &I I1)); eattac.

      - enough (exists v', List.In (c, Q, v') I1) by eattac.
        exists v.
        unshelve eapply (Deq_neq_In _ `(Deq _ _ &I I1)); eattac.

      - consider (SRPC Ready P /\ SRPC (Working n) P1) by eauto using SRPC_recv_Q.
        smash_eq c n; attac.

        consider (proc_client c (PRecv h)).
        bs (Ready = Busy `(_)).

      - consider (exists c', SRPC (Locked c' n) P /\ SRPC (Working c') P1) by eauto using SRPC_recv_R.
        smash_eq c c'.
        + attac.
        + hsimpl in *.
          consider (proc_client c (PRecv &handle)).
          attac.
      - consider (exists c', SRPC (Working c') P /\ SRPC (Locked c' n) P1) by eauto using SRPC_send_Q.
        consider (proc_client c P) by attac.
        consider (Working c' = Busy `(_)) by attac.
        attac.

      - consider (SRPC (Working n) P /\ SRPC Ready P1) by eauto using SRPC_send_R.
        enough (c = n) by attac.
        enough (proc_client n P) by attac.
        attac.

      - consider (exists c', SRPC (Working c') P /\ SRPC (Working c') P1) by eauto using SRPC_tau.
        enough (c = c') by attac.
        enough (proc_client c' P) by attac.
        attac.
    Qed.


    Lemma well_formed_invariant_tau__locks_sound [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      well_formed N0 ->
      locks_sound N1.

    Proof.
      repeat (intros ?).

      enough (lock N0 n0 n1).
      {
        assert (serv_client n0 (NetMod.get n1 N0)) by attac.
        smash_eq n n1.
        + eapply serv_client_invariant_tau; eattac.
        + now replace (NetMod.get n1 N1) with (NetMod.get n1 N0) by (eauto using NV_stay with LTS).
      }

      enough (N0 =(NTau n Tau)=> N1) by eauto using SRPC_lock_tau_derive with LTS.
      eattac.
    Qed.


    Lemma well_formed_invariant_tau__locks_complete [n N0 N1] :
      NVTrans n Tau N0 N1 ->
      well_formed N0 ->
      locks_complete N1.

    Proof.
      repeat (intros ?).

      assert (N0 =(NTau n Tau)=> N1) by attac.
      enough (lock N0 n0 n1) by eauto using lock_tau_preserve.
      enough (serv_client n0 (NetMod.get n1 N0)) by attac.

      smash_eq n n1.
      2: { now replace (NetMod.get n1 N1) with (NetMod.get n1 N0) by (eauto using NV_stay with LTS). }

      assert (AnySRPC_serv (NetMod.get n N0)) by eattac.
      destruct (NetMod.get n N0) as [I0 P0 O0] eqn:?.
      destruct (NetMod.get n N1) as [I1 P1 O1] eqn:?.

      hsimpl in *. hsimpl in *.
      rewrite `(NetMod.get n N0 = _) in *.

      consider (_ =(Tau)=> _);
        try (destruct `(NameTag) as [n1 [|]]).

      - consider (SRPC Ready P0 /\ SRPC (Working n1) P1) by eauto using SRPC_recv_Q.
        smash_eq n0 n1; eauto with LTS.
        consider (serv_client n0 _).
        + enough (List.In (n0, Q, v0) I0) by eattac.
          unshelve eapply (Deq_neq_In _ `(Deq _ _ I0 I1)); eattac.
        + consider (proc_client n0 P1); eattac.
        + attac.

      - consider (exists c', SRPC (Locked c' n1) P0 /\ SRPC (Working c') P1) by eauto using SRPC_recv_R.
        smash_eq n0 c'; eauto with LTS.
        consider (serv_client n0 _).
        + enough (List.In (n0, Q, v0) I0) by eattac.
          unshelve eapply (Deq_neq_In _ `(Deq _ _ I0 I1)); eattac.
        + hsimpl in *.
          consider (proc_client n0 (cont0 _)); eattac.
        + attac.

      - consider (exists c', SRPC (Working c') P0 /\ SRPC (Locked c' n1) P1) by eauto using SRPC_send_Q.
        smash_eq n0 c'; eauto with LTS.
        consider (serv_client n0 _).
        + attac.
        + consider (proc_client n0 P1); eattac.
        + assert (List.In (n0, R, v0) O0 \/ List.In (n0, R, v0) [(n1, Q, v)]) as [|] by (hsimpl in * |-; eattac); eattac.

      - consider (SRPC (Working n1) P0 /\ SRPC Ready P1) by eauto using SRPC_send_R.
        smash_eq n0 n1; eauto with LTS.
        consider (serv_client n0 _).
        + attac.
        + consider (proc_client n0 P1); eattac.
          bs (Ready = Busy `(_)) by eattac.
        + assert (List.In (n0, R, v0) O0 \/ List.In (n0, R, v0) [(n1, R, v)]) as [|] by (hsimpl in * |-; eattac); eattac.

      - consider (exists c', SRPC (Working c') P0 /\ SRPC (Working c') P1) by eauto using SRPC_tau.
        smash_eq n0 c'; eauto with LTS.
        consider (serv_client n0 _).
        + attac.
        + consider (proc_client n0 P1); eattac.
        + attac.

    Qed.


    Lemma well_formed_invariant_tau [n a N0 N1] :
      (N0 =(NTau n a)=> N1) ->
      well_formed N0 ->
      well_formed N1.

    Proof.
      intros.
      consider (_ =(_)=> _).

      constructor.
      - eauto using well_formed_invariant_tau__service_wf with LTS.
      - eauto using well_formed_invariant_tau__locks_sound with LTS.
      - eauto using well_formed_invariant_tau__locks_complete with LTS.
    Qed.


    Lemma well_formed_invariant__well_formed_comm__sender_Q [n0 n1 v] [N0 N1 : Net] :
      n0 <> n1 ->
      (N0 =(NComm n0 n1 Q v)=> N1) ->
      well_formed N0 ->
      exists srpc, service_wf srpc (NetMod.get n0 N1).

    Proof.
      intros.
      assert (lock N1 n0 n1) by eauto using well_formed_send_Q_new_lock.
      consider (exists n', SRPC_serv (Locked n' n1) (NetMod.get n0 N1)).
      {
        assert (serv_lock [n1] (NetMod.get n0 N1)) by attac.
        eauto using lock_SRPC_Locked_serv with LTS.
      }

      exists (Locked n' n1).

      destruct (NetMod.get n0 N0) as [I0 P0 O0] eqn:?.
      consider (exists srpc0, service_wf srpc0 (NetMod.get n0 N0)) by attac.

      consider (N0 =(_)=> _); compat_hsimpl in *; doubt; rewrite `(NetMod.get n0 _ = _) in *.
      constructor; ltac1:(autounfold with SRPC); intros; simpl in *.
      - auto.
      - attac.
      - attac.
      - hsimpl in *.
        bs (serv_o (serv I2 P2 ((n1, Q, v) :: O2)) = []) by eauto using service_wf_R_in_out_nil.

      - enough (s = n1) by eattac.
        consider (exists c, srpc0 = Locked c s) by attac.
        hsimpl in *.
        assert (SRPC_serv (Locked c s) (serv I2 P2 ((n1, Q, v)::O2))) by attac.
        consider (Locked n' n1 = Locked c s) by attac.

      - hsimpl in *.
        assert (~ In (s, Q, v0) (removelast (serv_o (serv I2 P2 ((n1, Q, v) :: O2))))) by eauto using service_wf_Q_out_last_inv.
        destruct O2; attac.
      - hsimpl in *.
        assert (Deq (c, R) v0 ((n1, Q, v)::O2) ((n1, Q, v)::O')) by attac.
        attac.
      - compat_hsimpl in *; attac.
      - attac.
      - hsimpl in *.
        enough (O2 = []) by bs.
        eapply service_wf__Q_out_last_nil_inv with (O0:=[]);
          eauto; simpl in *; eauto.
      - attac.
      - attac.
      - attac.
    Qed.


    Lemma well_formed_invariant__well_formed_comm__sender_R [n0 n1 v] [N0 N1 : Net] :
      n0 <> n1 ->
      (N0 =(NComm n0 n1 R v)=> N1) ->
      well_formed N0 ->
      exists srpc, service_wf srpc (NetMod.get n0 N1).

    Proof.
      intros.

      consider (exists srpc, service_wf srpc (NetMod.get n0 N0)) by attac.
      exists srpc. (* The process did not change! *)

      assert (lock N0 n1 n0) by eauto using well_formed_send_R_lock_l.

      consider (exists n', service_wf (Locked n' n0) (NetMod.get n1 N0))
        by eauto using well_formed_recv_R_SRPC.

      destruct (NetMod.get n0 N0) as [I00 P00 O00] eqn:?.
      destruct (NetMod.get n0 N1) as [I01 P01 O01] eqn:?.
      destruct (NetMod.get n1 N0) as [I10 P10 O10] eqn:?.
      destruct (NetMod.get n1 N1) as [I11 P11 O11] eqn:?.

      consider (_ =(_)=> _); compat_hsimpl in *.
      constructor; ltac1:(autounfold with SRPC); intros;
        repeat (rewrite `(NetMod.get _ _ = _) in * ); hsimpl in *.
      - consider (service_wf srpc (serv _ P00 _)).
      - attac.
      - attac.
      - assert (In (s, R, v0) (serv_i (serv I00 P00 ((n1, R, v)::O01)))) by attac.
        consider (exists c', srpc = Locked c' s) by eauto using service_wf_R_in_lock_inv.
        assert (SRPC_serv (Locked c' s) (serv I00 P00 ((n1, R, v) :: O01))) by eauto using service_wf_SRPC_inv with LTS.
        attac.
      - consider (exists c', srpc = Locked c' s) by eauto using service_wf_Q_out_lock_inv with datatypes LTS.
        assert (SRPC_serv (Locked c' s) (serv I00 P00 ((n1, R, v) :: O01))) by eauto using service_wf_SRPC_inv with LTS.
        attac.
      - enough (~ In (s, Q, v0) (removelast ((n1, R, v)::O01))) by (destruct O01; eattac).
        eauto using service_wf_Q_out_last_inv.
      - smash_eq n1 c.
        1: { bs (In (n1, R, v0) O01) by attac. }
        enough (~ In (c, R, v') ((n1, R, v)::O')) by eattac.
        enough (Deq (c, R) v0 (serv_o (serv I00 P00 ((n1, R, v)::O01))) ((n1, R, v)::O')) by attac.
        now enough (Deq (c, R) v0 (serv_o (serv I00 P00 O01)) O') by attac.
      - attac.
      - attac.
      - enough (exists v0, In (s, Q, v0) ((n1, R, v)::O01)) by (hsimpl in *; destruct `(_ \/ _); attac).
        assert (serv_o (serv I00 P00 ((n1, R, v)::O01)) <> []) by attac.
        enough (srpc = Locked c s) by (subst; eauto using service_wf_lock_Q_inv).
        enough (SRPC_serv srpc (serv I00 P00 ((n1, R, v)::O01))) by attac.
        eauto using service_wf_SRPC_inv with LTS.
      - attac.
      - attac.
      - attac.
    Qed.

    Lemma well_formed_invariant__well_formed_comm__sender [n0 n1 t v] [N0 N1 : Net] :
      n0 <> n1 ->
      (N0 =(NComm n0 n1 t v)=> N1) ->
      well_formed N0 ->
      exists srpc, service_wf srpc (NetMod.get n0 N1).

    Proof.
      intros.
      destruct t;
        eauto using
          well_formed_invariant__well_formed_comm__sender_Q
        , well_formed_invariant__well_formed_comm__sender_R.

    Qed.


    Lemma well_formed_invariant__well_formed_comm__receiver_Q [n0 n1 v] [N0 N1 : Net] :
      n0 <> n1 ->
      (N0 =(NComm n0 n1 Q v)=> N1) ->
      well_formed N0 ->
      exists srpc, service_wf srpc (NetMod.get n1 N1).

    Proof.
      intros.

      consider (exists srpc, service_wf srpc (NetMod.get n1 N0)) by attac.
      exists srpc. (* The process did not change! *)

      assert (lock N1 n0 n1) by eauto using well_formed_send_Q_new_lock.
      assert (~ serv_client n0 (NetMod.get n1 N0)).
      {
        intros ?.
        absurd (lock N0 n0 n1).
        2: { attac. }
        bs (n0 <> n0) by eauto using lock_no_send.
      }

      destruct (NetMod.get n0 N0) as [I00 P00 O00] eqn:?.
      destruct (NetMod.get n0 N1) as [I01 P01 O01] eqn:?.
      destruct (NetMod.get n1 N0) as [I10 P10 O10] eqn:?.
      destruct (NetMod.get n1 N1) as [I11 P11 O11] eqn:?.

      consider (_ =(_)=> _);
      constructor; ltac1:(autounfold with SRPC); intros;
        repeat (rewrite `(NetMod.get _ _ = _) in * ); compat_hsimpl in * |-; hsimpl in *.
      - consider (service_wf srpc _); attac.
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
      - enough (exists c, SRPC_serv (Locked c s) (serv I10 P10 O10)) by attac.
        enough (exists c, srpc = Locked c s) by (hsimpl in * |-; eauto using service_wf_SRPC_inv with LTS).
        enough (In (s, R, v0) (serv_i (serv I10 P10 O10))) by eauto using service_wf_R_in_lock_inv.
        simpl in *.
        assert (In (s, R, v0) I10 \/ In (s, R, v0) [(n0, Q, v)]) as [|]; attac.
      - enough (exists c, SRPC_serv (Locked c s) (serv I10 P10 O10)) by attac.
        enough (exists c, srpc = Locked c s) by (hsimpl in * |-; eauto using service_wf_SRPC_inv with LTS).
        enough (In (s, Q, v0) (serv_o (serv I10 P10 O10))) by eauto using service_wf_Q_out_lock_inv.
        attac.

      - enough (~ In (s, Q, v0) (removelast ((n1, Q, v) :: O01))) by (destruct O01; attac).
        eauto with LTS.

      - attac.
      - enough (In (s, R, v0) (serv_i (serv I10 P10 O10))) by attac.
        enough (In (s, R, v0) I10) by attac.
        assert (In (s, R, v0) I10 \/ In (s, R, v0) [(n0, Q, v)]) as [|]; attac.

      - compat_hsimpl; attac.

      - assert (serv_o (serv I10 P10 O10) <> []) by attac.
        enough (srpc = Locked c s) by attac.
        assert (SRPC_serv srpc (serv I10 P10 O10)) by eauto using service_wf_SRPC_inv.
        attac.

      - smash_eq n0 c.
        1: { attac. }
        assert (In (c, Q, v0) I10 \/ In (c, Q, v0) [(n0, Q, v)]) as [|]; attac.

      - smash_eq n0 c.
        1: { attac. }
        assert (In (c, Q, v0) I10 \/ In (c, Q, v0) [(n0, Q, v)]) as [|]; attac.

      - smash_eq n0 c; attac.
    Qed.


    Lemma service_wf_SRPC_proc_inv [srpc S P] :
      service_wf srpc S ->
      serv_p S = P ->
      SRPC srpc P.

    Proof.
      intros.
      destruct S as [? ? ?]. hsimpl in *.
      eenough (SRPC_serv srpc (serv _ P _)); attac.
    Qed.

    #[export] Hint Resolve service_wf_SRPC_proc_inv : LTS.


    Lemma service_wf_lock_no_R [S srpc L n v I] :
      service_wf srpc S ->
      serv_lock L S ->
      I = serv_i S ->
      ~ In (n, R, v) I.

    Proof.
      intros.
      assert (SRPC_serv srpc &S) by attac.
      consider (exists s, serv_lock [s] &S) by eauto 4 using SRPC_serv_get_lock with LTS.
      consider (exists c, SRPC_serv (Locked c s) &S) by eauto using lock_SRPC_Locked_serv with LTS.
      destruct S as [I0 P0 O0]; hsimpl in *.
      intros ?.
      smash_eq n s.
      - hsimpl in *; bs.
      - assert (SRPC (Locked c s) P0) by attac.
        consider (exists c', srpc = Locked c' n) by eauto using service_wf_R_in_lock_inv.
        bs (Locked c' n = Locked c s) by attac.
    Qed.

    Lemma well_formed_lock_no_R [n0 n1 m1 v N I] :
      well_formed N ->
      lock N n0 n1 ->
      I = serv_i (NetMod.get n0 N) ->
      ~ In (m1, R, v) I.

    Proof.
      intros.
      consider (serv_lock [n1] (NetMod.get n0 N)).
      consider (exists srpc, service_wf srpc (NetMod.get n0 N)) by attac.
      eauto using service_wf_lock_no_R with LTS.
    Qed.

    #[export] Hint Resolve well_formed_lock_no_R : LTS.


    Lemma well_formed_R_derive_lock [n0 n1 m0 m1 N0 N1 v] :
      well_formed N0 ->
      (N0 =(NComm n1 n0 R v)=> N1) ->
      lock N1 m0 m1 ->
      lock N0 m0 m1.

    Proof.
      intros.

      assert (n0 <> m0) by (intros ?; attac; bs (~ lock N1 m0 m1) by eauto using well_formed_send_R_receiver_no_lock with LTS).

      smash_eq n1 m0.
      - consider (_ =(_)=> _); smash_eq n0 n1; hsimpl in *.
        unfold lock, lock_set in *.
        hsimpl in *.
        exists L. split > [attac|].

        consider (exists srpc, service_wf srpc (NetMod.get n1 N0)) by attac.
        bs (~ serv_lock L &S) by eauto using service_wf_send_R_no_lock_r.
      - assert (NetMod.get m0 N0 = NetMod.get m0 N1) by attac.
        eapply lock_move_eq; eauto.
    Qed.


    Lemma well_formed_Q_bad_sender_derive_lock [n0 n1 m0 m1 N0 N1 v] :
      well_formed N0 ->
      (N0 =(NComm n0 n1 Q v)=> N1) ->
      n0 <> m0 ->
      lock N1 m0 m1 ->
      lock N0 m0 m1.

    Proof.
      intros.

      unfold lock, lock_set in *; hsimpl in *.
      exists L. split > [attac|].

      smash_eq n0 n1; hsimpl in *.
      1: {attac. }

      smash_eq m0 n1.
      2: { attac. }

      consider (_ =(_)=> _); hsimpl in *.
      eauto using serv_recv_Q_derive_lock.
    Qed.


    Lemma well_formed_invariant__well_formed_comm__receiver_R [n0 n1 v] [N0 N1 : Net] :
      n0 <> n1 ->
      (N0 =(NComm n0 n1 R v)=> N1) ->
      well_formed N0 ->
      exists srpc, service_wf srpc (NetMod.get n1 N1).

    Proof.
      intros.
      consider (exists srpc, service_wf srpc (NetMod.get n1 N0)) by attac.
      exists srpc. (* The process did not change! *)

      assert (lock N0 n1 n0) by eauto using well_formed_reply_lock.
      consider (exists n', service_wf (Locked n' n0) (NetMod.get n1 N0))
        by eauto using well_formed_recv_R_SRPC.

      destruct (NetMod.get n0 N0) as [I00 P00 O00] eqn:?.
      destruct (NetMod.get n0 N1) as [I01 P01 O01] eqn:?.
      destruct (NetMod.get n1 N0) as [I10 P10 O10] eqn:?.
      destruct (NetMod.get n1 N1) as [I11 P11 O11] eqn:?.

      consider (O10 = []) by attac.
      assert (forall s v, ~ In (s, R, v) I10) by (eauto using well_formed_lock_no_R, eq_sym with LTS).

      consider (_ =(_)=> _); compat_hsimpl in *.
      constructor; ltac1:(autounfold with SRPC); intros;
        repeat (rewrite `(NetMod.get _ _ = _) in * ); hsimpl in *.
      - consider (service_wf srpc (serv _ P10 _)).
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

    Lemma well_formed_invariant__well_formed_comm__receiver [n0 n1 t v] [N0 N1 : Net] :
      n0 <> n1 ->
      (N0 =(NComm n0 n1 t v)=> N1) ->
      well_formed N0 ->
      exists srpc, service_wf srpc (NetMod.get n1 N1).

    Proof.
      intros.
      destruct t;
        eauto using
          well_formed_invariant__well_formed_comm__receiver_Q
        , well_formed_invariant__well_formed_comm__receiver_R.
    Qed.


    Lemma well_formed_invariant__well_formed_comm__self_Q [n0 v] [N0 N1 : Net] :
      (N0 =(NComm n0 n0 Q v)=> N1) ->
      well_formed N0 ->
      exists srpc, service_wf srpc (NetMod.get n0 N1).

    Proof.
      intros.

      consider (exists srpc, service_wf srpc (NetMod.get n0 N0)) by attac.
      exists srpc. (* The process did not change! *)

      assert (lock N1 n0 n0) by eauto using well_formed_send_Q_new_lock.
      assert (~ serv_client n0 (NetMod.get n0 N0)).
      {
        intros ?.
        absurd (lock N0 n0 n0).
        2: { attac. }
        bs (n0 <> n0) by eauto using lock_no_send.
      }
      consider (exists n', SRPC_serv (Locked n' n0) (NetMod.get n0 N1)).
      {
        assert (serv_lock [n0] (NetMod.get n0 N1)) by attac.
        eauto using lock_SRPC_Locked_serv with LTS.
      }

      destruct (NetMod.get n0 N0) as [I0 P0 O0] eqn:?.
      destruct (NetMod.get n0 N1) as [I1 P1 O1] eqn:?.

      consider (N0 =(_)=> _); compat_hsimpl in *; doubt; rewrite `(NetMod.get n0 _ = _) in *.
      compat_hsimpl in *; rename I2 into I0.
      constructor; ltac1:(autounfold with SRPC); intros; simpl in *.
      - consider (service_wf srpc (serv _ P1 _)).
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
      bs (serv_o (serv I0 P1 ((n0, Q, v) :: O1)) = []) by eauto using service_wf_R_in_out_nil.

    - enough (s = n0) by eattac.
      consider (exists c, srpc = Locked c s) by attac.
      assert (SRPC_serv (Locked c s) (serv I0 P1 ((n0, Q, v)::O1))) by attac.
      consider (Locked n' n0 = Locked c s) by attac.
    - assert (~ In (s, Q, v0) (removelast (serv_o (serv I0 P1 ((n0, Q, v) :: O1))))) by eauto using service_wf_Q_out_last_inv.
      destruct O1; attac.
    - assert (Deq (c, R) v0 ((n0, Q, v)::O1) ((n0, Q, v)::O')) by attac.
      attac.
    - bs (O1 = []) by (eapply service_wf__Q_out_last_nil_inv with (O0:=[]); eauto; simpl in *; eauto).
    - assert (~ In (s, R, v') I0) by attac.
      intros ?.
      apply `(~ In _ _).
      assert (In (s, R, v') I0 \/ In (s, R, v') [(n0, Q, v)]) as [|]; attac.
    - bs (O1 = []) by (eapply service_wf__Q_out_last_nil_inv with (O0:=[]); eauto; simpl in *; eauto).
    - assert (In (c, Q, v0) I0 \/ In (c, Q, v0) [(n0, Q, v)]) as [|] by attac; doubt.
      unfold lock, lock_set in *; hsimpl in *.
      bs.
    - assert (In (c, Q, v0) I0 \/ In (c, Q, v0) [(n0, Q, v)]) as [|] by attac; doubt.
      unfold lock, lock_set in *; hsimpl in *.
      bs.
    - unfold lock, lock_set in *; hsimpl in *.
      bs.
    Qed.


    Lemma well_formed_invariant__well_formed_comm__self [n0 t v] [N0 N1 : Net] :
      (N0 =(NComm n0 n0 t v)=> N1) ->
      well_formed N0 ->
      exists srpc, service_wf srpc (NetMod.get n0 N1).

    Proof.
      intros.
      destruct t.
      - eauto using well_formed_invariant__well_formed_comm__self_Q.
      - bs (n0 <> n0) by eauto using well_formed_no_self_reply.
    Qed.


    Lemma well_formed_invariant_comm__service_wf [n0 n1 t v] [N0 N1 : Net] :
      (N0 =(NComm n0 n1 t v)=> N1) ->
      well_formed N0 ->
      service_wf_net N1.

    Proof.
      repeat (intros ?).
      smash_eq_on n n0 n1; subst.
      - eauto using well_formed_invariant__well_formed_comm__self.
      - eauto using well_formed_invariant__well_formed_comm__sender.
      - eauto using well_formed_invariant__well_formed_comm__receiver.
      - replace (NetMod.get n N1) with (NetMod.get n N0); attac.
    Qed.

    Lemma well_formed_invariant_comm__locks_sound_Q [n0 n1 v] [N0 N1 : Net] :
      (N0 =(NComm n0 n1 Q v)=> N1) ->
      well_formed N0 ->
      locks_sound N1.

    Proof.
      intros * ? ? m0 m1 ?.
      assert (lock N1 n0 n1) by eauto using well_formed_send_Q_new_lock.
      assert (~ lock N0 n0 n1) by (bs (n0 <> n0) by eauto using lock_no_send).
      assert (~ serv_client n0 (NetMod.get n1 N0)) by attac.

      smash_eq n0 m0.
      1: { assert (SRPC_net N1) by attac.
           consider (m1 = n1) by (eapply SRPC_lock_set_uniq; eauto).
           consider (_ =(_)=> _); compat_hsimpl in *.
           attac.
      }

      assert (lock N0 m0 m1) by eauto using well_formed_Q_bad_sender_derive_lock.

      consider (_ =(_)=> _); hsimpl in *.
      consider (serv_client m0 (NetMod.get m1 N0)) by attac; compat_hsimpl in *.
      - smash_eq_on m1 n1 n0; subst; compat_hsimpl; attac.
      - smash_eq_on m1 n1 n0; subst; compat_hsimpl; attac.
      - smash_eq_on m1 n1 n0; subst; compat_hsimpl; attac.
    Qed.

    Lemma well_formed_invariant_comm__locks_sound_R [n0 n1 v] [N0 N1 : Net] :
      (N0 =(NComm n0 n1 R v)=> N1) ->
      well_formed N0 ->
      locks_sound N1.

    Proof.
      intros * ? ? m1 m0 ?.
      assert (lock N0 n1 n0) by eauto using well_formed_send_R_lock_l.
      assert (~ lock N1 n1 n0) by eauto using well_formed_send_R_receiver_no_lock.

      assert (n0 <> n1) by eauto using well_formed_no_self_reply.

      smash_eq n1 m1.
      1: { bs (n0 = m0) by eauto using SRPC_net_no_relock with LTS. }

      assert (lock N0 m1 m0) by eauto using well_formed_R_derive_lock.

      consider (_ =(_)=> _); hsimpl in *.
      consider (serv_client m1 (NetMod.get m0 N0)) by attac; compat_hsimpl in *.
      - smash_eq_on m0 n1 n0; subst; compat_hsimpl; attac.
      - smash_eq_on m0 n1 n0; subst; compat_hsimpl; attac.
      - smash_eq_on m0 n1 n0; subst; compat_hsimpl; attac.
    Qed.

    Lemma well_formed_invariant_comm__locks_sound [n0 n1 t v] [N0 N1 : Net] :
      (N0 =(NComm n0 n1 t v)=> N1) ->
      well_formed N0 ->
      locks_sound N1.

    Proof.
      destruct t.
      - eauto using well_formed_invariant_comm__locks_sound_Q.
      - eauto using well_formed_invariant_comm__locks_sound_R.
    Qed.


    Lemma well_formed_invariant_comm__locks_complete_Q [n0 n1 v] [N0 N1 : Net] :
      (N0 =(NComm n0 n1 Q v)=> N1) ->
      well_formed N0 ->
      locks_complete N1.

    Proof.
      intros * ? ? m0 m1 ?.
      assert (lock N1 n0 n1) by eauto using well_formed_send_Q_new_lock.
      assert (~ lock N0 n0 n1) by bs (n0 <> n0) by eauto using lock_no_send.
      assert (~ lock N0 n0 m1) by bs (n0 <> n0) by eauto using lock_no_send.

      assert (~ serv_lock [n1] (NetMod.get n0 N0)) by attac. clear H3.
      assert (serv_lock [n1] (NetMod.get n0 N1)) by attac. clear H4.

      assert (service_wf_net N1) by eauto using well_formed_invariant_comm__service_wf.

      assert (serv_client n0 (NetMod.get n1 N1)) by (consider (_ =(_)=> _); compat_hsimpl in *; attac).

      smash_eq n1 m1.
      2: {
        assert (serv_client m0 (NetMod.get m1 N0)).
        {
          consider (_ =(_)=> _); compat_hsimpl in *.
          smash_eq n1 n0; attac.
          smash_eq m1 n0; attac.
          consider (serv_client m0 _); attac.
        }
        assert (lock N0 m0 m1) by attac.
        eauto using lock_Q_preserve.
      }

      enough (serv_lock [n1] (NetMod.get m0 N1)) by attac.

      smash_eq n0 m0.
      smash_eq n1 m0.
      2: {
        replace (NetMod.get m0 N1) with (NetMod.get m0 N0)
        by (eapply act_particip_stay with (a := NComm n0 n1 Q v); attac).
        enough (lock N0 m0 n1) by attac.
        enough (serv_client m0 (NetMod.get n1 N0)) by attac.
        consider (_ =(_)=> _); compat_hsimpl in *.
        consider (serv_client m0 _); attac.
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

      consider (On01 = []) by consider (serv_lock _ (serv _ _ On01)).

      consider (_ =(_)=> _); smash_eq n0 n1; compat_hsimpl in *.
      hsimpl in *.

      enough (serv_lock [n1] (NetMod.get n1 N0)).
      {
        rewrite `(NetMod.get n1 N0 = _) in *.
        consider (serv_lock [n1] _); constructor; attac.
        intros ?.
        assert (In (n, R, v0) In10 \/ In (n, R, v0) [(n0, Q, v)]) as [|]; eattac.
      }

      enough (serv_client n1 (NetMod.get n1 N0)) by attac.
      consider (serv_client n1 _); attac.
      assert (In (n1, Q, v0) In10 \/ In (n1, Q, v0) [(n0, Q, v)]) as [|]; attac.
    Qed.


    Lemma well_formed_invariant_comm__locks_complete_R [n0 n1 v] [N0 N1 : Net] :
      (N0 =(NComm n0 n1 R v)=> N1) ->
      well_formed N0 ->
      locks_complete N1.

    Proof.
      intros * ? ? m1 m0 ?.

      assert (lock N0 n1 n0) by eauto using well_formed_send_R_lock_l.
      assert (~ lock N1 n1 n0) by eauto using well_formed_send_R_receiver_no_lock.

      assert (serv_lock [n0] (NetMod.get n1 N0)) by attac. clear H2.
      assert (~ serv_lock [n0] (NetMod.get n1 N1)) by attac. clear H3.
      enough (serv_lock [m0] (NetMod.get m1 N1)) by attac.

      assert (n0 <> n1) by eauto using well_formed_no_self_reply.
      assert (serv_client n1 (NetMod.get n0 N0)) by attac.

      assert (service_wf_net N1) by eauto using well_formed_invariant_comm__service_wf.

      (* maybe I need a script for this... *)
      destruct (NetMod.get n0 N0) as [In00 Pn00 On00] eqn:?.
      destruct (NetMod.get n0 N1) as [In01 Pn01 On01] eqn:?.
      destruct (NetMod.get n1 N0) as [In10 Pn10 On10] eqn:?.
      destruct (NetMod.get n1 N1) as [In11 Pn11 On11] eqn:?.
      destruct (NetMod.get m0 N0) as [Im00 Pm00 Om00] eqn:?.
      destruct (NetMod.get m0 N1) as [Im01 Pm01 Om01] eqn:?.
      destruct (NetMod.get m1 N0) as [Im10 Pm10 Om10] eqn:?.
      destruct (NetMod.get m1 N1) as [Im11 Pm11 Om11] eqn:?.

      consider (On10 = []) by consider (serv_lock _ (serv _ _ On10)).

      consider (_ =(_)=> _); compat_hsimpl in *.
      smash_eq m0 m1 n0 n1; compat_hsimpl in *|-.
      - enough (serv_lock [m0] (NetMod.get m0 N0)) by bs.
        enough (serv_client m0 (NetMod.get m0 N0)) by attac.
        rewrite `(NetMod.get m0 N0 = _).
        consider (serv_client m0 _); attac.
      - constructor.
        + attac.
        + enough (serv_lock [m0] (NetMod.get m0 N0)) by bs.
          enough (serv_client m0 (NetMod.get m0 N0)) by attac.
          rewrite `(NetMod.get m0 N0 = _).
          consider (serv_client m0 (serv _ _ [])); attac.
          assert (In (m0, Q, v0) Im10 \/ In (m0, Q, v0) [(n0, R, v)]) as [|]; eattac.
        + intros. hsimpl in *.
          intros ?.
          assert (In (n, R, v0) Im10 \/ In (n, R, v0) [(n0, R, v)]) as [|]; eattac.
          assert (AnySRPC_serv (serv Im10 Pm01 [])) by attac.
          consider (exists c, SRPC_serv (Locked c n0) (serv Im10 Pm01 [])) by eauto using lock_SRPC_Locked_serv.
          consider (exists c', SRPC_serv (Locked c' n) (serv Im10 Pm01 [])).
          {
            consider (exists srpc, service_wf srpc (serv Im10 Pm01 [])) by attac.
            consider (exists c', srpc = Locked c' n) by attac.
            exists c'; eauto using service_wf_SRPC_inv.
          }

          bs (Locked c' n = Locked c n0).
      - enough (serv_lock [m0] (NetMod.get m0 N0)) by bs.
        enough (serv_client m0 (NetMod.get m0 N0)) by attac.
        rewrite `(NetMod.get m0 N0 = _).
        consider (serv_client m0 _); attac.
      - exfalso.
        consider (exists srpc, service_wf srpc (NetMod.get m0 N0)) by attac.
        rewrite `(NetMod.get m0 N0 = _) in *.
        consider (serv_client m1 (serv _ _ Om01)).
        + bs.
        + absurd (proc_client m1 Pm01); auto.
          eauto using well_formed_in_net_R_excl_c with LTS.
        + assert (Deq (m1, R) v ((m1, R, v)::Om01) Om01); attac.
      - enough (serv_client m1 (NetMod.get m0 N0)) by (rewrite <- `(NetMod.get m1 N0 = _); attac).
        consider (serv_client m1 _); attac.
      - enough (serv_lock [m0] (NetMod.get m1 N0)) by bs.
        enough (serv_client m1 (NetMod.get m0 N0)) by attac.
        consider (serv_client m1 _); attac.
        assert (In (m1, Q, v0) Im00 \/ In (m1, Q, v0) [(m1, R, v)]) as [|]; attac.
      - enough (serv_client m1 (NetMod.get m0 N0)) by (rewrite <- `(NetMod.get m1 N0 = _); attac).
        consider (serv_client m1 _); attac.
        assert (In (m1, Q, v0) Im00 \/ In (m1, Q, v0) [(n0, R, v)]) as [|]; attac.
      - enough (serv_lock [m0] (NetMod.get m1 N0)) by bs.
        enough (serv_client m1 (NetMod.get m0 N0)) by attac.
        attac.
      - constructor; attac.
        + enough (serv_lock [m0] (NetMod.get m1 N0)); attac.
        + intros ?.
          assert (In (n, R, v0) Im10 \/ In (n, R, v0) [(n0, R, v)]) as [|]; attac.
          assert (AnySRPC_serv (serv Im10 Pm10 [])) by attac.
          consider (exists c, SRPC_serv (Locked c n0) (serv Im10 Pm10 [])) by eauto using lock_SRPC_Locked_serv.
          consider (exists c', SRPC_serv (Locked c' n) (serv Im10 Pm10 [])).
          {
            consider (exists srpc, service_wf srpc (serv Im10 Pm10 [])) by attac.
            consider (exists c', srpc = Locked c' n) by eattac.
            exists c'; eauto using service_wf_SRPC_inv.
          }

          bs (Locked c' n = Locked c n0).
      - rewrite <- `(NetMod.get m1 _ = _).
        attac.
        (* TODO compress those cases *)
    Qed.

    Lemma well_formed_invariant_comm__locks_complete [n0 n1 t v] [N0 N1 : Net] :
      (N0 =(NComm n0 n1 t v)=> N1) ->
      well_formed N0 ->
      locks_complete N1.

    Proof.
      destruct t.
      - eauto using well_formed_invariant_comm__locks_complete_Q.
      - eauto using well_formed_invariant_comm__locks_complete_R.
    Qed.


    Hint Resolve trans_Serv | 0 : typeclass_instances.
    Lemma well_formed_invariant_comm [n0 n1 t] [v] [N0 N1 : Net] :
      (N0 =(NComm n0 n1 t v)=> N1) ->
      well_formed N0 ->
      well_formed N1.

    Proof.
      intros.

      constructor.
      - eauto using well_formed_invariant_comm__service_wf with LTS.
      - eauto using well_formed_invariant_comm__locks_sound with LTS.
      - eauto using well_formed_invariant_comm__locks_complete with LTS.
    Qed.


    Theorem well_formed_invariant : trans_invariant well_formed always.

    Proof.
      unfold trans_invariant.
      intros.
      destruct a.
      - eauto using well_formed_invariant_tau.
      - eauto using well_formed_invariant_comm.
    Qed.


    #[export] Hint Resolve well_formed_invariant : inv.
    #[export] Hint Extern 0 (well_formed _) => solve_invariant : LTS.

    Check well_formed_invariant.
End SRPC_NET_F.

Module Type SRPC_NET(Conf : SRPC_NET_CONF) := Conf <+ SRPC_NET_PARAMS <+ SRPC_NET_F.
