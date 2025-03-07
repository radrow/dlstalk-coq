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
Require Import DlStalk.Locks.

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


Module Type SRPC_CONF := LOCKS_CONF.

Module Type SRPC_PARAMS(Conf : SRPC_CONF).
  Declare Module Export Locks : LOCKS(Conf).
End SRPC_PARAMS.

Module SRPC_DEFS(Import Conf : SRPC_CONF)(Import Params : SRPC_PARAMS(Conf)).
  (** SRPC process handling a request from the client [c] *)
    Inductive SRPC_Busy_State (c : Name) :=
    | BWork : SRPC_Busy_State c
    | BLock (s : Name) : SRPC_Busy_State c
    .

    #[export] Hint Constructors SRPC_Busy_State : LTS.


    (** Behavioral description of an Single-threaded RPC process *)
    Inductive SRPC_Busy [c] : SRPC_Busy_State c -> Proc -> Prop :=
    | SRPC_Busy_Work [P0]
        (* If sends a reply, then to the client. *)
        (HReply : forall c' v P1, (P0 =(Send (c', R) v)=> P1) -> c = c')

        (* If sends a query, then locked. *)
        (HQuery : forall s v P1, (P0 =(Send (s, Q) v)=> P1) -> SRPC_Busy (BLock c s) P1)

        (* If taus, then still working *)
        (HTau : forall P1, (P0 =(Tau)=> P1) -> SRPC_Busy (BWork c) P1)

        (* Is not a receiving process. Note that the below does not work: *)
        (* (forall n v P1, P0 =(Recv n v)=> P1 -> False) -> *)
        (* Because that would allow the process to get stuck in a state in which it receives but
      doesn't accept anything. That would be considered a lock on empty set and we don't want
      that. *)
        (HNoRecv : forall h, P0 <> PRecv h)

        (* We assume 100% uptime. We are in academia, after all. *)
        (HNoEnd : P0 <> PEnd)
      : SRPC_Busy (BWork c) P0

    | SRPC_Busy_Lock [s P0]
        (* Accepts ALL replies from server *)
        (HReplyAll : forall v, exists P1, (P0 =(Recv (s, R) v)=> P1))
        (* Accepts ONLY replies and ONLY from server *)
        (HReplyOnly : forall a P1, P0 =(a)=> P1 -> exists v, a = Recv (s, R) v)
        (* If recvs a reply, moves to busy *)
        (HRecvR : forall a P1, P0 =(a)=> P1 -> SRPC_Busy (BWork c) P1)
      : SRPC_Busy (BLock c s) P0
    .


    (** SRPC state of any service *)
    Inductive SRPC_State :=
    | Free : SRPC_State
    | Busy [c] : SRPC_Busy_State c -> SRPC_State
    .

    #[export] Hint Constructors SRPC_State : LTS.


    Notation "'Work'" := (fun c => Busy (BWork c)) (at level 30).
    Notation "'Lock'" := (fun c s => Busy (BLock c s)) (at level 30).

    Notation "'Work' c" := (Busy (BWork c)) (at level 200) : type_scope.
    Notation "'Lock' c s" := (Busy (BLock c s)) (at level 200) : type_scope.


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

    | SRPC_Busy_ [P0 c]
        (srpc : SRPC_Busy_State c)
        (HBusy : SRPC_Busy srpc P0)
        (HReply : forall v P1, P0 =(Send (c, R) v)=> P1 -> SRPC Free P1)
        (HQuery : forall s v P1, P0 =(Send (s, Q) v)=> P1 -> SRPC (Lock c s ) P1)
        (HRecv : forall s v P1, P0 =(Recv (s, R) v)=> P1 -> SRPC (Work c) P1)
        (HTau : forall P1, P0 =(Tau)=> P1 -> SRPC (Work c) P1)
      : SRPC (Busy srpc) P0
    .


    Definition SRPC_serv srpc S := match S with serv _ P _ => SRPC srpc P end.

    Definition AnySRPC_serv S := exists s, SRPC_serv s S.

    Definition AnySRPC P := exists s, SRPC s P.

    #[export] Hint Transparent SRPC_serv AnySRPC AnySRPC_serv : LTS.

    (* TODO this :) *)
    Lemma srpc_inv
      : forall (srpc : SRPC_State) (P0 : Proc) (P : Prop),

        (forall (h : NameTag -> option (Val -> Proc))
           (hq : Name -> Val -> Proc),
            (forall c, match h (c, Q) with
                  | None => False
                  | Some cont => forall v, cont v = hq c v
                  end
            ) ->
            (forall c v, SRPC (Work c) (hq c v)) ->
            (forall c, h (c, R) = None) ->
            P0 = PRecv h ->
            srpc = Free ->
            P
        ) ->

        (forall (P1 : Proc) c,
            SRPC (Work c) P1 ->
            STau P1 = P0 ->
            srpc = Work c ->
            P
        ) ->

        (forall (P1 : Proc) c s v,
            SRPC (Lock c s) P1 ->
            P0 = PSend (s, Q) v P1 ->
            srpc = Work c ->
            P
        ) ->

        (forall (P1 : Proc) c v,
           SRPC Free P1 ->
           P0 = PSend (c, R) v P1 ->
           srpc = Work c ->
           P
        ) ->

        (forall (c s : Name)
           (h : NameTag -> option (Val -> Proc))
           (hr : Name -> Val -> Proc),
            (match h (s, R) with
             | None => False
             | Some cont => forall v, cont v = hr s v
             end
            ) ->
            (forall v, SRPC (Work c) (hr s v)) ->
            (forall n t, n <> s -> h (n, t) = None) ->
            (forall n, h (n, Q) = None) ->
            P0 = PRecv h ->
            srpc = Free ->
            P
        ) ->

        SRPC srpc P0 -> P.
    Abort.


    Ltac2 rec destruct_SRPC (hs : ident) (htr : ident option) :=
      let hs_h := hyp hs in
      match! (Constr.type hs_h) with
      | AnySRPC_serv ?p =>
          let srpc := Fresh.in_goal @srpc in
          destruct $hs_h as [$srpc $hs];
          destruct_SRPC hs htr
      | AnySRPC ?p =>
          let srpc := Fresh.in_goal @srpc in
          destruct $hs_h as [$srpc $hs];
          destruct_SRPC hs htr
      | SRPC_serv ?srpc (serv _ _ _) =>
          simpl in $hs;
          destruct_SRPC hs htr
      | SRPC_serv ?srpc ?p =>
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
                     [ bs
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
                     [ bs
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
      | SRPC_Busy ?srpc ?p =>
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
                     [ bs
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
                           try (inversion $htr_h; bs)
                       end
                     ]

                 | ssubst;
                   first
                     [ bs
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
End SRPC_DEFS.

Module Type SRPC_F(Import Conf : SRPC_CONF)(Import Params : SRPC_PARAMS(Conf)).
  Module Import SrpcDefs := SRPC_DEFS(Conf)(Params).

  (* This is to prevent stupid unfolding, but preserve inference from SRPC *)
  Lemma SRPC_SRPC_serv : forall [s S I P O], S = serv I P O -> SRPC s P <-> SRPC_serv s S.
  Proof. split; intros; subst; eauto. Qed.

  Lemma AnySRPC_AnySRPC_serv : forall [S I P O], S = serv I P O -> AnySRPC P <-> AnySRPC_serv S.
  Proof. unfold AnySRPC_pq. split; intros; subst; eauto. Qed.

  Lemma SRPC_AnySRPC : forall [s P], SRPC s P -> AnySRPC P.
  Proof. unfold AnySRPC. eauto. Qed.

  Lemma SRPC_pq_AnySRPC_serv : forall [s P], SRPC_serv s P -> AnySRPC_serv P.
  Proof. unfold AnySRPC_pq. eauto. Qed.


  #[export] Hint Immediate SRPC_SRPC_serv AnySRPC_AnySRPC_serv : LTS.
  #[export] Hint Resolve -> SRPC_SRPC_serv AnySRPC_AnySRPC_serv 10 : LTS.
  #[export] Hint Rewrite <- SRPC_SRPC_serv AnySRPC_AnySRPC_serv using spank : LTS.

  #[export] Hint Resolve SRPC_AnySRPC SRPC_pq_AnySRPC_serv : LTS.

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
  Lemma trans_invariant_AnySRPC_serv : trans_invariant AnySRPC_serv always.

  Proof.
    intros N0 N1 a T Hsrpc _.
    kill T; auto.
    all: destruct SRPC Hsrpc H; eattac.
  Qed.

  #[export] Hint Resolve trans_invariant_AnySRPC_serv : inv.
  #[export] Hint Extern 10 (AnySRPC_serv _) => solve_invariant : LTS.


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


  Lemma AnySRPC_STau_inv P :
    AnySRPC (STau P) <-> exists c, SRPC (Work c) (STau P).

  Proof.
    split; intros.
    - kill H.
      assert (STau P =(Tau)=> P ) as T by attac.
      kill H0.
      1: apply HQueryOnly in T; eattac.
      exists c.
      have (SRPC_Busy srpc (STau P)).
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
      have (SRPC_Busy srpc (PSend n v P)).
      kill HBusy.
      1: constructor; attac.
      apply HReplyOnly in T; attac.
    - eattac.
  Qed.


  Lemma SRPC_Busy_work_act [P0 : Proc] [c] :
    SRPC_Busy (BWork c) P0 ->
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


  Lemma SRPC_busy_reply [P0 P1 P2 path] [c c' v] [s : SRPC_Busy_State c] :
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


  Lemma SRPC_busy_reply_exists [P0] [c] [s : SRPC_Busy_State c] :
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
    - assert (SRPC_Busy (BWork c) P0) as Hsrpc by (constructor; eattac).
      specialize (SRPC_Busy_work_act Hsrpc) as [P1 [[v T]|[T|[s [v T]]]]].
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


  Lemma SRPC_work_inv [P : Proc] [c0 c1] [s0 : SRPC_Busy_State c0] [s1 : SRPC_Busy_State c1] :
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


  Lemma SRPC_pq_work_inv [S : Serv] [c0 c1] [s0 : SRPC_Busy_State c0] [s1 : SRPC_Busy_State c1] :
    SRPC_serv (Busy s0) S ->
    SRPC_serv (Busy s1) S ->
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
        bs.
    - kill Hsrpc1.
      + specialize (HQueryAll some_name some_val) as [P1 T].
        kill HBusy.
        1: kill T.
        apply HReplyOnly in T.
        destruct T.
        bs.

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
    SRPC_serv srpc0 S ->
    SRPC_serv srpc1 S ->
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


  Lemma SRPC_Work_PRecv_bs h c :
    SRPC (Work c) (PRecv h) <-> False.
  Proof. split; intros. consider (SRPC _ _). consider (SRPC_Busy _ _). bs.  contradiction. Qed.

  Lemma SRPC_Free_PSend_bs n v P1 :
    SRPC Free (PSend n v P1) <-> False.
  Proof. split; intros. consider (SRPC _ _). destruct n. specialize (HQueryAll n v). eattac. contradiction. Qed.

  Lemma SRPC_Free_STau_bs P1 :
    SRPC Free (STau P1) <-> False.
  Proof. split; intros. consider (SRPC _ _). specialize (HQueryAll some_name some_val). eattac. contradiction. Qed.

  Lemma SRPC_Lock_PSend_bs n v P1 c s :
    SRPC (Lock c s) (PSend n v P1) <-> False.
  Proof. split; intros. consider (SRPC _ _). destruct n.  consider (SRPC_Busy _ _); doubt. specialize (HReplyAll v); attac. contradiction. Qed.

  Lemma SRPC_Lock_STau_bs P1 c s :
    SRPC (Lock c s) (STau P1) <-> False.
  Proof. split; intros. consider (SRPC _ _). consider (SRPC_Busy _ _); doubt. specialize (HReplyAll some_val); attac. contradiction. Qed.

  #[export] Hint Rewrite ->
    SRPC_Work_PRecv_bs
    SRPC_Free_PSend_bs
    SRPC_Free_STau_bs
    SRPC_Lock_PSend_bs
    SRPC_Lock_STau_bs
    using spank
    : bs.

  Lemma SRPC_Work_recv_bs P0 P1 n v c :
    (P0 =(Recv n v)=> P1) ->
    SRPC (Work c) P0 <->
    False.
  Proof. attac. Qed.

  Lemma SRPC_Free_send_bs n v P1 :
    SRPC Free (PSend n v P1) <-> False.
  Proof. split; intros. consider (SRPC _ _). eattac. Qed.
  Lemma SRPC_Free_tau_bs P1 :
    SRPC Free (STau P1) <-> False.
  Proof. split; intros. consider (SRPC _ _). attac. Qed.
  Lemma SRPC_Free_recv_R_None_bs h n :
    h (n, R) <> None -> SRPC Free (PRecv h) <-> False.
  Proof. split; intros. consider (SRPC _ _). destruct (h (n, R)) eqn:P1v; doubt; specialize (HQueryOnly (Recv (n, R) some_val) (p some_val)) as [? ?]; eattac. contradiction. Qed.
  Lemma SRPC_Free_recv_R_Some_bs h n cont :
    h (n, R) = Some cont -> SRPC Free (PRecv h) <-> False.
  Proof. split; intros. consider (SRPC _ _). destruct (h (n, R)) eqn:P1v; doubt; specialize (HQueryOnly (Recv (n, R) some_val) (p some_val)) as [? ?]; eattac. contradiction. Qed.

  Lemma SRPC_Lock_send_bs n v c s P1 :
    SRPC (Lock c s) (PSend n v P1) <-> False.
  Proof. split; intros. consider (SRPC _ _). destruct n. kill HBusy. specialize (HReply0 n v). eattac. destruct (HReplyAll v). attac. contradiction. Qed.
  Lemma SRPC_Lock_tau_bs c s P1 :
    SRPC (Lock c s) (STau P1) <-> False.
  Proof. split; intros. consider (SRPC _ _). kill HBusy. specialize (HReply0 some_name some_val). eattac. destruct (HReplyAll some_val). attac. contradiction. Qed.
  Lemma SRPC_Lock_recv_Q_None_bs h n c s :
    h (n, Q) <> None -> SRPC (Lock c s) (PRecv h) <-> False.
  Proof. split; intros. consider (SRPC _ _). destruct (h (n, Q)) eqn:P1v; doubt; kill HBusy; doubt; specialize (HReplyOnly (Recv (n, Q) some_val) (p some_val)) as [? ?]; eattac. contradiction. Qed.
  Lemma SRPC_Lock_recv_Q_Some_bs h n c s cont :
    h (n, Q) = Some cont -> SRPC (Lock c s) (PRecv h) <-> False.
  Proof. split; intros. consider (SRPC _ _). destruct (h (n, Q)) eqn:P1v; doubt; kill HBusy; doubt; specialize (HReplyOnly (Recv (n, Q) some_val) (p some_val)) as [? ?]; eattac. contradiction. Qed.
  Lemma SRPC_Lock_recv_other_None_bs h n c s t :
    h (n, t) <> None -> n <> s -> SRPC (Lock c s) (PRecv h) <-> False.
  Proof. split; intros. destruct t. eapply SRPC_Lock_recv_Q_None_bs; eauto. apply H.
         consider (SRPC _ _). destruct (h (n, R)) eqn:P1v; doubt.
         kill HBusy; doubt. specialize (HReplyOnly (Recv (n, R) some_val) (p some_val)) as [? ?]; eattac. contradiction.
  Qed.
  Lemma SRPC_Lock_recv_other_Some_bs h n c s t cont :
    h (n, t) = Some cont -> n <> s -> SRPC (Lock c s) (PRecv h) <-> False.
  Proof. split; intros. destruct t. eapply SRPC_Lock_recv_Q_Some_bs; eauto.
         destruct (h (n, R)) eqn:?;
         consider (SRPC _ _). destruct (h (n, R)) eqn:P1v; doubt.
         kill HBusy; doubt. specialize (HReplyOnly (Recv (n, R) some_val) (p some_val)) as [? ?]; eattac. hsimpl in *.
         Set Printing All.
         change Tag with Tag_ in *. (* TODO THIS SHOULD NOT BE *)
         bs. bs.
  Qed.

  #[export] Hint Rewrite ->
    SRPC_Work_recv_bs
    SRPC_Free_send_bs
    SRPC_Free_tau_bs
    SRPC_Free_recv_R_None_bs
    SRPC_Free_recv_R_Some_bs
    SRPC_Lock_send_bs
    SRPC_Lock_tau_bs
    SRPC_Lock_recv_Q_None_bs
    SRPC_Lock_recv_Q_Some_bs
    SRPC_Lock_recv_other_None_bs
    SRPC_Lock_recv_other_Some_bs
    using spank
    : bs.


  (** SRPC process can be locked only on one thing *)
  Lemma SRPC_one_lock [P : Proc] [L] :
    AnySRPC P ->
    proc_lock L P ->
    length (nodup NAME.eq_dec L) = 1%nat.

  Proof.
    intros Hsrpc HL.

    destruct SRPC Hsrpc.
    - destruct P0; doubt.

      specialize (HL some_name) as [[HNoQ HNoIn] HYesR].
      specialize (HQueryAll some_name some_val) as [P1 T].
      bs.

    - destruct P; bs.
    - destruct P; try (kill HL).

      enough (Forall (eq s) L) as HAll.
      {
        eapply all_same_nodup_one in HAll as [HEq | HEq]; rewrite HEq in *; auto.

        specialize (HL s) as [[_ HYesR] _].
        hsimpl in *.
        exfalso.
        apply HYesR.
        bs.
      }

      apply (Forall_forall (eq s) L).
      intros.

      destruct (handle (x, R)) eqn:Hx.
      + specialize (HReplyOnly (Recv (x, R) some_val) (p some_val)) as [v' HEq]; ssubst; attac.
      + specialize (HL x) as [[HL _] _].
        bs.
  Qed.


  (** SRPC service can be locked only on one thing *)
  Lemma SRPC_pq_one_lock [S : Serv] [L] :
    AnySRPC_serv S ->
    pq_lock L S ->
    length (nodup NAME.eq_dec L) = 1%nat.

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
    pose (NoDup_nodup NAME.eq_dec L) as HNodup.

    consider (exists n : Name, nodup NAME.eq_dec L = [n]) by eauto using nodup_one.
    exists n.
    rewrite <- `(_ = [n]).

    apply (proc_lock_equiv_inv HL).
    - apply nodup_incl; auto with datatypes.
    - unfold incl.
      intros.
      apply (nodup_In NAME.eq_dec); auto.
  Qed.


  (** If SRPC service is locked, then it is known on who *)
  Lemma SRPC_pq_get_lock [S : Serv] [L] :
    AnySRPC_serv S ->
    pq_lock L S ->
    exists n, pq_lock [n] S.

  Proof.
    intros Hsrpc HL.
    destruct HL.
    consider (exists n, proc_lock [n] P) by eauto using SRPC_get_lock.
    exists n.

    enough (In n L) by attac.
    enough (incl [n] L) by attac.
    eauto using proc_lock_incl.
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
      destruct (NAME.eq_dec n s); subst; auto.
      destruct (handle (n, R)) eqn:HEq; doubt.
      assert (PRecv handle =(Recv (n, R) some_val)=> p some_val) as T'.
      constructor; auto.

      apply HReplyOnly in T' as [v HEq'].
      kill HEq'; auto.

    - destruct (handle (n, Q)) eqn:HEq; auto.
      assert (PRecv handle =(Recv (n, Q) some_val)=> p some_val) as T'.
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
      destruct (handle (s, R)) eqn:HEq; doubt.
      edestruct (HQueryOnly (Recv (s, R) some_val)) as (P1 & v & HEq' & Hsrpc).
      constructor.
      eapply HEq.
      kill HEq'.
      rewrite <- HEq in HL.
      specialize (HL s).
      kill HL.
      assert (List.In s [s]) by attac.
      apply H in H1.
      bs.
    - destruct P; doubt.
    - exists c.
      destruct P; doubt.
      destruct (NAME.eq_dec s0 s); subst.
      {
        constructor; eauto with LTS.
        constructor; eauto.
      }

      kill T.

      destruct (handle (s, R)) eqn:HEq; doubt.
      edestruct (HReplyOnly (Recv (s, R) some_val)) as [P1' HEq'].
      constructor. apply HEq.

      kill HEq'.

      specialize (HL s).
      attac.
  Qed.


  (** You can't judge locks of a service based on its SRPC-state, because the code may be in a *)
  (*   locked state, but there are messages to be sent *)
  Example SRPC_Lock_pq_lock [S : Serv] [s c] :
    SRPC_serv (Lock c s) S -> pq_lock [s] S.
  Abort.


  (** SRPC-lock state is complete for all SRPC services *)
  Lemma lock_SRPC_Lock_serv [S : Serv] [s] :
    AnySRPC_serv S ->
    pq_lock [s] S -> (exists c, SRPC_serv (Lock c s) S).

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
        bs (Lock c' n1 = Work c) by attac.
      + eapply lock_SRPC_Lock; eattac.
    - absurd (exists c', SRPC (Lock c' n1) P1).
      + intros Hx; hsimpl in Hx.
        bs (Lock c' n1 = Work c) by attac.
      + eapply lock_SRPC_Lock; eattac.
  Qed.


  (** You need at least a tau to change the lock *)
  Lemma SRPC_pq_no_relock [S0 S1 a n0 n1] :
    AnySRPC_serv S0 ->
    pq_lock [n0] S0 ->
    pq_lock [n1] S1 ->
    (S0 =(a)=> S1) ->
    n0 = n1.

  Proof.
    intros.
    consider (exists c0, SRPC_serv (Lock c0 n0) S0) by eauto using lock_SRPC_Lock_serv with LTS.
    consider (exists c1, SRPC_serv (Lock c1 n1) S1) by eauto using lock_SRPC_Lock_serv with LTS.
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
        bs.

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
      + bs.
      + specialize (HReplyAll some_val) as [P1 T].
        kill T.
    - constructor; eattac.

    - constructor; intros;
        destruct Hsrpc_p as [srpc Hsrpc_p];
        ltac1:(dependent destruction Hsrpc_p) >
                [|ltac1:(dependent destruction HBusy)].
      + split; intros.
        * destruct (handle (m, R)) eqn:HH; auto.
          assert (PRecv handle =(Recv (m, R) some_val)=> p some_val) as T by attac.
          apply HQueryOnly in T as (c & v & HEq & _).
          bs.
        * assert (PRecv handle =(Recv (n, Q) v)=> P v) as T by attac.
          apply HQueryOnly in T as (c & _ & _ & Hsrpc_n).
          apply C; eattac.
      + assert (PRecv handle =(Recv (n, Q) some_val)=> P some_val) as T by attac.
        kill T.
      + assert (PRecv handle =(Recv (n, Q) some_val)=> P some_val) as T by attac.
        apply HReplyOnly in T as (v & HEq).
        bs.
      + assert (PRecv handle =(Recv (n, R) some_val)=> P some_val) as T by attac.
        apply HQueryOnly in T as (c & v & HEq & _).
        bs.
      + assert (PRecv handle =(Recv (n, R) some_val)=> P some_val) as T by attac.
        kill T.
      + split; intros.
        * destruct (handle (m, Q)) eqn:HH; auto.
          assert (PRecv handle =(Recv (m, Q) some_val)=> p some_val) as T by attac.
          apply HReplyOnly in T as (v & HEq).
          bs.
        * assert (PRecv handle =(Recv (n, R) v)=> P v) as T by attac.
          apply HRecv in T as Hsrpc_n.
          apply C; eattac.
    - constructor.
      assert (STau P =(Tau)=> P) as T by attac.
      assert (AnySRPC P) by eattac.
      attac.
  Qed.

  #[export] Hint Resolve SRPC_Decisive : LTS.


  Lemma SRPC_Decisive_q [S] :
    AnySRPC_serv S ->
    Decisive_q S.
  Proof. intros. destruct S; eattac. Qed.

  #[export] Hint Resolve SRPC_Decisive_q : LTS.


  Lemma SRPC_tau_no_lock_r [S0 S1 L] :
    AnySRPC_serv S0 ->
    (S0 =(Tau)=> S1) ->
    ~ pq_lock L S1.

  Proof.
    intros; intros ?.
    consider (exists s, pq_lock [s] S1) by eauto using SRPC_pq_get_lock with LTS.
    consider (exists c, SRPC_serv (Lock c s) S1) by eauto using lock_SRPC_Lock_serv with LTS.
    consider (_ =(_)=> _); consider (pq_lock _ _); doubt; simpl in *.
    - destruct n as [n [|]].
      + assert (SRPC (Work n) P1) by eauto using SRPC_inv_recv_Q_r.
        bs (Work n = Lock c s) by attac.
      + consider (exists c', SRPC (Work c') P1) by eauto using SRPC_inv_recv_R_r.
        bs (Work c' = Lock c s) by attac.
    - consider (exists c', SRPC (Work c') P1) by eauto using SRPC_inv_tau_r.
      bs (Work c' = Lock c s) by attac.
  Qed.

End SRPC_F.

Module Type SRPC(Conf : SRPC_CONF) := Conf <+ SRPC_PARAMS <+ SRPC_F.
