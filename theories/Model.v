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

From DlStalk Require Import Tactics.
From DlStalk Require Import Lemmas.
From DlStalk Require Import ModelData.
From DlStalk Require Import LTS.
From DlStalk Require Import Que.


Module Type PROC_CONF.
  Include QUE_CONF.
End PROC_CONF.

Module Type PROC_PARAMS(Conf : PROC_CONF).
  Declare Module Export Que : QUE(Conf).
End PROC_PARAMS.

Module Type PROC_F(Conf : PROC_CONF)(Import Params : PROC_PARAMS(Conf)).
  Inductive Act {Payload : Set} : Set :=
  | Send (n : NameTag) (v : Payload) : Act
  | Recv (n : NameTag) (v : Payload) : Act
  | Tau
  .
  #[export] Hint Constructors Act : LTS.


  Definition PAct : Set := @Act Val.
  #[global] Hint Unfold PAct : LTS.
  #[global] Hint Transparent PAct : LTS.


  #[export] Instance gen_Act_PAct : gen_Act PAct :=
    {
      Payload := Val;
      send := Send;
      recv := Recv;
      ia a := a = Tau;

      ia_disjoint := ltac:(intros; split; discriminate);
      send_recv := ltac:(intros; discriminate);
      gact_rec := ltac:(destruct a; attac);
    }.

  #[export] Hint Unfold gen_Act_PAct : LTS.
  #[export] Hint Transparent gen_Act_PAct : LTS.

  #[export] Hint Extern 10 (ia _) => unfold ia; simpl : LTS.
  #[export] Hint Extern 10 (send _) => unfold send; simpl : LTS.
  #[export] Hint Extern 10 (recv _) => unfold recv; simpl : LTS.


  Lemma ia_PAct_inv : forall (a : PAct), ia a <-> a = Tau.
  Proof. split; intros H; kill H. Qed.

  #[export] Hint Rewrite -> @ia_PAct_inv using assumption : LTS LTS_concl.


  CoInductive Proc : Set :=
  | PEnd
  | PSend (n : NameTag) (v : Val) (P : Proc) : Proc
  | PRecv (handle : NameTag -> option (Val -> Proc)) : Proc
  | STau (P : Proc) : Proc
  .

  Fact unfold_Proc : forall (P : Proc),
      P = match P with
          | PRecv handle => PRecv handle
          | PSend n v P' => PSend n v P'
          | STau P' => STau P'
          | PEnd => PEnd
          end.
    intros.
    destruct P; auto.
  Qed.

  #[export] Hint Constructors Proc : LTS.


  Inductive ProcTrans : PAct -> Proc -> Proc -> Prop :=
  | PrTRecv [n v handle P]
    : handle n = Some P ->
      ProcTrans (Recv n v) (PRecv handle) (P v)

  | PrTSend n v P
    : ProcTrans (Send n v) (PSend n v P) P

  | PrTTau P
    : ProcTrans Tau (STau P) P
  .

  #[export] Hint Constructors ProcTrans : LTS.


  #[export]
    Instance trans_proc : LTS PAct Proc  :=
    {
      trans := ProcTrans
    }.
  #[export] Hint Unfold trans_proc : LTS.
  #[export] Hint Transparent trans_proc : LTS.


  Section Inversions.
    Lemma ProcTrans_Recv_inv n v P0 P1 :
      (P0 =(Recv n v)=> P1) <->
        exists h cont, P0 = PRecv h
                  /\ h n = Some cont
                  /\ P1 = cont v.
    Proof.
      repeat split; eattac.
      kill H; eattac.
    Qed.

    Lemma ProcTrans_Send_inv n v P0 P1 :
      (P0 =(Send n v)=> P1) <->
        P0 = PSend n v P1.
    Proof. eattac; kill H; attac. Qed.

    Lemma ProcTrans_Tau_inv P0 P1 :
      (P0 =(Tau)=> P1) <->
        P0 = STau P1.
    Proof. eattac; kill H; attac. Qed.

    Lemma ProcTrans_PRecv_inv handle a P1 :
      (PRecv handle =(a)=> P1) <->
        exists n v cont, a = Recv n v
                    /\ handle n = Some cont
                    /\ P1 = cont v.
    Proof. eattac; kill H; eattac. Qed.

    Lemma ProcTrans_PSend_inv n v a P0 P1 :
      (PSend n v P0 =(a)=> P1) <->
        a = Send n v /\ P0 = P1.
    Proof. eattac; kill H; eattac. Qed.

    Lemma ProcTrans_STau_inv a P0 P1 :
      (STau P0 =(a)=> P1) <->
        a = Tau /\ P0 = P1.
    Proof. attac; kill H; attac. Qed.
  End Inversions.
  #[export] Hint Rewrite -> @ProcTrans_Recv_inv @ProcTrans_Send_inv @ProcTrans_Tau_inv using assumption : LTS.
  #[export] Hint Rewrite -> @ProcTrans_PRecv_inv @ProcTrans_PSend_inv @ProcTrans_STau_inv using assumption : LTS.


  Inductive Serv := serv {serv_i : Que Val; serv_p : Proc; serv_o : Que Val}.
  #[export] Hint Constructors Serv : LTS.

  Inductive STrans : PAct -> Serv -> Serv -> Prop :=
  | STRecv [n v I0 I1 P O]
      (HEnq : Enq n v I0 I1)
    : STrans (Recv n v) (serv I0 P O) (serv I1 P O)

  | STPick [n v I0 I1 P0 P1 O]
      (HDeq : Deq n v I0 I1)
    : (P0 =(Recv n v)=> P1) ->
      STrans Tau (serv I0 P0 O) (serv I1 P1 O)

  | STSend [n v I P0 P1 O0 O1]
      (HEnq : Enq n v O0 O1)
    : (P0 =(Send n v)=> P1) ->
      STrans Tau (serv I P0 O0) (serv I P1 O1)

  | STPush {n v I P O}
    : STrans (Send n v) (serv I P ((n, v)::O)) (serv I P O)

  | STTau {I P0 P1 O}
    : (P0 =(Tau)=> P1) ->
      STrans Tau (serv I P0 O) (serv I P1 O)
  .


  #[export] Hint Constructors STrans : LTS.


  #[export]
    Instance trans_Serv : LTS PAct Serv  :=
    {
      trans := STrans
    }.

  #[export] Hint Unfold trans_Serv : LTS.
  #[export] Hint Transparent trans_Serv : LTS.


  Section Inversions.
    Lemma STrans_Recv_inv n v S0 S1 :
      (S0 =(Recv n v)=> S1) <-> exists I0 P0 O0, serv I0 P0 O0 = S0 /\ serv (I0 ++ [(n, v)]) P0 O0 = S1.
    Proof. eattac; kill H; eattac. Qed.

    Lemma STrans_Send_inv n v S0 S1 :
      (S0 =(Send n v)=> S1) <->
        exists I0 P0 O1, serv I0 P0 ((n, v)::O1) = S0 /\ serv I0 P0 O1 = S1.
    Proof. eattac; kill H; eattac. Qed.

    Lemma STrans_Tau_Recv_inv I0 O0 S1 handle :
      (serv I0 (PRecv handle) O0 =(Tau)=> S1) <->
        exists n v I1 P1, (PRecv handle =(Recv n v)=> P1) /\ Deq n v I0 I1 /\ S1 = serv I1 P1 O0.
    Proof.
      split; intros.
      - kill H; kill H0; eattac.
      - eattac.
    Qed.

    Lemma STrans_Tau_Send_inv n v I0 P0 O0 S1 :
      (serv I0 (PSend n v P0) O0 =(Tau)=> S1) <->
        exists P1, (PSend n v P0 =(Send n v)=> P1) /\ S1 = serv I0 P0 (O0 ++ [(n, v)]).
    Proof.
      split; intros.
      - kill H; kill H0; subst. eattac.
      - eattac; kill H.
    Qed.

    Lemma STrans_Tau_Tau_inv  I0 P0 O0 S1 :
      (serv I0 (STau P0) O0 =(Tau)=> S1) <->
        exists P1, (STau P0 =(Tau)=> P1) /\ S1 = serv I0 P1 O0.
    Proof.
      split; intros.
      - kill H; eattac.
      - eattac.
    Qed.

    Lemma STrans_Recv_t_inv a I0 P0 O0 I1 P1 O1 :
      (length I1 > length I0)%nat ->
      (serv I0 P0 O0 =(a)=> serv I1 P1 O1) <->
        exists n v, I1 = I0 ++ [(n, v)] /\ P1 = P0 /\ O1 = O0 /\ a = Recv n v.
    Proof.
      split; intros.
      - kill H0; try ltac1:(lia).
        + attac. subst. exists n, v. attac.
        + kill H1.
          apply Deq_length in HDeq.
          ltac1:(lia).
      - eattac.
    Qed.

    Lemma STrans_Pick_t_inv a I0 P0 O0 I1 P1 O1 :
      (length I1 < length I0)%nat ->
      (serv I0 P0 O0 =(a)=> serv I1 P1 O1) <->
        exists n v, Deq n v I0 I1 /\ (P0 =(Recv n v)=> P1) /\ O1 = O0 /\ a = Tau.
    Proof.
      split; intros.
      - kill H0; try ltac1:(lia); eattac.
      - eattac.
    Qed.

    Lemma STrans_Tau_t_inv a I0 P0 O0 I1 P1 O1 :
      length I0 = length I1 -> length O0 = length O1 ->
      (serv I0 P0 O0 =(a)=> serv I1 P1 O1) <->
        I1 = I0 /\ O1 = O0 /\ a = Tau /\ (P0 =(Tau)=> P1).
    Proof.
      split; intros; subst.
      - kill H1; attac; absurd (length I1 = length I0); attac.
      - eattac.
    Qed.

    Lemma STrans_Send_t_inv a I0 P0 O0 I1 P1 O1 :
      (length O1 > length O0)%nat ->
      (serv I0 P0 O0 =(a)=> serv I1 P1 O1) <->
        exists n v, O1 = O0 ++ [(n, v)] /\ (P0 =(Send n v)=> P1) /\ I1 = I0 /\ a = Tau.
    Proof.
      split; intros.
      - kill H0; try ltac1:(lia).
        + attac. subst. exists n, v. attac.
        + simpl in *.
          ltac1:(lia).
      - eattac.
    Qed.

    Lemma STrans_Push_t_inv a I0 P0 O0 I1 P1 O1 :
      (length O1 < length O0)%nat ->
      (serv I0 P0 O0 =(a)=> serv I1 P1 O1) <->
        exists n v, I0 = I1 /\ P0 = P1 /\ O0 = ((n,v)::O1) /\ a = (Send n v).
    Proof.
      split; intros.
      - kill H0; eattac.
      - eattac.
    Qed.
  End Inversions.
  #[export] Hint Rewrite
  -> @STrans_Recv_inv @STrans_Send_inv @STrans_Tau_Recv_inv @STrans_Tau_Send_inv @STrans_Tau_Tau_inv
      using (first [assumption | lia]) : LTS.

  #[export] Hint Rewrite
  -> @STrans_Recv_t_inv @STrans_Pick_t_inv @STrans_Tau_t_inv @STrans_Send_t_inv @STrans_Push_t_inv using (solve [eauto with LTS datatypes; lia]) : LTS.

End PROC_F.

Module Type PROC(Conf : PROC_CONF) := Conf <+ PROC_PARAMS <+ PROC_F.


Ltac2 destruct_ma a :=
  destruct $a as [[[? ?]|[? ?]|]|[[? ?]|[? ?]|]|[[? ?]|[? ?]|]].

Ltac2 Notation "destruct_ma" c(constr) := destruct_ma c.

Ltac2 evar t :=
  let u := open_constr:(_:$t) in
  match Constr.Unsafe.kind u with
  | Constr.Unsafe.Cast v _ _ => v
  | _ => Control.throw Init.Assertion_failure
  end.


Ltac2 rec special_destruct (h : ident) :=
  let hh := hyp h in
  match! (Constr.type hh) with
  | ex ?x =>
      match (Constr.Unsafe.kind x) with
      | Constr.Unsafe.Lambda arg _val =>
          let arg_n := match Constr.Binder.name arg with
                       | None => Fresh.in_goal @x
                       | Some n => Fresh.in_goal n
                       end in
          destruct $hh as [$arg_n $h];
          special_destruct h
      | _ => Control.throw Init.Assertion_failure
      end
  | _ /\ _ =>
      let h' := Fresh.in_goal h in
      destruct $hh as [$h $h'];
      Control.enter (fun () => special_destruct h);
      Control.enter (fun () => special_destruct h')
  | _ => ()
  end.


Ltac2 sd t :=
  match! goal with
  | [h : _ |- _] =>
      let h_hyp := hyp h in
      let h' := Fresh.in_goal h in
      assert $t as $h' by (eapply $h_hyp; eauto with LTS);
      clear $h;
      rename $h' into $h;
      special_destruct h
  end.



Ltac2 rec pose_matches (l : (ident * constr) list) :=
  match l with
  | [] => ()
  | (i, x)::rest =>
      match Constr.Unsafe.kind x with
      | Constr.Unsafe.Var x' =>
          if Ident.equal x' i then () else pose $x as $i
      | _ => pose $x as $i
      end;

      pose_matches rest
  end.

Ltac2 rec print_list (l : (ident * constr) list) :=
  match l with
  | [] => ()
  | (i, x)::rest =>
      printf "%I --> %t" i x;
      print_list rest
  end.


Ltac2 rec rebind (l : (ident * constr) list) :=
  match l with
  | [] => ()
  | (v, _t)::rest =>
      let v_h := hyp v in
      match! (eval cbv in $v_h) with
      | ?x =>
          if Constr.is_var x
          then ltac1:(x a |- replace x with a in * by auto) (Ltac1.of_constr x) (Ltac1.of_ident v)
          else ()
      end;
      rebind rest
  end.

Ltac2 obtain (h : ident) (p : pattern) :=
  let body := strip_exists h in
  let m := Pattern.matches p body in
  pose_matches m;
  unshelve (rebind m).

Ltac2 Notation "obtain" h(ident) p(pattern) := unshelve (obtain h p); try assumption.


Ltac2 rec tr(t : constr) :=
  match (Constr.Unsafe.kind t) with
  | Constr.Unsafe.Prod prem concl =>
      match (Constr.Binder.name prem) with
      | None => t
      | Some _n =>
          Constr.Unsafe.make (Constr.Unsafe.Prod prem (tr concl))
      end
  | _ => t
  end.


Ltac2 rec build_impl prems concl :=
  match prems with
  | [] => concl
  | prem::rest =>
      let concl := Constr.Unsafe.make (Constr.Unsafe.Prod prem concl) in
      build_impl rest concl
  end.

Ltac2 rec move_rels rels (idx : int) t :=
  match rels with
  | [] => t
  | _shift::rest =>
      move_rels rest (Int.add 1 idx) t
  end.

Ltac2 rec normalize_forall' (acc : binder list) (t : constr) :=
  match (Constr.Unsafe.kind t) with
  | Constr.Unsafe.Prod prem concl =>
      match (Constr.Binder.name prem) with
      | None =>
          normalize_forall' (prem::acc) concl
      | Some _n =>
          (*
          - lift acc by 1
          - get future
          - incr 0 by len acc
          - construct forall

           *)

          let acc := List.map (
                         fun prem =>
                           let n := Constr.Binder.name prem in
                           let t := Constr.Binder.type prem in
                           let t := Constr.Unsafe.liftn 1 1 t in
                           Constr.Binder.unsafe_make n (Constr.Binder.Relevant) t
                       ) acc
          in

          let concl := normalize_forall' acc concl in

          let concl := Constr.Unsafe.liftn (List.length acc) 1 concl in

          let kind := Constr.Unsafe.Prod prem concl in
          let t := Constr.Unsafe.make kind in
          t
      end
  | _ =>
      let t := build_impl acc t in
      t
  end.


Ltac2 rec ignores_rel1 t :=
  if Constr.Unsafe.closedn 2 t
  then
    let t := Constr.Unsafe.substnl ['(False)] 1 t in
    Constr.Unsafe.closedn 0 t
  else ignores_rel1 (Constr.Unsafe.liftn (-1) 3 t).


Ltac2 judge_prod t : (ident option * constr * constr) option :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod prem concl =>
      let prem_t := Constr.Binder.type prem in
      match Constr.Binder.name prem with
      | Some n =>
          if ignores_rel1 concl
          then
            Some (None, prem_t, concl)
          else
            Some (Some n, prem_t, concl)
      | None =>
          Some (None, prem_t, concl)
      end
  | _ =>
      None
  end.


Ltac2 rec normalize_forall_step (t : constr) :=
  match judge_prod t with
  | Some (None, iprem_t, iconcl) =>

      match judge_prod iconcl with
      | Some (Some fprem_i, fprem_t, fconcl) =>

          let iprem_t := Constr.Unsafe.liftn 1 1 iprem_t in
          let fconcl := Constr.Unsafe.liftn 1 1 fconcl in
          let fconcl := Constr.Unsafe.liftn (-1) 3 fconcl in
          let fprem_t := Constr.Unsafe.liftn (-1) 1 fprem_t in

          let iprem := Constr.Binder.unsafe_make None (Constr.Binder.Relevant) iprem_t in
          let ikind := Constr.Unsafe.Prod iprem fconcl in
          let fprem := Constr.Binder.unsafe_make (Some fprem_i) (Constr.Binder.Relevant) fprem_t in
          let fkind := Constr.Unsafe.Prod fprem (Constr.Unsafe.make ikind) in

          let t := Constr.Unsafe.make fkind in

          t
      | _ =>

          let iprem := Constr.Binder.unsafe_make None (Constr.Binder.Relevant) iprem_t in
          let iconcl := normalize_forall_step iconcl in
          let ikind := Constr.Unsafe.Prod iprem iconcl in
          let t := Constr.Unsafe.make ikind in
          t
      end
  | Some (Some iprem_i, iprem_t, iconcl) =>

      let iprem := Constr.Binder.unsafe_make (Some iprem_i) (Constr.Binder.Relevant) iprem_t in
      let iconcl := normalize_forall_step iconcl in
      let ikind := Constr.Unsafe.Prod iprem iconcl in
      let t := Constr.Unsafe.make ikind in
      t
  | _ =>
      t
  end.

Ltac2 rec normalize_forall t :=
  let t' := normalize_forall_step t in
  if Constr.equal t t'
  then t
  else normalize_forall (Constr.Unsafe.liftn -1 1 t').

Ltac2 normalize_hyp h :=
  let h_hyp := hyp h in
  let t := normalize_forall (Constr.type h_hyp) in
  let v := Fresh.in_goal @H in
  assert $t as $v by (intros; eapply $h_hyp; eauto);
  clear $h;
  rename $v into $h.

Ltac2 Notation "normalize" h(ident) := normalize_hyp h.


Ltac2 rec split_forall t :=
  match (Constr.Unsafe.kind t) with
  | Constr.Unsafe.Prod prem concl =>
      match (Constr.Binder.name prem) with
      | None =>
          split_forall concl
      | Some n =>
          let t := Constr.Binder.type prem in
          let e := evar t in
          let concl := Constr.Unsafe.substnl [e] 0 concl in
          let (args, targs, tail) := split_forall concl in
          (n::args, t::targs, tail)
      end
  | _ =>
      ([], [], t)
  end.


Import Ltac2.Constr.Unsafe.

Ltac2 evar_to_ident t :=
  let s := Message.to_string (Message.of_constr t) in
  String.set s 0 (Char.of_int 118);
  match Ident.of_string s with
  | Some i => i
  | None => Fresh.in_goal @e
  end.


Module Type MON_CONF.
  Parameter Inline Msg : Set.
  Parameter Inline MState : Set.
End MON_CONF.

Module Type MON_PROC_CONF := PROC_CONF <+ MON_CONF.

Module Type MON_PARAMS(Import Conf : MON_PROC_CONF).
  Declare Module Export Proc : PROC(Conf).

  Inductive EMsg :=
  | MqSend : NameTag -> Val -> EMsg
  | MqRecv : NameTag -> Val -> EMsg
  | MqProbe : NameTag -> Msg -> EMsg
  .
  #[export] Hint Constructors EMsg : LTS.

  Notation MQue := (list EMsg).


  Inductive MVal :=
  | MValM : Msg -> MVal
  | MValP : Val -> MVal
  .
  #[export] Hint Constructors MVal : LTS.


  Inductive MAct :=
  | MActP : PAct -> MAct
  | MActT : PAct -> MAct
  | MActM : @Act Msg -> MAct
  .
  #[export] Hint Constructors MAct : LTS.


  Inductive MProc :=
  | MRecv (state : MState)
  | MSend (to : NameTag) (msg : Msg) (M : MProc)
  .

  #[export] Hint Constructors MProc : LTS.
End MON_PARAMS.

Module Type MON_HANDLE(Import Conf : MON_PROC_CONF)(Import Params : MON_PARAMS(Conf)).
  Parameter mon_handle : EMsg -> MState -> MProc.
End MON_HANDLE.

Module Type MON_F(Import Conf : MON_PROC_CONF)(Import Params : MON_PARAMS(Conf)).
  Declare Module Import MonHandle : MON_HANDLE(Conf)(Params).
  Export MonHandle.

  Notation "# v" := (MValP v) (at level 1).
  Notation "^ v" := (MValM v) (at level 1).

  #[export,refine]
    Instance gen_Act_MAct : gen_Act MAct :=
    {
      Payload := MVal;

      send n v :=
        match v with
        | MValP v' => MActT (send n v')
        | MValM v' => MActM (Send n v')
        end;

      recv n v :=
        match v with
        | MValP v' => MActT (recv n v')
        | MValM v' => MActM (Recv n v')
        end;

      ia a :=
        match a with
        | MActM Tau | MActT Tau | MActP _ => True
        | _ => False
        end;

      send_recv := ltac:(intros; destruct v; auto; discriminate);
      ia_disjoint := ltac:(intros; split; destruct v; auto; discriminate);
      gact_rec := _;
    }.
  Proof.
    intros.
    destruct_ma a; attac.
    - specialize (X (n, t) (MValP v)); attac.
    - specialize (X0 (n, t) (MValP v)); attac.
    - specialize (X (n, t) (MValM v)); attac.
    - specialize (X0 (n, t) (MValM v)); attac.
  Defined.

  #[export] Hint Unfold gen_Act_MAct : LTS.
  #[export] Hint Transparent gen_Act_MAct : LTS.


  Definition PayloadM (v : MVal) : @Payload MAct gen_Act_MAct := v.
  #[export] Hint Transparent PayloadM : LTS typeclass_instances.
  #[export] Hint Unfold PayloadM : LTS typeclass_instances.
  #[global] Coercion PayloadM : MVal >-> Payload.



  Fixpoint next_state (M : MProc) :=
    match M with
    | MRecv s => s
    | MSend _ _ next => next_state next
    end.

  Coercion next_state : MProc >-> MState.

  Inductive MonAct : Set :=
  | MonRecv : EMsg -> MonAct
  | MonSend : NameTag -> Msg -> MonAct
  .
  #[export] Hint Constructors MonAct : LTS.


  Inductive MonTrans : MonAct -> MProc -> MProc -> Prop :=
  | MonTSend : forall {n msg M},
      MonTrans
        (MonSend n msg)
        (MSend n msg M)
        M
  | MonTRecv : forall {ev s},
      MonTrans
        (MonRecv ev)
        (MRecv s)
        (mon_handle ev s)
  .
  #[export] Hint Constructors MonTrans : LTS.


  #[export]
    Instance trans_mon : LTS MonAct MProc  :=
    {
      trans := MonTrans
    }.

  #[export] Hint Unfold trans_mon : LTS.
  #[export] Hint Transparent trans_mon : LTS.


  Section Inversions.
    Fact MonTrans_Recv_inv (M0 M1 : MProc) e :
      (M0 =(MonRecv e)=> M1) <->
        exists s, M0 = MRecv s /\ M1 = mon_handle e s.

    Proof.
      split; intros.
      - kill H. exists s. attac.
      - attac.
    Qed.

    Fact MonTrans_Send_inv (M0 M1 : MProc) n e :
      (M0 =(MonSend n e)=> M1) <->
        M0 = MSend n e M1.

    Proof.
      destruct M0, M1; eattac.
    Qed.
  End Inversions.

  #[export] Hint Rewrite -> @MonTrans_Recv_inv @MonTrans_Send_inv using assumption : LTS LTS_concl.


  Lemma next_state_keep1 [n v M0 M1] :
    (M0 =(MonSend n v)=> M1) ->
    next_state M0 = next_state M1.

  Proof.
    intros; eattac.
  Qed.


  Lemma next_state_keep [path M0 M1] :
    (M0 =[path]=> M1) ->
    Forall (fun a => match a with MonRecv _ => False | _ => True end) path ->
    next_state M0 = next_state M1.

  Proof with attac.
    ltac1:(generalize dependent M0).
    induction path; intros M0 T HF.
    inversion T...

    apply path_split1 in T as [M0' [T0 T1]];
      inversion HF.
    destruct a; inversion H1...
  Qed.


  Lemma next_state_invariant [n] : trans_invariant (fun M => next_state M = n)
                                     (fun a => match a with MonRecv _ => False | _ => True end).

  Proof.
    unfold trans_invariant.
    intros. destruct a; eattac.
  Qed.


  #[export] Hint Resolve next_state_invariant : inv.
  #[export] Hint Extern 10 (next_state _ = _) => solve_invariant : LTS.
  #[export] Hint Extern 10 (?a = next_state _) =>
    match a with
    | next_state _ => fail 1
    | _ => apply eq_sym; solve_invariant
    end: LTS.


  Definition ready M := exists s, M = MRecv s.

  #[export] Hint Unfold ready : LTS.
  #[export] Hint Transparent ready : LTS.


  Lemma ready_inv M : ready M <-> (exists s, M = MRecv s).
  Proof. split; intros; destruct M; unfold ready in *; eattac. Qed.

  #[export] Hint Rewrite -> @ready_inv using assumption : LTS.
  #[export] Hint Resolve <- ready_inv : LTS.


  Inductive MServ := mserv { mserv_i : MQue; mserv_m :> MProc; mserv_s : Serv}.
  #[export] Hint Constructors MServ : LTS.


  Inductive MTrans : MAct -> MServ -> MServ -> Prop :=
  | MTSendM : forall {n msg MQ M0 M1 S},
      (M0 =(MonSend n msg)=> M1) ->
      MTrans (MActM (Send n msg))
        (mserv MQ M0 S)
        (mserv MQ M1 S)

  | MTRecvM : forall {n v MQ M S},
      MTrans (MActM (Recv n v))
        (mserv MQ M S)
        (mserv (MQ ++ [MqProbe n v]) M S)

  | MTPickM : forall {n v MQ M0 M1 S},
      (M0 =(MonRecv (MqProbe n v))=> M1) ->
      MTrans (MActM Tau)
        (mserv (MqProbe n v :: MQ) M0 S)
        (mserv MQ M1 S)

  | MTRecvT : forall {n v} {MQ M S},
      MTrans (MActT (Recv n v))
        (mserv MQ M S)
        (mserv (MQ ++ [MqRecv n v]) M S)

  | MTSendT : forall {n v MQ M0 M1 S},
      (M0 =(MonRecv (MqSend n v))=> M1) ->
      MTrans (MActT (Send n v))
        (mserv (MqSend n v :: MQ) M0 S)
        (mserv MQ M1 S)

  | MTRecvP : forall {n v MQ M0 M1 S0 S1}
                (TP : S0 =(Recv n v)=> S1),
      (M0 =(MonRecv (MqRecv n v))=> M1) ->
      MTrans (MActP (Recv n v))
        (mserv (MqRecv n v :: MQ) M0 S0)
        (mserv MQ M1 S1)

  | MTSendP : forall {n v MQ M S0 S1}
                (TP : S0 =(Send n v)=> S1),
      MTrans (MActP (Send n v))
        (mserv MQ M S0)
        (mserv (MQ ++ [MqSend n v]) M S1)

  | MTTauP : forall {MQ M S0 S1}
               (TP : S0 =(Tau)=> S1),
      MTrans (MActP Tau)
        (mserv MQ M S0)
        (mserv MQ M S1)
  .
  #[export] Hint Constructors MTrans : LTS.


  #[export]
    Instance trans_mserv : LTS MAct MServ  :=
    {
      trans := MTrans
    }.

  #[export] Hint Unfold trans_mserv : LTS.
  #[export] Hint Transparent trans_mserv : LTS.


  Section Inversions.
    Fact MTrans_SendM_inv n msg MS0 MS1 :
      (MS0 =(MActM (Send n msg))=> MS1) <-> exists MQ M0 P M1,
          MS0 = mserv MQ M0 P /\ MS1 = mserv MQ M1 P /\ (M0 =(MonSend n msg)=> M1).
    Proof.
      split; intros.
      - destruct MS0, MS1; kill H. eexists _,_,_,_. eattac.
      - eattac.
    Qed.

    Fact MTrans_RecvM_inv n v MS0 MS1 :
      (MS0 =(MActM (Recv n v))=> MS1) <-> exists MQ M P,
          MS0 = mserv MQ M P /\ MS1 = mserv (MQ ++ [MqProbe n v]) M P.
    Proof.
      split; intros.
      - destruct MS0, MS1; kill H. eexists _,_,_. eattac.
      - attac.
    Qed.

    Fact MTrans_PickM_inv MS0 MS1 :
      (MS0 =(MActM Tau)=> MS1) <-> exists n msg MQ P M0 M1,
          MS0 = mserv (MqProbe n msg :: MQ) M0 P /\ MS1 = mserv MQ M1 P /\ (M0 =(MonRecv (MqProbe n msg))=> M1).
    Proof.
      split; intros.
      - kill H; kill H0. eexists _,_. eattac.
      - hsimpl in *. constructor. eattac.
    Qed.

    Fact MTrans_RecvT_inv n v MS0 MS1 :
      (MS0 =(MActT (Recv n v))=> MS1) <-> exists MQ M P,
          MS0 = mserv MQ M P /\ MS1 = mserv (MQ ++ [MqRecv n v]) M P.
    Proof.
      split; intros.
      - destruct MS0, MS1; kill H. eexists _,_,_. eattac.
      - attac.
    Qed.

    Fact MTrans_SendT_inv n v MS0 MS1 :
      (MS0 =(MActT (Send n v))=> MS1) <-> exists MQ P M0 M1,
          MS0 = mserv (MqSend n v :: MQ) M0 P /\ MS1 = mserv MQ M1 P /\ (M0 =(MonRecv (MqSend n v))=> M1).
    Proof.
      split; intros.
      - kill H; kill H0. eattac.
      - hsimpl in *. constructor. eattac.
    Qed.

    Fact MTrans_RecvP_inv n v MS0 MS1 :
      (MS0 =(MActP (Recv n v))=> MS1) <-> exists MQ P0 M0 M1 P1,
          MS0 = mserv (MqRecv n v :: MQ) M0 P0 /\ MS1 = mserv MQ M1 P1 /\ (M0 =(MonRecv (MqRecv n v))=> M1)
          /\ (P0 =(Recv n v)=> P1).
    Proof.
      split; intros.
      - kill H; kill H0. eexists _,_; eattac.
      - hsimpl in *. constructor; eattac.
    Qed.

    Fact MTrans_SendP_inv n v MS0 MS1 :
      (MS0 =(MActP (Send n v))=> MS1) <-> exists MQ M P0 P1,
          MS0 = mserv MQ M P0 /\ MS1 = mserv (MQ ++ [MqSend n v]) M P1 /\ (P0 =(Send n v)=> P1).
    Proof.
      split; intros.
      - destruct MS0, MS1; kill H. eexists _,_,_. eattac.
      - attac.
    Qed.

    Fact MTrans_TauP_inv MS0 MS1 :
      (MS0 =(MActP Tau)=> MS1) <-> exists MQ M P0 P1,
          MS0 = mserv MQ M P0 /\ MS1 = mserv MQ M P1 /\ (P0 =(Tau)=> P1).
    Proof. eattac; kill H; eattac. Qed.
  End Inversions.

  #[export] Hint Rewrite -> @MTrans_RecvM_inv @MTrans_SendM_inv @MTrans_PickM_inv @MTrans_SendT_inv @MTrans_RecvT_inv @MTrans_SendP_inv @MTrans_RecvP_inv @MTrans_TauP_inv using assumption : LTS.


  Definition is_MqProbe ev := match ev with MqProbe _ _ => True | _ => False end.
  #[export] Hint Unfold is_MqProbe : LTS.
  #[export] Hint Transparent is_MqProbe : LTS.

  Definition is_MqSend ev := match ev with MqSend _ _ => True | _ => False end.
  #[export] Hint Unfold is_MqSend : LTS.
  #[export] Hint Transparent is_MqSend : LTS.

  Definition is_MqRecv ev := match ev with MqRecv _ _ => True | _ => False end.
  #[export] Hint Unfold is_MqRecv : LTS.
  #[export] Hint Transparent is_MqRecv : LTS.


  Notation NoSends_MQ := (Forall (fun e => match e with MqSend _ _ => False | _ => True end)).


  Lemma ready_q_erecv [MQ M S n e] :
    ready M ->
    (mserv (MqProbe n e :: MQ) M S =(MActM Tau)=>
       mserv MQ (mon_handle (MqProbe n e) M) S).

  Proof. eattac. Qed.


  Lemma ready_q_tsend [MQ M S n v] :
    ready M ->
    (mserv (MqSend n v :: MQ) M S =(MActT (Send n v))=>
       mserv MQ (mon_handle (MqSend n v) M) S).

  Proof. eattac. Qed.


  Lemma ready_q_trecv [MQ M S0 S1 n v] :
    ready M ->
    (S0 =(Recv n v)=> S1) ->
    (mserv (MqRecv n v :: MQ) M S0 =(MActP (Recv n v))=>
       mserv MQ (mon_handle (MqRecv n v) M) S1).

  Proof. eattac 10. Qed.


  Lemma is_MqProbe_inv ev : is_MqProbe ev <-> exists n msg, ev = MqProbe n msg.
  Proof. destruct ev; eattac. Qed.

  #[export] Hint Rewrite -> @is_MqProbe_inv using assumption : LTS.


  Definition MQ_Clear := Forall is_MqProbe.

  Lemma MQ_Clear_Forall MQ : Forall is_MqProbe MQ <-> MQ_Clear MQ.
  Proof. unfold MQ_Clear; split; auto. Qed.

  #[export] Hint Immediate MQ_Clear_Forall : LTS.


  Lemma MQ_Clear_cons_inv ev Q : MQ_Clear (ev :: Q) <-> exists n msg, ev = MqProbe n msg /\ MQ_Clear Q.
  Proof. unfold MQ_Clear. eattac; kill H; eattac. Qed.

  Lemma MQ_Clear_app_inv Q0 Q1 : MQ_Clear (Q0 ++ Q1) <-> MQ_Clear Q0 /\ MQ_Clear Q1.
  Proof. unfold MQ_Clear. eattac; apply Forall_app in H; eattac. Qed.

  #[export] Hint Rewrite -> @MQ_Clear_cons_inv @MQ_Clear_app_inv using assumption : LTS LTS_concl.


  Lemma MQ_Clear_nil : MQ_Clear [].
  Proof. constructor. Qed.

  #[export] Hint Resolve MQ_Clear_nil : LTS.


  Lemma MQ_Clear_cons [a Q] : is_MqProbe a -> MQ_Clear Q -> MQ_Clear (a::Q).
  Proof. intros; constructor; eauto with LTS. Qed.

  #[export] Hint Resolve MQ_Clear_cons : LTS.


  Lemma MQ_Clear_send_in_bs [Q n v] :
    List.In (MqSend n v) Q -> ~ MQ_Clear Q.

  Proof.
    intros.
    intros Hx.
    eapply Forall_forall with (P := is_MqProbe) in H; eauto.
  Qed.

  #[export] Hint Resolve MQ_Clear_send_in_bs : bs.


  Lemma MQ_Clear_recv_in_bs [Q n v] :
    List.In (MqSend n v) Q -> ~ MQ_Clear Q.

  Proof.
    intros.
    intros Hx.
    eapply Forall_forall with (P := is_MqProbe) in H; eauto.
  Qed.

  #[export] Hint Resolve MQ_Clear_recv_in_bs : bs.


  Lemma MQ_Clear_NoSends : forall MQ, MQ_Clear MQ -> NoSends_MQ MQ.
  Proof. induction MQ; attac. Qed.

  #[export] Hint Resolve MQ_Clear_NoSends : LTS.


  Inductive mon_assg := _mon_assg {assg_mq : MQue; assg_clear : MQ_Clear assg_mq; assg_m : MState}.
  Arguments _mon_assg MQ M S : rename.


  (** Instrumentation function *)
  Definition serv_instr (a : mon_assg) : Serv -> MServ :=
    fun (s : Serv) => mserv (assg_mq a) (MRecv (assg_m a)) s.
  Coercion serv_instr : mon_assg >-> Funclass.

  #[export] Hint Unfold serv_instr : LTS.
  #[export] Hint Transparent serv_instr : LTS.


  Lemma assg_with_ready : forall (assg : mon_assg) S,
      ready (assg S).

  Proof.
    attac.
  Qed.

  #[export] Hint Resolve assg_with_ready : LTS.


  (** Instrumentation is an injection *)
  Lemma assg_inj : forall (a : mon_assg) [S0 S1], a S0 = a S1 -> S0 = S1.

  Proof. attac. Qed.
  #[export] Hint Rewrite @assg_inj using assumption : LTS.


  Fixpoint retract_recv (MQ : MQue) : Que Val :=
    match MQ with
    | [] => []
    | MqRecv n v :: MQ' => (n, v) :: retract_recv MQ'
    | _ :: MQ' => retract_recv MQ'
    end.


  Fixpoint retract_send (MQ : MQue) : Que Val :=
    match MQ with
    | [] => []
    | MqSend n v :: MQ' => (n, v) :: retract_send MQ'
    | _ :: MQ' => retract_send MQ'
    end.

  Lemma retract_recv_In [MQ n v] : List.In (MqRecv n v) MQ -> List.In (n, v) (retract_recv MQ).
  Proof. intros; induction MQ; intros; hsimpl in *; attac.
         destruct H; subst; simpl in *; attac. destruct a; attac.
  Qed.

  Lemma retract_send_In [MQ n v] : List.In (MqSend n v) MQ -> List.In (n, v) (retract_send MQ).
  Proof. intros; induction MQ; intros; hsimpl in *; attac.
         destruct H; subst; simpl in *; attac. destruct a; attac.
  Qed.

  Lemma In_retract_recv MQ n v : List.In (n, v) (retract_recv MQ) -> List.In (MqRecv n v) MQ.
  Proof. intros; induction MQ; intros; hsimpl in *; attac.
         destruct a; attac. destruct H; hsimpl in *; eattac.
  Qed.

  Lemma In_retract_send [MQ n v] : List.In (n, v) (retract_send MQ) -> List.In (MqSend n v) MQ.
  Proof. intros; induction MQ; intros; hsimpl in *; attac.
         destruct a; attac. destruct H; hsimpl in *; eattac.
  Qed.

  #[export] Hint Immediate retract_recv_In retract_send_In In_retract_recv In_retract_send : LTS.
  #[export] Hint Resolve retract_recv_In retract_send_In : LTS. (* strategy: the rewriter will reduce the other way, so solver has to infer it back*)


  Lemma retract_recv_In_inv MQ n v : List.In (MqRecv n v) MQ <-> List.In (n, v) (retract_recv MQ).
  Proof. split; intros; eauto with LTS. Qed.

  Lemma retract_send_In_inv MQ n v : List.In (MqSend n v) MQ <-> List.In (n, v) (retract_send MQ).
  Proof. split; intros; eauto with LTS. Qed.

  #[export] Hint Rewrite <- retract_recv_In_inv retract_send_In_inv using assumption : LTS LTS_concl.


  Lemma retract_recv_app MQ0 MQ1 : retract_recv (MQ0 ++ MQ1) = retract_recv MQ0 ++ retract_recv MQ1.
  Proof. induction MQ0; simpl in *; eattac. destruct a; eattac. Qed.

  Lemma retract_send_app MQ0 MQ1 : retract_send (MQ0 ++ MQ1) = retract_send MQ0 ++ retract_send MQ1.
  Proof. induction MQ0; simpl in *; eattac. destruct a; eattac. Qed.

  #[export] Hint Rewrite -> @retract_recv_app retract_send_app using assumption : LTS LTS_concl.
  #[export] Hint Resolve retract_recv_app retract_send_app : LTS.


  Lemma retract_recv_mrecv_nil MQ : MQ_Clear MQ -> retract_recv MQ = [].
  Proof. induction MQ; eattac. Qed.

  Lemma retract_send_mrecv_nil MQ : MQ_Clear MQ -> retract_send MQ = [].
  Proof. induction MQ; eattac. Qed.

  Lemma MQ_nil_mrecv MQ : retract_recv MQ = [] -> retract_send MQ = [] -> MQ_Clear MQ.
  Proof. induction MQ; eattac. destruct a; eattac. Qed.

  #[export] Hint Rewrite -> @retract_recv_mrecv_nil @retract_send_mrecv_nil using assumption : LTS LTS_concl.
  #[export] Hint Resolve retract_recv_mrecv_nil retract_send_mrecv_nil MQ_nil_mrecv : LTS.


  Lemma retract_recv_app_mrecv MQ0 MQ1 : MQ_Clear MQ1 -> retract_recv (MQ0 ++ MQ1) = retract_recv MQ0.
  Proof. eattac. Qed.

  Lemma retract_send_app_mrecv MQ0 MQ1 : MQ_Clear MQ1 -> retract_send (MQ0 ++ MQ1) = retract_send MQ0.
  Proof. eattac. Qed.

  Lemma retract_recv_mrecv_app MQ0 MQ1 : MQ_Clear MQ0 -> retract_recv (MQ0 ++ MQ1) = retract_recv MQ1.
  Proof. eattac. Qed.

  Lemma retract_send_mrecv_app MQ0 MQ1 : MQ_Clear MQ0 -> retract_send (MQ0 ++ MQ1) = retract_send MQ1.
  Proof. eattac. Qed.

  #[export] Hint Rewrite -> @retract_recv_app_mrecv @retract_send_app_mrecv @retract_recv_mrecv_app retract_send_mrecv_app using assumption : LTS_R LTS_concl_r.
  #[export] Hint Resolve retract_recv_app_mrecv retract_send_app_mrecv retract_recv_mrecv_app retract_send_mrecv_app : LTS.


  (** Deinstrumentation. Strips off monitoring and disassembles monitor's queue. *)
  Coercion serv_deinstr (MS0 : MServ) : Serv :=
    match MS0 with
    | (mserv MQ0 _ (serv I0 P0 O0)) => (serv (I0 ++ (retract_recv MQ0)) P0 (retract_send MQ0 ++ O0))
    end.

  (** Deinstrumentation is inversion of instrumentation *)
  Theorem service_serv_deinstr_instr : forall (a : mon_assg) S, serv_deinstr (a S) = S.

  Proof.
    intros.
    destruct S.
    destruct a.
    induction serv_i0; simpl; attac.
  Qed.

  #[export] Hint Rewrite @service_serv_deinstr_instr using assumption : LTS.
  #[export] Hint Resolve service_serv_deinstr_instr : LTS.


  Lemma serv_deinstr_In_recv [MQ M S I P O n v] :
    List.In (MqRecv n v) MQ ->
    serv_deinstr (mserv MQ M S) = (serv I P O) ->
    List.In (n, v) I.

  Proof.
    revert I P O n v.

    induction MQ; intros; attac.
    destruct S.
    hsimpl.
    destruct H; attac.
    destruct a; attac.
  Qed.


  Lemma serv_deinstr_In_send [MQ M S I P O n v] :
    List.In (MqSend n v) MQ ->
    serv_deinstr (mserv MQ M S) = (serv I P O) ->
    List.In (n, v) O.

  Proof.
    revert I P O n v.
    induction MQ; intros; attac.
    destruct S.
    hsimpl.
    destruct H; subst.
    - attac.
    - destruct a; hsimpl; attac.
  Qed.


  Definition MAct_to_PAct (ma : MAct) : option PAct :=
    match ma with
    | MActT (Send n v) => Some (Send n v)
    | MActT (Recv n v) => Some (Recv n v)
    | MActP Tau => Some Tau
    | _ => None
    end.


  Fixpoint MPath_to_PPath (mpath : list MAct) : list PAct :=
    match mpath with
    | [] => []
    | ma :: mpath' =>
        match MAct_to_PAct ma with
        | None => MPath_to_PPath mpath'
        | Some a => a :: MPath_to_PPath mpath'
        end
    end.

  Notation "ma >:- a" := (MAct_to_PAct ma = Some a) (at level 70) : type_scope.
  Notation "mpath >:~ ppath" := (MPath_to_PPath mpath = ppath) (at level 70) : type_scope.


  Lemma MPath_to_PPath_cons : forall ma mpath,
      MPath_to_PPath (ma :: mpath) = MPath_to_PPath [ma] ++ MPath_to_PPath mpath.

  Proof. intros; destruct_ma ma; attac. Qed.


  Lemma MPath_to_PPath_app : forall mpath0 mpath1,
      MPath_to_PPath (mpath0 ++ mpath1) = MPath_to_PPath mpath0 ++ MPath_to_PPath mpath1.

  Proof.
    induction mpath0; intros. 1: attac.
    rewrite MPath_to_PPath_cons.
    rewrite <- app_comm_cons in *.
    rewrite <- app_assoc in *.
    rewrite <- IHmpath0.
    apply MPath_to_PPath_cons.
  Qed.

  #[export] Hint Rewrite MPath_to_PPath_app using assumption : LTS LTS_concl. (* TODO aren't the following invs a bit redundant? *)


  Lemma path_corr_cons : forall ma mpath a ppath,
      ma >:- a ->
      mpath >:~ ppath ->
      ma::mpath >:~ a::ppath.

  Proof. attac. Qed.


  Lemma path_corr_app : forall mpath0 mpath1 ppath0 ppath1,
      mpath0 >:~ ppath0 ->
      mpath1 >:~ ppath1 ->
      mpath0 ++ mpath1 >:~ ppath0 ++ ppath1.

  Proof.
    induction mpath0. 1: attac.
    intros.
    rewrite <- app_comm_cons.
    attac.
    destruct_ma a; attac.
    all: f_equal; eapply IHmpath0; eattac.
  Qed.


  Lemma path_corr_app_nil_l : forall mpath0 mpath1 ppath,
      mpath0 >:~ [] ->
      mpath1 >:~ ppath ->
      mpath0 ++ mpath1 >:~ ppath.

  Proof.
    intros.
    eapply path_corr_app with (ppath0:=[]); attac.
  Qed.


  Lemma path_corr_app_nil_r : forall mpath0 mpath1 ppath,
      mpath0 >:~ ppath ->
      mpath1 >:~ [] ->
      mpath0 ++ mpath1 >:~ ppath.

  Proof.
    intros.
    replace ppath with (ppath ++ []) by attac.
    eapply path_corr_app with (ppath1:=[]); attac.
  Qed.


  Lemma path_corr_cons_nil_l : forall ma mpath ppath,
      MAct_to_PAct ma = None ->
      mpath >:~ ppath ->
      ma :: mpath >:~ ppath.

  Proof. attac. Qed.



  #[export] Hint Resolve path_corr_cons path_corr_app path_corr_app_nil_l path_corr_app_nil_r path_corr_cons_nil_l : LTS.

  (* auto somehow fails to solve obvious bs eg Send <> Tau *)
  #[export] Hint Extern 4 (_ <> _) => solve [congruence | discriminate] : LTS.


  Lemma path_corr_uncons_nil_l : forall ma mpath,
      ma :: mpath >:~ [] ->
      MAct_to_PAct ma = None.

  Proof. intros. destruct_ma ma; attac. Qed.


  Lemma path_corr_uncons_nil_r : forall ma mpath,
      ma :: mpath >:~ [] ->
      mpath >:~ [].

  Proof. intros. destruct_ma ma; attac. Qed.


  Lemma path_corr_split_nil_l : forall mpath0 mpath1,
      mpath0 ++ mpath1 >:~ [] ->
      mpath0 >:~ [].

  Proof.
    intros.
    induction mpath0. 1: attac.
    rewrite <- app_comm_cons in *.
    assert (MAct_to_PAct a = None) by eauto using path_corr_uncons_nil_l.
    attac.
  Qed.


  Lemma path_corr_split_nil_r : forall mpath0 mpath1,
      mpath0 ++ mpath1 >:~ [] ->
      mpath1 >:~ [].

  Proof.
    intros.
    induction mpath0. 1: attac.
    rewrite <- app_comm_cons in *.
    assert (MAct_to_PAct a = None) by eauto using path_corr_uncons_nil_l.
    attac.
  Qed.


  #[export] Hint Resolve path_corr_uncons_nil_r path_corr_uncons_nil_l path_corr_split_nil_r path_corr_split_nil_l : LTS.


  (** Correspondence guarantees a split *)
  Theorem path_corr_split : forall [mpath0 mpath1 ppath],
      (mpath0 ++ mpath1) >:~ ppath ->
      exists ppath0 ppath1,
        ppath = ppath0 ++ ppath1
        /\ mpath0 >:~ ppath0
        /\ mpath1 >:~ ppath1.

  Proof with attac.
    induction mpath0; attac.
    1: { exists [], (MPath_to_PPath mpath1)... }

    specialize (IHmpath0 mpath1 (MPath_to_PPath (mpath0 ++ mpath1)) ltac:(attac))
      as (ppath0 & ppath1 & ? & ?).

    destruct (MAct_to_PAct a) eqn:?.
    - exists (p :: ppath0), ppath1...
    - exists ppath0, ppath1...
  Qed.


  Lemma path_corr_split_inv : forall mpath0 mpath1 ppath,
      (mpath0 ++ mpath1) >:~ ppath <->
      exists ppath0 ppath1,
        ppath = ppath0 ++ ppath1
        /\ mpath0 >:~ ppath0
        /\ mpath1 >:~ ppath1.

  Proof. attac. Qed.

  #[export] Hint Rewrite -> path_corr_split_inv using assumption : LTS.


  (** Action is "flushing" when it works strictly towards making the monitor queue smaller. *)
  Definition Flushing_act (a : MAct) : Prop :=
    match a with
    | MActM (Send _ _) => True (* MProcitor may need to send to reach ready state*)
    | MActM (Recv _ _) => False
    | MActM Tau        => True (* MProcitor may need to tau to reach ready state*)
    | MActT (Recv _ _) => False
    | MActT (Send _ _) => True
    | MActT Tau        => False (* Impossible *)
    | MActP (Recv _ _) => True
    | MActP (Send _ _) => False
    | MActP Tau        => False
    end.

  #[export] Hint Transparent Flushing_act : LTS.


  (** Flushing action reduces the monitor queue *)
  Lemma Flushing_act_split : forall [a] [MQ0 M0 I0 P0 O0] [MQ1 M1 I1 P1 O1],
      (mserv MQ0 M0 (serv I0 P0 O0) =(a)=> mserv MQ1 M1 (serv I1 P1 O1)) ->
      Flushing_act a ->
      exists MQ', MQ0 = MQ' ++ MQ1.

  Proof.
    intros.
    inversion H; subst; inversion H0; subst; simpl in *; ltac1:(try contradiction).
    - exists []. auto.
    - exists [MqProbe n v]. auto.
    - exists [MqSend n v]. auto.
    - exists [MqRecv n v]. auto.
  Qed.


  (** Flushing path can be reapplied with a bigger monitor queue, and the residue will remain. *)
  Lemma Flushing_cont : forall [mpath] [MQ0 M0 S0] [MQ1 M1 S1] MQ',
      (mserv MQ0 M0 S0 =[mpath]=> mserv MQ1 M1 S1) ->
      Forall Flushing_act mpath ->
      (mserv (MQ0 ++ MQ') M0 S0 =[mpath]=> mserv (MQ1 ++ MQ') M1 S1).

  Proof with eattac 10.
    induction mpath; intros.
    inversion H. constructor.

    hsimpl in *.
    rename H into T0.
    rename H2 into T1.

    switch a.
    destruct a; try (simpl in *; contradiction).
    - case (MActP ?x).
      destruct x; try (contradiction).
      kill T0.
      eapply IHmpath in T1; auto.
      unshelve eapply (path_seq1 _ T1)...
    - case (MActT ?x).
      kill T0; try (contradiction)...
    - case (MActM ?x).
      kill T0; try (contradiction)...
  Qed.


  (** Flushing act can be reapplied with a shorter monitor queue*)
  Lemma Flushing_retract1 : forall [a] [MQ0 M0 S0] [MQ1 M1 S1] MQ',
      (mserv (MQ0 ++ MQ') M0 S0 =(a)=> mserv (MQ1 ++ MQ') M1 S1) ->
      Flushing_act a ->
      (mserv MQ0 M0 S0 =(a)=> mserv MQ1 M1 S1).

  Proof.
    intros.
    consider (_ =(_)=> _); eattac 10.
  Qed.


  (** Flushing path can be reapplied with a shorter monitor queue *)
  Lemma Flushing_retract : forall [mpath] [MQ0 M0 S0] [MQ1 M1 S1] MQ',
      (mserv (MQ0 ++ MQ') M0 S0 =[mpath]=> mserv (MQ1 ++ MQ') M1 S1) ->
      Forall Flushing_act mpath ->
      (mserv MQ0 M0 S0 =[mpath]=> mserv MQ1 M1 S1).

  Proof.
    intros.
    generalize dependent MQ0 M0 S0 MQ'.
    induction mpath; attac.
    - enough (MQ0 = MQ1) by attac.
      eapply app_inv_l.
      eauto.
    - rename MQ1 into MQ2.
      rename M1 into M2.
      rename S1 into S2.
      destruct N1 as [MQ1' M1 S1].

      enough (exists MQ1, MQ1' = MQ1 ++ MQ').
      {
        hsimpl in *.
        enough (mserv MQ0 M0 S0 =( a )=> mserv MQ1 M1 S1); eauto using Flushing_retract1 with LTS.
      }

      clear - H1 H2.
      generalize dependent MQ1' M1 S1.
      induction mpath; eattac.
      destruct N1 as [MQ11' M11 S11].
      assert (exists MQ11, MQ11' = MQ11 ++ MQ'); eattac.

      consider (_ =(a)=> _); eattac.
  Qed.


  Definition flush1 (MQ : MQue) (M : MProc) : option MAct :=
    match M with
    | MRecv _ =>
        match MQ with
        | [] => None
        | MqRecv nc v :: _ => Some (MActP (Recv nc v))
        | MqSend nc v :: _ => Some (MActT (Send nc v))
        | MqProbe nc e :: _ => Some (MActM (Recv nc e))
        end
    | MSend nc e _ => Some (MActM (Send nc e))
    end.

  Fixpoint mcode_measure (M : MProc) : (nat * MState) :=
    match M with
    | MRecv s => (O, s)
    | MSend nc e Mc =>
        let (n, s) := mcode_measure Mc
        in (S n, s)
    end.
  Fixpoint flush_measure (MQ : MQue) (M : MProc) : nat :=
    match MQ with
    | [] =>
        let (n, _) := mcode_measure M in
        n
    | e :: MQ' =>
        let (n, s) := mcode_measure M in
        S n + flush_measure MQ' M
    end.

  Definition EMsg_to_MAct (e : EMsg) : MAct :=
    match e with
    | MqRecv nc v => MActP (Recv nc v)
    | MqSend nc v => MActT (Send nc v)
    | MqProbe nc e => MActM Tau
    end.

  Fixpoint flush_mcode (M : MProc) : list MAct :=
    match M with
    | MRecv s => []
    | MSend nc e Mc => MActM (Send nc e) :: flush_mcode Mc
    end.

  Fixpoint mk_flush_path (MQ : MQue) (M : MProc) : list MAct :=
    match MQ with
    | [] => flush_mcode M
    | e :: MQ' =>
        let mpath0 := flush_mcode M in
        let mpath1 := mk_flush_path MQ' (mon_handle e M) in
        mpath0 ++ EMsg_to_MAct e :: mpath1
    end.

  Fixpoint flush_Mstate (MQ : MQue) (M : MProc) : MState :=
    match MQ with
    | [] => M
    | e :: MQ' =>
        flush_Mstate MQ' (mon_handle e M)
    end.

  Definition flush_M MQ M := MRecv (flush_Mstate MQ M).
  Definition flush_S MQ S := match S with serv I0 P0 O0 => serv (I0 ++ retract_recv MQ) P0 O0 end.
  Definition flush_path MS := match MS with mserv MQ M _ => mk_flush_path MQ M end.
  Definition flush_MS MS0 := match MS0 with mserv MQ0 M0 S0 => mserv [] (flush_M MQ0 M0) (flush_S MQ0 S0) end.

  #[export] Hint Unfold flush_M : LTS.
  #[export] Hint Transparent flush_M flush_S flush_path flush_MS : LTS.


  Lemma flush_S_Clear MQ S0 : MQ_Clear MQ -> flush_S MQ S0 = S0.
  Proof. destruct S0; attac. Qed.

  #[export] Hint Rewrite -> flush_S_Clear using spank : LTS LTS_concl.


  Lemma flush_skip_M MQ nc e s:
    flush_M MQ (MSend nc e s) = flush_M MQ s.

  Proof.
    generalize dependent nc e s.
    induction MQ; attac.
  Qed.

  Lemma flush_cont_M MQ0 MQ1 M :
    flush_M (MQ0 ++ MQ1) M = flush_M MQ1 (flush_M MQ0 M).

  Proof.
    unfold flush_M.
    generalize dependent M MQ1.
    induction MQ0; attac.
    induction MQ1; attac.
  Qed.

  #[export] Hint Rewrite -> flush_skip_M flush_cont_M using assumption : LTS LTS_concl.


  Lemma mk_flush_cont_path MQ0 MQ1 M :
    mk_flush_path (MQ0 ++ MQ1) M =
    mk_flush_path MQ0 M ++ mk_flush_path MQ1 (flush_M MQ0 M).

  Proof.
    unfold flush_M.
    generalize dependent M MQ1.
    induction MQ0; attac.
    induction MQ1; attac.
    repeat (rewrite <- app_assoc in * ).
    repeat (rewrite <- app_comm_cons in * ).
    attac.
  Qed.


  Lemma flush_M_go : forall MQ (M : MProc) S,
      mserv MQ M S =[flush_mcode M]=> mserv MQ (MRecv M) S.
  Proof.
    intros.
    generalize dependent S.
    induction M; eattac.
  Qed.


  Lemma flush_go : forall MQ0 M0 S0,
    mserv MQ0 M0 S0 =[ mk_flush_path MQ0 M0 ]=> mserv [] (flush_M MQ0 M0) (flush_S MQ0 S0).

  Proof.
    intros.
    destruct S0 as [I0 P0 O0].
    generalize dependent M0 I0 P0 O0.
    induction MQ0; attac.
    - induction M0; eattac.
    - eapply path_seq.
      1: eauto using flush_M_go.

      destruct a; eapply path_seq1; eattac 15.
      now replace (I0 ++ (n, v) :: retract_recv MQ0) with ((I0 ++ [(n, v)]) ++ retract_recv MQ0) by eattac.
  Qed.

  Lemma flush_go_MS : forall {MS0}, MS0 =[flush_path MS0]=> flush_MS MS0.
  Proof.
    unfold flush_MS.
    destruct MS0 as [MQ0 M0 S0].
    eauto using flush_go.
  Qed.

  #[export] Hint Resolve flush_go_MS flush_go : LTS.


  Lemma EMsg_to_MAct_Flushing : forall e, Flushing_act (EMsg_to_MAct e).
  Proof. destruct e; attac. Qed.

  Lemma flush_M_Flushing : forall M, Forall Flushing_act (flush_mcode M).
  Proof. induction M; attac. Qed.

  #[export] Hint Resolve EMsg_to_MAct_Flushing flush_M_Flushing : LTS.


  Lemma flush_path_Flushing : forall MQ M, Forall Flushing_act (mk_flush_path MQ M).
  Proof. induction MQ; hsimpl in *; attac. Qed.

  #[export] Hint Resolve flush_path_Flushing : LTS.


  Lemma flush_M_admin : forall M, flush_mcode M >:~ [].
  Proof. induction M; attac. Qed.

  #[export] Hint Resolve flush_M_admin : LTS.


  Lemma flush_path_admin : forall MQ (M : MProc), MQ_Clear MQ -> mk_flush_path MQ M >:~ [].
  Proof.
    induction MQ; attac.

    enough ( MPath_to_PPath (flush_mcode M) ++
               MPath_to_PPath
               (mk_flush_path MQ (mon_handle (MqProbe n msg) M)) = [] ++ []
           ) by attac.

    rewrite <- MPath_to_PPath_app.
    eapply path_corr_app; eattac.
  Qed.

  #[export] Hint Resolve flush_path_admin : LTS.


  Hint Unfold flush_MS : LTS.
  Lemma flush_go_Clear : forall MQ M S, MQ_Clear MQ -> mserv MQ M S =[mk_flush_path MQ M]=> mserv [] (flush_M MQ M) S.
  Proof.
    intros.
    ltac1:(replace &S with (flush_S MQ &S) at 2 by attac).
    attac.
  Qed.

  #[export] Hint Resolve flush_go_Clear : LTS.


  Lemma flush_M_ready : forall MQ M, ready (flush_M MQ M).

  Proof. unfold flush_M. attac. Qed.

  #[export] Hint Resolve flush_M_ready : LTS.


  Definition flush_Mr MQ M := exist _ (flush_M MQ M) (flush_M_ready MQ M).

  Definition flush_assg' (MQ : MQue) (M : MProc) : mon_assg :=
    {| assg_mq := []; assg_m := flush_Mstate MQ M; assg_clear := ltac:(attac)|}.

  Definition flush_assg (a : mon_assg) : mon_assg :=
    flush_assg' (assg_mq a) (MRecv (assg_m a)).

  Lemma flush_go_instr : forall (a : mon_assg) S0,
      a S0 =[flush_path (a S0)]=> flush_assg a S0.

  Proof.
    unfold flush_assg.
    intros.
    destruct S0 as [I0 P0 O0].
    destruct a.
    attac.
  Qed.


  Lemma move_ex_r [A] P Q : (P /\ exists x : A, Q x) <-> exists x : A, P /\ Q x.
    split; intros.
    - destruct H as [H [x Hx]]. exists x. auto.
    - destruct H as [x [H Hx]]. split; auto; exists x; auto.
  Qed.

  Lemma move_ex_l [A] P Q : (exists x : A, P x) /\ Q <-> exists x : A, P x /\ Q.
    split; intros.
    - destruct H as [[x Hx] H]. exists x. auto.
    - destruct H as [x [Hx H]]. split; auto; exists x; auto.
  Qed.

  Fact forall_imp : forall [A] P (Q : A -> Prop), (P -> forall x, Q x) -> (forall x, P -> Q x).
    intros. auto.
  Qed.

  (** Any state of a monitored process can be dragged to a "canonical" one, where the monitor is ready
  and has empty queue. **)
  Theorem flush_go_until : forall MQ0 MQ1 M0 S0,
      (mserv (MQ0 ++ MQ1) M0 S0 =[ mk_flush_path MQ0 M0 ]=> mserv MQ1 (flush_M MQ0 M0) (flush_S MQ0 S0)).

  Proof with ltac2:(eauto with LTS).
    destruct S0.
    intros.
    eapply Flushing_cont with (MQ0:=MQ0)(MQ1:=[])...
  Qed.


  (** Any state of a monitored process can be dragged to a "canonical" one, where the monitor is ready
  and has empty queue. **)
  Theorem flush_go_until_Clear : forall MQ0 MQ1 M0 S0,
      MQ_Clear MQ0 ->
      (mserv (MQ0 ++ MQ1) M0 S0 =[ mk_flush_path MQ0 M0 ]=> mserv MQ1 (flush_M MQ0 M0) S0).

  Proof with ltac2:(eauto with LTS).
    intros.
    eapply Flushing_cont with (MQ0:=MQ0)(MQ1:=[])...
  Qed.


  Lemma Forall_app_solve : forall [A : Set] (P : A -> Prop)
                             (l1 l2 : list A), Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
  Proof. intros. apply Forall_app. auto. Qed.

  #[export] Hint Resolve Forall_cons : LTS.
  #[export] Hint Resolve Forall_app_solve : LTS.


  Lemma corr_extraction1 : forall
      [ma]
      [MQ0 M0 I0 P0 O0] [MQ1 M1 I1 P1 O1],
      (mserv MQ0 M0 (serv I0 P0 O0) =(ma)=> mserv MQ1 M1 (serv I1 P1 O1)) ->
      (serv (I0 ++ retract_recv MQ0) P0 (retract_send MQ0 ++ O0) =[MPath_to_PPath [ma]]=> serv (I1 ++ retract_recv MQ1) P1 (retract_send MQ1 ++ O1)).

  Proof.
    intros.
    destruct_ma ma; hsimpl in *; attac.
    - rewrite <- app_assoc in *; attac.
    - rewrite <- app_assoc in *; attac.
    - consider (_ =(_)=> _); attac.
  Qed.


  Lemma corr_extraction : forall
      [mpath]
      [MQ0 M0 I0 P0 O0] [MQ1 M1 I1 P1 O1],
      (mserv MQ0 M0 (serv I0 P0 O0) =[mpath]=> mserv MQ1 M1 (serv I1 P1 O1)) ->
      (serv (I0 ++ retract_recv MQ0) P0 (retract_send MQ0 ++ O0) =[MPath_to_PPath mpath]=> serv (I1 ++ retract_recv MQ1) P1 (retract_send MQ1 ++ O1)).

  Proof with (eauto with LTS).
    induction mpath; intros.
    1: { attac. }

    hsimpl in * |-.

    destruct N1 as [MQ0' M0' [I0' P0' O0']].
    rewrite MPath_to_PPath_cons.

    eapply path_seq with (middle := serv (I0' ++ retract_recv MQ0') P0' (retract_send MQ0' ++ O0'));
      eauto using corr_extraction1.
  Qed.


  Instance Serv_Transp_M : LTS MAct Serv | 10 :=
    {
      trans := fun (ma : MAct) (S0 S1 : Serv) =>
                 match MAct_to_PAct ma with
                 | None => S1 = S0
                 | Some a => @trans PAct Serv trans_Serv a S0 S1
                 end
    }.


  Lemma Serv_Transp_act [ma : MAct] [a : PAct] [S0 S1 : Serv] :
    ma >:- a ->
    (S0 =(ma)=> S1) <-> (S0 =(a)=> S1).

  Proof.
    unfold trans, Serv_Transp_M.
    intros.
    attac.
  Qed.


  Lemma Serv_Transp_skip [ma : MAct] [S0 S1 : Serv] :
    MAct_to_PAct ma = None ->
    (S0 =(ma)=> S1) <-> S1 = S0.

  Proof.
    unfold trans, Serv_Transp_M.
    intros.
    attac.
  Qed.

  #[export] Hint Rewrite -> Serv_Transp_act Serv_Transp_skip using spank : LTS LTS_concl.
  #[export] Hint Immediate Serv_Transp_act Serv_Transp_skip : LTS.
  #[export] Hint Resolve <- Serv_Transp_act Serv_Transp_skip : LTS.


  Lemma Serv_Transp_M_path : forall (mpath : list MAct) (S0 S1 : Serv),
      (S0 =[mpath]=> S1) <-> (S0 =[MPath_to_PPath mpath]=> S1).

  Proof.
    induction mpath; split; attac; unfold trans, Serv_Transp_M in *.
    - destruct (MAct_to_PAct a) eqn:?.
      + enough (N1 =[MPath_to_PPath mpath]=> S1) by attac.
        apply IHmpath; eattac.
      + eapply IHmpath; eattac.
    - destruct (MAct_to_PAct a) eqn:?; attac.
      + enough ((S0 =(a)=> N1) /\ (N1 =[mpath]=> S1)) by attac.
        split.
        * unfold trans, Serv_Transp_M; attac.
        * eapply IHmpath; eattac.
      + assert (S0 =(a)=> S0) by eattac.
        enough (S0 =[mpath]=> S1) by attac.
        eapply IHmpath; eattac.
  Qed.

  #[export] Hint Rewrite -> Serv_Transp_M_path using spank : LTS LTS_concl.
  #[export] Hint Immediate Serv_Transp_M_path : LTS.
  #[export] Hint Resolve <- Serv_Transp_M_path : LTS.


  (** If a monitored process progresses over a path, then the unmonitored process can follow a
  corresponding path, if the traces in the monitor's queue are converted to unconsumed sends and
  receives of the process. *)
  Theorem corr_extraction_instr : forall [mpath MS0 MS1],
      (MS0 =[mpath]=> MS1) ->
      (serv_deinstr MS0 =[mpath]=> serv_deinstr MS1).

  Proof with (attac).
    intros.

    destruct MS0 as [MQ0 M0 [I0 P0 O0]].
    destruct MS1 as [MQ1 M1 [I1 P1 O1]].

    eauto using corr_extraction with LTS.
  Qed.


  Notation "MS0 =[*]=> MS1" := (MS0 =[flush_path MS0]=> MS1) (at level 80) : type_scope.

  Theorem Transp_soundness_base : forall [mpath0 : list MAct] [MS0 MS1 : MServ],
      (MS0 =[ mpath0 ]=> MS1) ->
      (serv_deinstr MS0 =[ mpath0 ++ flush_path MS1 ]=> serv_deinstr (flush_MS MS1)).

  Proof.
    intros.

    assert (serv_deinstr MS0 =[ mpath0 ]=> serv_deinstr MS1) by eauto using corr_extraction_instr.
    enough  (serv_deinstr MS1 =[ flush_path MS1 ]=> serv_deinstr (flush_MS MS1)) by attac.
    enough (MS1 =[ flush_path MS1 ]=> flush_MS MS1) by eauto using corr_extraction_instr.
    eauto using flush_go_MS.
  Qed.


  Lemma Transp_completeness_tau : forall [S0 S1] (a : mon_assg),
      (S0 =( Tau )=> S1) ->
      (a S0 =(MActP Tau)=> a S1).

  Proof.
    intros *.
    intros T. kill T; eattac 10.
  Qed.


  Lemma Transp_completeness_send_prep : forall [n v] [S0 S1] MQ0 M0,
      (S0 =( Send n v )=> S1) ->
      (mserv MQ0 M0 S0 =[MActP (Send n v) :: mk_flush_path MQ0 M0]=> (mserv [MqSend n v] (flush_M MQ0 M0) (flush_S MQ0 S1))).

  Proof.
    intros.

    eenough (mserv (MQ0 ++ [MqSend n v]) M0 S1 =[mk_flush_path MQ0 M0]=> _) by eattac.
    eapply flush_go_until.
  Qed.


  Lemma Transp_completeness_send : forall [n v] [S0 S1] MQ0 M0,
      (S0 =( Send n v )=> S1) ->
      (mserv MQ0 M0 S0 =[MActP (Send n v) :: mk_flush_path MQ0 M0 ++ [MActT (Send n v)]]=>
         (mserv [] (mon_handle (MqSend n v) (flush_Mstate MQ0 M0)) (flush_S MQ0 S1))).

  Proof.
    intros.

    eenough (mserv [MqSend n v] (flush_M MQ0 M0) (flush_S MQ0 S1) =(MActT (Send n v))=> _)
      by (rewrite app_comm_cons; eauto using Transp_completeness_send_prep with LTS).

    eattac.
  Qed.


  Lemma Flushing_clear1 [a] [MQ0 M0 S0 MS1] :
    (mserv MQ0 M0 S0 =(a)=> MS1) ->
    MQ_Clear MQ0 ->
    Flushing_act a ->
    [a] >:~ [].

  Proof.
    intros.
    destruct_ma a; attac.
  Qed.


  Lemma Flushing_clear [mpath] [MQ0 M0 S0 MS1] :
    (mserv MQ0 M0 S0 =[mpath]=> MS1) ->
    MQ_Clear MQ0 ->
    Forall Flushing_act mpath ->
    mpath >:~ [].

  Proof.
    generalize dependent MQ0 M0 S0.
    induction mpath; attac.
    destruct N1.

    assert ([a] >:~ []) by eauto using Flushing_clear1.
    destruct_ma a; simpl; doubt.
    all: eapply IHmpath; eattac.
    eattac.
  Qed.


  Lemma Transp_completeness_send_instr : forall [n v] [S0 S1] (a : mon_assg),
      (S0 =( Send n v )=> S1) ->
        (a S0 =[MActP (Send n v) :: flush_path (a S0) ++ [MActT (Send n v)]]=>
           (mserv [] (mon_handle (MqSend n v) (assg_m (flush_assg a))) S1)).

  Proof with eattac.
    intros.

    destruct a as [MQ0 ? M0].

    simpl.

    ltac1:(replace S1 with (flush_S MQ0 S1) by eauto using flush_S_Clear with LTS).
    eauto using Transp_completeness_send.
  Qed.


  Lemma Transp_completeness_recv_prep : forall n v MQ0 M0 S0,
    (mserv MQ0 M0 S0 =[MActT (Recv n v) :: mk_flush_path MQ0 M0]=> mserv [MqRecv n v] (flush_M MQ0 M0) (flush_S MQ0 S0)).

  Proof.
    intros.

    eenough ( mserv (MQ0 ++ [MqRecv n v]) M0 S0 =[mk_flush_path MQ0 M0]=> _) by eattac.
    eapply flush_go_until.
  Qed.


  Lemma Transp_completeness_recv : forall [n v] [S0 S1] MQ0 M0,
      MQ_Clear MQ0 ->
      (S0 =( Recv n v )=> S1) ->
      (mserv MQ0 M0 S0 =[MActT (Recv n v) :: mk_flush_path MQ0 M0 ++ [MActP (Recv n v)]]=> mserv [] (mon_handle (MqRecv n v) (flush_Mstate MQ0 M0)) S1).

  Proof.
    intros.

    eenough (mserv [MqRecv n v] (flush_M MQ0 M0) (flush_S MQ0 S0) =(MActP (Recv n v))=> _)
      by (rewrite app_comm_cons; eauto using Transp_completeness_recv_prep with LTS).

    eattac 10.
  Qed.


  Theorem Transp_completeness1 : forall [a S0 S1] (assg : mon_assg),
      (S0 =( a )=> S1) ->
      exists mpath0 ma mpath1 M1,
        (assg S0 =[ mpath0 ++ ma :: mpath1]=> mserv [] M1 S1)
        /\ mpath0 >:~ []
        /\ ma >:- a
        /\ mpath1 >:~ [].

  Proof.
    intros.
    destruct a.
    - exists (MActP (Send n v) :: flush_path (assg S0)), (MActT (Send n v)), [].
      eexists.
      split.
      1: eapply Transp_completeness_send_instr; eauto. (* TODO why? *)
      destruct assg; attac.
    - exists [], (MActT (Recv n v)), (mk_flush_path (assg_mq assg) (MRecv (assg_m assg)) ++ [MActP (Recv n v)]).
      eexists.
      destruct assg.
      split.
      1: eapply Transp_completeness_recv; eauto. (* TODO why? *)
      unshelve attac.
      attac.
    - exists [], (MActP Tau).
      exists (flush_path (assg S1)).
      eexists.

      split.
      + simpl.
        enough (assg S0 =(MActP Tau)=> assg S1) by (destruct assg; hsimpl; eattac).
        eauto using Transp_completeness_tau.
      + destruct assg; attac.
  Qed.


  Theorem Transp_completeness1_instr : forall [a S0 S1] (assg : mon_assg),
      (S0 =( a )=> S1) ->
      exists mpath0 ma mpath1 M1,
        (assg S0 =[ mpath0 ++ ma :: mpath1]=> mserv [] (MRecv M1) S1)
        /\ mpath0 >:~ []
        /\ ma >:- a
        /\ mpath1 >:~ [].

  Proof.
    intros.

    consider ( exists mpath0 ma mpath1 M1,
                 (### assg S0 =[ mpath0 ++ ma :: mpath1]=> mserv [] M1 S1)
                 /\ mpath0 >:~ []
                 /\ ma >:- a
                 /\ mpath1 >:~ []
           ) by eauto using Transp_completeness1.

    assert (mserv [] M1 S1 =[*]=> mserv [] (flush_M [] M1) S1) by eauto using flush_go with LTS.

    exists mpath0, ma, (mpath1 ++ mk_flush_path [] M1).
    replace (mpath0 ++ ma :: mpath1 ++ mk_flush_path [] M1)
      with  ((mpath0 ++ ma :: mpath1) ++ mk_flush_path [] M1)
      by attac.
    exists (flush_Mstate [] M1); eattac.
  Qed.


  (** The Completeness. For any path of an unmonitored process, there exists a corresponding path if
  monitoring is applied. The final state is also a result of generic monitor application. *)
  Theorem Transp_completeness : forall [path S0 S1] (assg : mon_assg),
      (S0 =[ path ]=> S1) ->
      exists mpath M1,
        (assg S0 =[ mpath ]=> mserv [] M1 S1)
        /\ mpath >:~ path.

  Proof with eattac.
    induction path; intros.
    - destruct assg as [MQ0 ? M0].
      exists (mk_flush_path MQ0 (MRecv M0)), (flush_M MQ0 (MRecv M0)).
      eattac.

    - hsimpl in *.
      rename S1 into S2.
      rename N1 into S1.

      consider (exists mpath0 ma mpath1 M1,
                 (### assg S0 =[ mpath0 ++ ma :: mpath1]=> mserv [] (MRecv M1) S1)
                 /\ mpath0 >:~ []
                 /\ ma >:- a
                 /\ mpath1 >:~ []) by eauto using Transp_completeness1_instr.

      pose (assg1 := {|assg_mq := []; assg_m := M1; assg_clear := ltac:(attac)|}).
      consider (
          exists mpath2 M2,
            (### assg1 S1 =[ mpath2 ]=> mserv [] M2 S2)
            /\ mpath2 >:~ path
        ).

      exists ((mpath0 ++ ma :: mpath1) ++ mpath2).
      exists M2.
      eattac.

      rewrite `(mpath0 >:~ []).
      rewrite `(mpath1 >:~ []).
      attac.
  Qed.


  Lemma flushing_nil_MQ : forall MQ M, mk_flush_path MQ M = [] -> MQ = [].
  Proof. destruct MQ; attac. Qed.

  Lemma flushing_nil_M : forall MQ M, mk_flush_path MQ M = [] -> ready M.
  Proof. destruct MQ, M; attac. Qed.

  #[export] Hint Rewrite -> flushing_nil_MQ using spank : LTS LTS_concl.

  #[export] Hint Resolve flushing_nil_M : LTS.


  Fixpoint flushing_M_artifact (self : Name) (M : MProc) (n : Name) : MQue :=
    match M with
    | MRecv _ => []
    | MSend (n', t) e M' =>
        let MQ := flushing_M_artifact self M' n in
        if NAME.eqb n n' then MqProbe (self, t) e :: MQ else MQ
    end.

  Fixpoint flushing_artifact (self : Name) (MQ : MQue) (M : MProc) (n : Name) : MQue :=
    match MQ with
    | [] => flushing_M_artifact self M n
    | e :: MQ' =>
        let MQ0 := flushing_M_artifact self M n in
        let MQ1 := flushing_artifact self MQ' (mon_handle e M) n in
        MQ0 ++ match e with
          | MqSend (n', t) v => if NAME.eqb n n' then MqRecv (self, t) v :: MQ1 else MQ1
          | _ => MQ1
          end
    end.


  Fixpoint path_artifact (self : Name) (mpath : list MAct) (n : Name) : MQue :=
    match mpath with
    | [] => []
    | MActM (Send (n', t) e) :: mpath' =>
        if NAME.eqb n n' then MqProbe (self, t) e :: path_artifact self mpath' n else path_artifact self mpath' n
    | MActT (Send (n', t) v) :: mpath' =>
        if NAME.eqb n n' then MqRecv (self, t) v :: path_artifact self mpath' n else path_artifact self mpath' n
    | _ :: mpath' => path_artifact self mpath' n
    end.


  Lemma flushing_M_artifact_Clear : forall self M n, MQ_Clear (flushing_M_artifact self M n).
  Proof.
    induction M; attac.
    smash_eq n n0; attac.
  Qed.

  #[export] Hint Resolve flushing_M_artifact_Clear : LTS.

  Lemma flushing_artifact_NoSend : forall self MQ M n, NoSends_MQ (flushing_artifact self MQ M n).
  Proof.
    induction MQ; attac.
    destruct a; attac.
    smash_eq n n1; attac.
  Qed.

  Lemma path_artifact_NoSend : forall self mpath n, NoSends_MQ (path_artifact self mpath n).
  Proof.
    induction mpath; attac.
    destruct_ma a; attac; smash_eq n n0; attac.
  Qed.

  Lemma flushing_artifact_Clear : forall self MQ M n, NoSends_MQ MQ -> MQ_Clear (flushing_artifact self MQ M n).
  Proof.
    induction MQ; attac.
    destruct a; attac.
  Qed.

  #[export] Hint Resolve flushing_artifact_NoSend flushing_artifact_Clear path_artifact_NoSend : LTS.


  Lemma flushing_artifact_app : forall self MQ0 MQ1 M n,
      flushing_artifact self (MQ0 ++ MQ1) M n = flushing_artifact self MQ0 M n ++ flushing_artifact self MQ1 (flush_M MQ0 M) n.

  Proof.
    intros.

    generalize dependent M.
    induction MQ0; attac.
    - blast_cases; destruct MQ1; attac.
    - blast_cases; rewrite IHMQ0; attac.
  Qed.

End MON_F.

Module Type MON(Conf : MON_PROC_CONF) := Conf <+ MON_PARAMS <+ MON_F.
