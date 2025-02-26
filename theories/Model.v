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
  | Send (n : NChan) (v : Payload) : Act
  | Recv (n : NChan) (v : Payload) : Act
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
  | PSend (n : NChan) (v : Val) (P : Proc) : Proc
  | PRecv (handle : NChan -> option (Val -> Proc)) : Proc
  | PTau (P : Proc) : Proc
  .

  Fact unfold_Proc : forall (P : Proc),
      P = match P with
          | PRecv handle => PRecv handle
          | PSend n v P' => PSend n v P'
          | PTau P' => PTau P'
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
    : ProcTrans Tau (PTau P) P
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
        P0 = PTau P1.
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

    Lemma ProcTrans_PTau_inv a P0 P1 :
      (PTau P0 =(a)=> P1) <->
        a = Tau /\ P0 = P1.
    Proof. attac; kill H; attac. Qed.
  End Inversions.
  #[export] Hint Rewrite -> @ProcTrans_Recv_inv @ProcTrans_Send_inv @ProcTrans_Tau_inv using assumption : LTS.
  #[export] Hint Rewrite -> @ProcTrans_PRecv_inv @ProcTrans_PSend_inv @ProcTrans_PTau_inv using assumption : LTS.


  Inductive PQued := pq : Que Val -> Proc -> Que Val -> PQued.
  #[export] Hint Constructors PQued : LTS.

  Definition pq_I S := match S with pq I' _ _ => I' end.
  Definition pq_P S := match S with pq _ P _ => P end.
  Definition pq_O S := match S with pq _ _ O' => O' end.

  #[export] Hint Transparent pq_I pq_P pq_O : LTS.

  Section Inversions.
    Fact pq_I_inv : forall S I P O, S = pq I P O -> pq_I S = I.
    Proof. intros. subst. auto. Qed.

    Fact pq_P_inv : forall S I P O, S = pq I P O -> pq_P S = P.
    Proof. intros. subst. auto. Qed.

    Fact pq_O_inv : forall S I P O, S = pq I P O -> pq_O S = O.
    Proof. intros. subst. auto. Qed.
  End Inversions.

  #[export] Hint Rewrite -> pq_I_inv pq_P_inv pq_O_inv using spank : LTS LTS_concl.


  Inductive PTrans : PAct -> PQued -> PQued -> Prop :=
  | PTRecv [n v I0 I1 P O]
      (HEnq : Enq n v I0 I1)
    : PTrans (Recv n v) (pq I0 P O) (pq I1 P O)

  | PTPick [n v I0 I1 P0 P1 O]
      (HDeq : Deq n v I0 I1)
    : (P0 =(Recv n v)=> P1) ->
      PTrans Tau (pq I0 P0 O) (pq I1 P1 O)

  | PTSend [n v I P0 P1 O0 O1]
      (HEnq : Enq n v O0 O1)
    : (P0 =(Send n v)=> P1) ->
      PTrans Tau (pq I P0 O0) (pq I P1 O1)

  | PTPush {n v I P O}
    : PTrans (Send n v) (pq I P ((n, v)::O)) (pq I P O)

  | PTTau {I P0 P1 O}
    : P0 =(Tau)=> P1 ->
                 PTrans Tau (pq I P0 O) (pq I P1 O)
  .


  #[export] Hint Constructors PTrans : LTS.


  #[export]
    Instance trans_pqued : LTS PAct PQued  :=
    {
      trans := PTrans
    }.

  #[export] Hint Unfold trans_pqued : LTS.
  #[export] Hint Transparent trans_pqued : LTS.


  Section Inversions.
    Lemma PTrans_Recv_inv n v S0 S1 :
      (S0 =(Recv n v)=> S1) <-> exists I0 P0 O0, pq I0 P0 O0 = S0 /\ pq (I0 ++ [(n, v)]) P0 O0 = S1.
    Proof. eattac; kill H; eattac. Qed.

    Lemma PTrans_Send_inv n v S0 S1 :
      (S0 =(Send n v)=> S1) <->
        exists I0 P0 O1, pq I0 P0 ((n, v)::O1) = S0 /\ pq I0 P0 O1 = S1.
    Proof. eattac; kill H; eattac. Qed.

    Lemma PTrans_Tau_Recv_inv I0 O0 S1 handle :
      (pq I0 (PRecv handle) O0 =(Tau)=> S1) <->
        exists n v I1 P1, (PRecv handle =(Recv n v)=> P1) /\ Deq n v I0 I1 /\ S1 = pq I1 P1 O0.
    Proof.
      split; intros.
      - kill H; kill H0; eattac.
      - eattac.
    Qed.

    Lemma PTrans_Tau_Send_inv n v I0 P0 O0 S1 :
      (pq I0 (PSend n v P0) O0 =(Tau)=> S1) <->
        exists P1, (PSend n v P0 =(Send n v)=> P1) /\ S1 = pq I0 P0 (O0 ++ [(n, v)]).
    Proof.
      split; intros.
      - kill H; kill H0; subst. eattac.
      - eattac; kill H.
    Qed.

    Lemma PTrans_Tau_Tau_inv  I0 P0 O0 S1 :
      (pq I0 (PTau P0) O0 =(Tau)=> S1) <->
        exists P1, (PTau P0 =(Tau)=> P1) /\ S1 = pq I0 P1 O0.
    Proof.
      split; intros.
      - kill H; eattac.
      - eattac.
    Qed.

    Lemma PTrans_Recv_t_inv a I0 P0 O0 I1 P1 O1 :
      (length I1 > length I0)%nat ->
      (pq I0 P0 O0 =(a)=> pq I1 P1 O1) <->
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

    Lemma PTrans_Pick_t_inv a I0 P0 O0 I1 P1 O1 :
      (length I1 < length I0)%nat ->
      (pq I0 P0 O0 =(a)=> pq I1 P1 O1) <->
        exists n v, Deq n v I0 I1 /\ (P0 =(Recv n v)=> P1) /\ O1 = O0 /\ a = Tau.
    Proof.
      split; intros.
      - kill H0; try ltac1:(lia); eattac.
      - eattac.
    Qed.

    Lemma PTrans_Tau_t_inv a I0 P0 O0 I1 P1 O1 :
      length I0 = length I1 -> length O0 = length O1 ->
      (pq I0 P0 O0 =(a)=> pq I1 P1 O1) <->
        I1 = I0 /\ O1 = O0 /\ a = Tau /\ (P0 =(Tau)=> P1).
    Proof.
      split; intros; subst.
      - kill H1; attac; absurd (length I1 = length I0); attac.
      - eattac.
    Qed.

    Lemma PTrans_Send_t_inv a I0 P0 O0 I1 P1 O1 :
      (length O1 > length O0)%nat ->
      (pq I0 P0 O0 =(a)=> pq I1 P1 O1) <->
        exists n v, O1 = O0 ++ [(n, v)] /\ (P0 =(Send n v)=> P1) /\ I1 = I0 /\ a = Tau.
    Proof.
      split; intros.
      - kill H0; try ltac1:(lia).
        + attac. subst. exists n, v. attac.
        + simpl in *.
          ltac1:(lia).
      - eattac.
    Qed.

    Lemma PTrans_Push_t_inv a I0 P0 O0 I1 P1 O1 :
      (length O1 < length O0)%nat ->
      (pq I0 P0 O0 =(a)=> pq I1 P1 O1) <->
        exists n v, I0 = I1 /\ P0 = P1 /\ O0 = ((n,v)::O1) /\ a = (Send n v).
    Proof.
      split; intros.
      - kill H0; eattac.
      - eattac.
    Qed.
  End Inversions.
  #[export] Hint Rewrite
  -> @PTrans_Recv_inv @PTrans_Send_inv @PTrans_Tau_Recv_inv @PTrans_Tau_Send_inv @PTrans_Tau_Tau_inv
      using (first [assumption | lia]) : LTS.

  #[export] Hint Rewrite
  -> @PTrans_Recv_t_inv @PTrans_Pick_t_inv @PTrans_Tau_t_inv @PTrans_Send_t_inv @PTrans_Push_t_inv using (solve [eauto with LTS datatypes; lia]) : LTS.

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

Module Type MON_PARAMS(Conf : MON_PROC_CONF).
  Declare Module Export Proc : PROC(Conf).
End MON_PARAMS.

Module Type MON_F(Import Conf : MON_PROC_CONF)(Import Params : MON_PARAMS(Conf)).
  Inductive Event :=
  | TrSend : NChan -> Val -> Event
  | TrRecv : NChan -> Val -> Event
  | EvRecv : NChan -> Msg -> Event
  .
  #[export] Hint Constructors Event : LTS.


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


  Inductive MCode :=
  | MRecv (state : MState)
  | MSend (to : NChan) (msg : Msg) (M : MCode)
  .

  #[export] Hint Constructors MCode : LTS.


  Fixpoint next_state (M : MCode) :=
    match M with
    | MRecv s => s
    | MSend _ _ next => next_state next
    end.


  Record Mon :=
    { handle : Event -> MState -> MCode
    ; state : MCode
    }.

  #[export] Hint Constructors Mon : LTS.


  Inductive MonAct : Set :=
  | MonRecv : Event -> MonAct
  | MonSend : NChan -> Msg -> MonAct
  | MonTau : MonAct
  .
  #[export] Hint Constructors MonAct : LTS.


  Inductive MonTrans : MonAct -> Mon -> Mon -> Prop :=
  | MonTSend : forall {handle n msg M},
      MonTrans
        (MonSend n msg)
        {|handle := handle; state := MSend n msg M|}
        {|handle := handle; state := M|}
  | MonTRecv : forall {ev s handle},
      MonTrans
        (MonRecv ev)
        {|handle := handle; state := MRecv s|}
        {|handle := handle; state := handle ev s|}
  .
  #[export] Hint Constructors MonTrans : LTS.


  #[export]
    Instance trans_mon : LTS MonAct Mon  :=
    {
      trans := MonTrans
    }.

  #[export] Hint Unfold trans_mon : LTS.
  #[export] Hint Transparent trans_mon : LTS.


  Section Inversions.
    Fact MonTrans_Recv_inv (M0 M1 : Mon) e :
      (M0 =(MonRecv e)=> M1) <->
        exists h s, M0 = {|handle:=h;state:=MRecv s|} /\ M1 = {|handle:=h; state:=h e s|}.

    Proof.
      split; intros.
      - kill H. exists handle0, s. attac.
      - destruct M0, M1. eattac.
    Qed.

    Fact MonTrans_Send_inv (M0 M1 : Mon) n e :
      (M0 =(MonSend n e)=> M1) <->
        M0 = {|handle:=handle M1; state:=MSend n e (state M1)|}.

    Proof.
      destruct M0, M1; eattac.
    Qed.

    Fact MonTrans_Tau_inv (M0 M1 : Mon) :
      (M0 =(MonTau)=> M1) <-> False.
    Proof. eattac. Qed.

  End Inversions.

  #[export] Hint Rewrite -> @MonTrans_Recv_inv @MonTrans_Send_inv @MonTrans_Tau_inv using assumption : LTS LTS_concl.


  Lemma next_state_keep1 [n v M0 M1] :
    (M0 =(MonSend n v)=> M1) ->
    next_state (state M0) = next_state (state M1).

  Proof.
    intros; eattac.
  Qed.


  Lemma next_state_keep [path M0 M1] :
    (M0 =[path]=> M1) ->
    Forall (fun a => match a with MonRecv _ => False | _ => True end) path ->
    next_state (state M0) = next_state (state M1).

  Proof with attac.
    ltac1:(generalize dependent M0).
    induction path; intros M0 T HF.
    inversion T...

    apply path_split1 in T as [M0' [T0 T1]];
      inversion HF.
    destruct a; inversion H1...
  Qed.


  Lemma next_state_invariant [n] : trans_invariant (fun M => next_state (state M) = n)
                                     (fun a => match a with MonRecv _ => False | _ => True end).

  Proof.
    unfold trans_invariant.
    intros. destruct a; eattac.
  Qed.


  #[export] Hint Resolve next_state_invariant : inv.
  #[export] Hint Extern 10 (next_state (state _) = _) => solve_invariant : LTS.
  #[export] Hint Extern 10 (?a = next_state (state _)) =>
    match a with
    | next_state _ => fail 1
    | _ => apply eq_sym; solve_invariant
    end: LTS.


  Definition ready M := exists s, state (M) = MRecv s.

  #[export] Hint Unfold ready : LTS.
  #[export] Hint Transparent ready : LTS.


  Lemma ready_inv M : ready M <-> (exists h s, M = {|handle:=h;state:=MRecv s|}).
  Proof. split; intros; destruct M; unfold ready in *; eattac. Qed.

  #[export] Hint Rewrite -> @ready_inv using assumption : LTS.
  #[export] Hint Resolve <- ready_inv : LTS.


  Lemma ready_recv [M e] :
    ready M ->
    M =(MonRecv e)=> {|handle:=handle M; state:=handle M e (next_state (state M))|}.

  Proof. eattac. Qed.

  #[export] Hint Resolve ready_recv | 10 : LTS.


  Lemma ready_trans [M0 e] :
    ready M0 ->
    exists M1, M0 =(MonRecv e)=> M1.

  Proof. eattac. Qed.


  Inductive MQued := mq : list Event -> Mon -> PQued -> MQued.
  #[export] Hint Constructors MQued : LTS.

  Definition mq_MQ MS := match MS with mq MQ _ _ => MQ end.
  Definition mq_M MS := match MS with mq _ M _ => M end.
  Definition mq_S MS := match MS with mq _ _ S' => S' end.
  Definition mq_I MS := pq_I (mq_S MS).
  Definition mq_P MS := pq_P (mq_S MS).
  Definition mq_O MS := pq_O (mq_S MS).

  #[export] Hint Transparent mq_MQ mq_M mq_S mq_I mq_P mq_O : LTS.


  Inductive MTrans : MAct -> MQued -> MQued -> Prop :=
  | MTSendM : forall {n msg MQ M0 M1 S},
      (M0 =(MonSend n msg)=> M1) ->
      MTrans (MActM (Send n msg))
        (mq MQ M0 S)
        (mq MQ M1 S)

  | MTRecvM : forall {n v MQ M S},
      MTrans (MActM (Recv n v))
        (mq MQ M S)
        (mq (MQ ++ [EvRecv n v]) M S)

  | MTPickM : forall {n v MQ M0 M1 S},
      (M0 =(MonRecv (EvRecv n v))=> M1) ->
      MTrans (MActM Tau)
        (mq (EvRecv n v :: MQ) M0 S)
        (mq MQ M1 S)

  | MTTauM : forall {MQ M0 M1 S},
      (M0 =(MonTau)=> M1) ->
      MTrans (MActM Tau)
        (mq MQ M0 S)
        (mq MQ M1 S)

  | MTRecvT : forall {n v} {MQ M S},
      MTrans (MActT (Recv n v))
        (mq MQ M S)
        (mq (MQ ++ [TrRecv n v]) M S)

  | MTSendT : forall {n v MQ M0 M1 S},
      (M0 =(MonRecv (TrSend n v))=> M1) ->
      MTrans (MActT (Send n v))
        (mq (TrSend n v :: MQ) M0 S)
        (mq MQ M1 S)

  | MTRecvP : forall {n v MQ M0 M1 S0 S1}
                (TP : S0 =(Recv n v)=> S1),
      (M0 =(MonRecv (TrRecv n v))=> M1) ->
      MTrans (MActP (Recv n v))
        (mq (TrRecv n v :: MQ) M0 S0)
        (mq MQ M1 S1)

  | MTSendP : forall {n v MQ M S0 S1}
                (TP : S0 =(Send n v)=> S1),
      MTrans (MActP (Send n v))
        (mq MQ M S0)
        (mq (MQ ++ [TrSend n v]) M S1)

  | MTTauP : forall {MQ M S0 S1}
               (TP : S0 =(Tau)=> S1),
      MTrans (MActP Tau)
        (mq MQ M S0)
        (mq MQ M S1)
  .
  #[export] Hint Constructors MTrans : LTS.


  #[export]
    Instance trans_mqued : LTS MAct MQued  :=
    {
      trans := MTrans
    }.

  #[export] Hint Unfold trans_mqued : LTS.
  #[export] Hint Transparent trans_mqued : LTS.


  Section Inversions.
    Fact MTrans_SendM_inv n msg MS0 MS1 :
      (MS0 =(MActM (Send n msg))=> MS1) <-> exists MQ M0 P M1,
          MS0 = mq MQ M0 P /\ MS1 = mq MQ M1 P /\ (M0 =(MonSend n msg)=> M1).
    Proof.
      split; intros.
      - destruct MS0, MS1; kill H. eexists _,_,_,_. eattac.
      - hsimpl in *. constructor. destruct M1. eattac.
    Qed.

    Fact MTrans_RecvM_inv n v MS0 MS1 :
      (MS0 =(MActM (Recv n v))=> MS1) <-> exists MQ M P,
          MS0 = mq MQ M P /\ MS1 = mq (MQ ++ [EvRecv n v]) M P.
    Proof.
      split; intros.
      - destruct MS0, MS1; kill H. eexists _,_,_. eattac.
      - attac.
    Qed.

    Fact MTrans_PickM_inv MS0 MS1 :
      (MS0 =(MActM Tau)=> MS1) <-> exists n msg MQ P M0 M1,
          MS0 = mq (EvRecv n msg :: MQ) M0 P /\ MS1 = mq MQ M1 P /\ (M0 =(MonRecv (EvRecv n msg))=> M1).
    Proof.
      split; intros.
      - kill H; kill H0. eexists _,_. eattac.
      - hsimpl in *. constructor. eattac.
    Qed.

    Fact MTrans_RecvT_inv n v MS0 MS1 :
      (MS0 =(MActT (Recv n v))=> MS1) <-> exists MQ M P,
          MS0 = mq MQ M P /\ MS1 = mq (MQ ++ [TrRecv n v]) M P.
    Proof.
      split; intros.
      - destruct MS0, MS1; kill H. eexists _,_,_. eattac.
      - attac.
    Qed.

    Fact MTrans_SendT_inv n v MS0 MS1 :
      (MS0 =(MActT (Send n v))=> MS1) <-> exists MQ P M0 M1,
          MS0 = mq (TrSend n v :: MQ) M0 P /\ MS1 = mq MQ M1 P /\ (M0 =(MonRecv (TrSend n v))=> M1).
    Proof.
      split; intros.
      - kill H; kill H0. eattac.
      - hsimpl in *. constructor. eattac.
    Qed.

    Fact MTrans_RecvP_inv n v MS0 MS1 :
      (MS0 =(MActP (Recv n v))=> MS1) <-> exists MQ P0 M0 M1 P1,
          MS0 = mq (TrRecv n v :: MQ) M0 P0 /\ MS1 = mq MQ M1 P1 /\ (M0 =(MonRecv (TrRecv n v))=> M1)
          /\ (P0 =(Recv n v)=> P1).
    Proof.
      split; intros.
      - kill H; kill H0. eexists _,_; eattac.
      - hsimpl in *. constructor; eattac.
    Qed.

    Fact MTrans_SendP_inv n v MS0 MS1 :
      (MS0 =(MActP (Send n v))=> MS1) <-> exists MQ M P0 P1,
          MS0 = mq MQ M P0 /\ MS1 = mq (MQ ++ [TrSend n v]) M P1 /\ (P0 =(Send n v)=> P1).
    Proof.
      split; intros.
      - destruct MS0, MS1; kill H. eexists _,_,_. eattac.
      - attac.
    Qed.

    Fact MTrans_TauP_inv MS0 MS1 :
      (MS0 =(MActP Tau)=> MS1) <-> exists MQ M P0 P1,
          MS0 = mq MQ M P0 /\ MS1 = mq MQ M P1 /\ (P0 =(Tau)=> P1).
    Proof. eattac; kill H; eattac. Qed.
  End Inversions.

  #[export] Hint Rewrite -> @MTrans_RecvM_inv @MTrans_SendM_inv @MTrans_PickM_inv @MTrans_SendT_inv @MTrans_RecvT_inv @MTrans_SendP_inv @MTrans_RecvP_inv @MTrans_TauP_inv using assumption : LTS.


  Notation NoSends_MQ := (Forall (fun e => match e with TrSend _ _ => False | _ => True end)).


  Lemma mq_preserve_handle1 [a MQ0 M0 S0 MQ1 M1 S1] :
    (mq MQ0 M0 S0 =(a)=> mq MQ1 M1 S1) ->
    handle M0 = handle M1.

  Proof.
    intros.
    kill H; attac.
  Qed.


  Lemma mq_preserve_handle [mpath MQ0 M0 S0 MQ1 M1 S1] :
    (mq MQ0 M0 S0 =[mpath]=> mq MQ1 M1 S1) ->
    handle M0 = handle M1.

  Proof.
    intros.
    generalize dependent MQ0 M0 S0.
    induction mpath; eattac.
    destruct N1 as [MQ0' M0' S0'].
    transitivity '(handle M0').
    - eauto using mq_preserve_handle1 with LTS.
    - eauto.
  Qed.


  Definition ready_q (M : MQued) :=
    match M with
    | mq _ M _ => ready M
    end.

  #[export] Hint Unfold ready_q : LTS.
  #[export] Hint Transparent ready_q : LTS.


  Lemma ready_q_erecv [MQ M S n e] :
    ready M ->
    (mq (EvRecv n e :: MQ) M S =(MActM Tau)=>
       mq MQ {|handle:=handle M; state:=handle M (EvRecv n e) (next_state (state M))|} S).

  Proof. eattac. Qed.


  Lemma ready_q_tsend [MQ M S n v] :
    ready M ->
    (mq (TrSend n v :: MQ) M S =(MActT (Send n v))=>
       mq MQ {|handle:=handle M; state:=handle M (TrSend n v) (next_state (state M))|} S).

  Proof. eattac. Qed.


  Lemma ready_q_trecv [MQ M S0 S1 n v] :
    ready M ->
    (S0 =(Recv n v)=> S1) ->
    (mq (TrRecv n v :: MQ) M S0 =(MActP (Recv n v))=>
       mq MQ {|handle:=handle M; state:=handle M (TrRecv n v) (next_state (state M))|} S1).

  Proof. eattac. Qed.


  Definition Mon_ready := {M : Mon | ready M}.


  Definition is_EvRecv ev := match ev with EvRecv _ _ => True | _ => False end.
  #[export] Hint Unfold is_EvRecv : LTS.
  #[export] Hint Transparent is_EvRecv : LTS.


  Lemma is_EvRecv_inv ev : is_EvRecv ev <-> exists n msg, ev = EvRecv n msg.
  Proof. destruct ev; eattac. Qed.

  #[export] Hint Rewrite -> @is_EvRecv_inv using assumption : LTS.


  Definition MQ_Clear := Forall is_EvRecv.

  Lemma MQ_Clear_Forall MQ : Forall is_EvRecv MQ <-> MQ_Clear MQ.
  Proof. unfold MQ_Clear; split; auto. Qed.

  #[export] Hint Immediate MQ_Clear_Forall : LTS.


  Lemma MQ_Clear_cons_inv ev Q : MQ_Clear (ev :: Q) <-> exists n msg, ev = EvRecv n msg /\ MQ_Clear Q.
  Proof. unfold MQ_Clear. eattac; kill H; eattac. Qed.

  Lemma MQ_Clear_app_inv Q0 Q1 : MQ_Clear (Q0 ++ Q1) <-> MQ_Clear Q0 /\ MQ_Clear Q1.
  Proof. unfold MQ_Clear. eattac; apply Forall_app in H; eattac. Qed.

  #[export] Hint Rewrite -> @MQ_Clear_cons_inv @MQ_Clear_app_inv using assumption : LTS LTS_concl.


  Lemma MQ_Clear_nil : MQ_Clear [].
  Proof. constructor. Qed.

  #[export] Hint Resolve MQ_Clear_nil : LTS.


  Lemma MQ_Clear_cons [a Q] : is_EvRecv a -> MQ_Clear Q -> MQ_Clear (a::Q).
  Proof. intros; constructor; eauto with LTS. Qed.

  #[export] Hint Resolve MQ_Clear_cons : LTS.


  Lemma MQ_Clear_send_in_bs [Q n v] :
    List.In (TrSend n v) Q -> ~ MQ_Clear Q.

  Proof.
    intros.
    intros Hx.
    eapply Forall_forall with (P := is_EvRecv) in H; eauto.
  Qed.

  #[export] Hint Resolve MQ_Clear_send_in_bs : bs.


  Lemma MQ_Clear_recv_in_bs [Q n v] :
    List.In (TrSend n v) Q -> ~ MQ_Clear Q.

  Proof.
    intros.
    intros Hx.
    eapply Forall_forall with (P := is_EvRecv) in H; eauto.
  Qed.

  #[export] Hint Resolve MQ_Clear_recv_in_bs : bs.


  Lemma MQ_Clear_NoSends : forall MQ, MQ_Clear MQ -> NoSends_MQ MQ.
  Proof. induction MQ; attac. Qed.

  #[export] Hint Resolve MQ_Clear_NoSends : LTS.


  Definition MQ_clear :=
    { MQ : list Event
    | MQ_Clear MQ
    }.

  Definition MQued_ready := {M : MQued | ready_q M}.


  Definition instr_t := MQ_clear -> Mon_ready -> PQued -> MQued.


  (** Instrumentation function *)
  Definition instr : instr_t :=
    fun (MQ : MQ_clear) (M : Mon_ready) (P : PQued) => mq (proj1_sig MQ) (proj1_sig M) P.

  #[export] Hint Unfold instr : LTS.
  #[export] Hint Transparent instr : LTS.


  Lemma instr_with_ready : forall MQ M S,
      ready_q (instr MQ M S).

  Proof.
    intros.
    ltac1:(autounfold with LTS).
    destruct M as (M & HR).
    eauto.
  Qed.

  #[export] Hint Resolve instr_with_ready : LTS.


  (** Instrumentation is an injection *)
  Lemma instr_inj : forall [MQ M] [P0 P1], instr MQ M P0 = instr MQ M P1 -> P0 = P1.

  Proof.
    intros.
    unfold instr in H.
    injection H; trivial.
  Qed.

  #[export] Hint Rewrite @instr_inj using assumption : LTS.


  (** Split monitor queue between receive and send traces *)
  Inductive MQ_Split :
    list Event -> (* Monitor queue *)
    Que Val -> (* Receives *)
    Que Val -> (* Sends *)
    Prop :=
  | MQS_nil : MQ_Split [] [] []

  | MQS_recv : forall [n v MQ I O],
      MQ_Split MQ I O ->
      MQ_Split (TrRecv n v :: MQ) ((n, v)::I) O

  | MQS_send : forall [n v MQ I O],
      MQ_Split MQ I O ->
      MQ_Split (TrSend n v :: MQ) I ((n, v)::O)

  | MQS_mrecv : forall [n v MQ I O],
      MQ_Split MQ I O ->
      MQ_Split (EvRecv n v :: MQ) I O
  .

  #[export] Hint Constructors MQ_Split : LTS.


  Lemma MQ_Split_nil_inv_l MQ : MQ_Split MQ [] [] <-> MQ_Clear MQ.
  Proof.
    split; intros.
    - induction MQ; kill H; eattac.
    - induction MQ; kill H; eattac.
  Qed.

  Lemma MQ_Split_nil_inv_r MQ I O : MQ_Clear MQ -> MQ_Split MQ I O <-> I = [] /\ O = [].
  Proof.
    split; intros.
    - induction MQ. kill H0; attac.
      kill H. destruct a; kill H1. kill H0. apply IHMQ; attac.
    - hsimpl in *; subst; induction MQ; attac.
  Qed.

  Lemma MQ_Split_recv_inv n v MQ I O : MQ_Split (TrRecv n v :: MQ) I O <-> exists I', MQ_Split MQ I' O /\ I = (n,v)::I'.
  Proof.
    split; intros.
    - kill H. eattac.
    - eattac.
  Qed.

  Lemma MQ_Split_send_inv n v MQ I O : MQ_Split (TrSend n v :: MQ) I O <-> exists O', MQ_Split MQ I O' /\ O = (n,v)::O'.
  Proof.
    split; intros.
    - kill H. eattac.
    - eattac.
  Qed.

  Lemma MQ_Split_erecv_inv n v MQ I O : MQ_Split (EvRecv n v :: MQ) I O <-> MQ_Split MQ I O.
  Proof. split; intros. kill H. eattac. Qed.

  #[export] Hint Rewrite -> @MQ_Split_nil_inv_r @MQ_Split_nil_inv_l using spank : LTS LTS_concl.

  #[export] Hint Rewrite -> @MQ_Split_recv_inv @MQ_Split_send_inv @MQ_Split_erecv_inv using spank : LTS_L LTS_concl_L.


  (** Any queue can be split like that *)
  Lemma MQ_Split_exists : forall MQ, exists I O, MQ_Split MQ I O.

  Proof with (auto with LTS).
    induction MQ.
    exists []. exists []...

    destruct IHMQ as [i [o MQS]].

    destruct a.
    - exists i, ((n, v)::o)...
    - exists ((n, v)::i), o...
    - exists i, o...
  Qed.


  Lemma MQ_Split_split1 : forall [ev MQ I O],
      MQ_Split (ev :: MQ) I O ->
      exists I0 I1 O0 O1,
        MQ_Split [ev] I0 O0
        /\ MQ_Split MQ I1 O1
        /\ I = I0 ++ I1
        /\ O = O0 ++ O1.

  Proof with eattac.
    ltac1:(intros until O). intros HS.
    destruct ev; eattac.
  Qed.


  Lemma MQ_Split_split1_inv : forall ev MQ I O,
      MQ_Split (ev :: MQ) I O <->
        exists I0 I1 O0 O1,
          MQ_Split [ev] I0 O0
          /\ MQ_Split MQ I1 O1
          /\ I = I0 ++ I1
          /\ O = O0 ++ O1.
  Proof.
    split; intros.
    - apply MQ_Split_split1; auto.
    - destruct ev; eattac.
  Qed.


  Lemma MQ_Split_seq1 : forall [ev MQ I0 I1 O0 O1],
      MQ_Split [ev] I0 O0 ->
      MQ_Split MQ I1 O1 ->
      MQ_Split (ev :: MQ) (I0 ++ I1) (O0 ++ O1).

  Proof with eattac.
    destruct ev...
  Qed.

  #[export] Hint Resolve MQ_Split_seq1 : LTS.


  Lemma MQ_Split_seq : forall [MQ0 MQ1 I0 I1 O0 O1],
      MQ_Split MQ0 I0 O0 ->
      MQ_Split MQ1 I1 O1 ->
      MQ_Split (MQ0 ++ MQ1) (I0 ++ I1) (O0 ++ O1).

  Proof with attac.
    induction MQ0; ltac1:(intros until O1); intros HS0 HS1.
    inversion HS0...

    apply MQ_Split_split1 in HS0
        as (I00 & I01 & O00 & O01 & HS00 & HS01 & HEqI & HEqO);
      subst.

    assert (MQ_Split (MQ0 ++ MQ1) (I01 ++ I1) (O01 ++ O1))...

    repeat (rewrite <- app_assoc in * ).
    repeat (rewrite <- app_comm_cons in * ).
    eauto with LTS.
  Qed.

  #[export] Hint Resolve MQ_Split_seq : LTS.


  Lemma MQ_Split_split : forall [MQ0 MQ1 I O],
      MQ_Split (MQ0 ++ MQ1) I O ->
      exists I0 I1 O0 O1,
        MQ_Split MQ0 I0 O0
        /\ MQ_Split MQ1 I1 O1
        /\ I = I0 ++ I1
        /\ O = O0 ++ O1.

  Proof with eattac.
    induction MQ0; intros *; intro HS.
    - repeat eexists...
    - destruct (MQ_Split_split1 HS)
        as (I00 & I01 & O00 & O01 & ?);
        subst.

      assert (MQ_Split (MQ0 ++ MQ1) I01 O01) as HS0 by apply H.

      apply IHMQ0 in HS0 as (I10 & I11 & O10 & O11 & ?); subst...
      exists (I00 ++ I10), I11, (O00 ++ O10), O11.
      eattac.
  Qed.


  Lemma MQ_Split_split_inv : forall MQ0 MQ1 I O,
      MQ_Split (MQ0 ++ MQ1) I O <->
        exists I0 I1 O0 O1,
          MQ_Split MQ0 I0 O0
          /\ MQ_Split MQ1 I1 O1
          /\ I = I0 ++ I1
          /\ O = O0 ++ O1.

  Proof with eattac.
    induction MQ0; intros *; (split > [intro HS | intros HEx]).
    - eattac.
    - eattac.
    - eapply MQ_Split_split; eauto.
    - destruct a; eattac.
  Qed.

  #[export] Hint Rewrite -> @MQ_Split_split_inv using assumption : LTS LTS_concl.


  (** Split is deterministic for any queue. *)
  Lemma MQ_Split_det : forall [MQ I O I' O'],
      MQ_Split MQ I O ->
      MQ_Split MQ I' O' <->
        (I = I' /\ O = O').

  Proof with eattac.
    induction MQ; eattac.
    all: destruct a; hsimpl in *.

    eapply IHMQ in H.
    all: try (eapply IHMQ in H; eauto; eapply H in H0; eattac).
    apply H in H0. eattac.
  Qed.


  (** Pushing a receive to the queue is reflected in the split *)
  Lemma MQ_Split_push_recv : forall [MQ I O] n v,
      MQ_Split MQ I O <->
        MQ_Split (MQ ++ [TrRecv n v]) (I ++ [(n, v)]) O.

  Proof with attac.
    split; generalize dependent I O n v.
    all: induction MQ; eattac.
    all: kill H; hsimpl in *; eattac.
  Qed.

  #[export] Hint Immediate MQ_Split_push_recv : LTS.


  (** Pushing a send to the queue is reflected in the split *)
  Lemma MQ_Split_push_send : forall [MQ I O] n v,
      MQ_Split MQ I O ->
      MQ_Split (MQ ++ [TrSend n v]) I (O ++ [(n, v)]).

  Proof.
    eattac.
  Qed.

  #[export] Hint Immediate MQ_Split_push_send : LTS.


  (** Pushing a monitor msg to the queue is reflected in the split *)
  Lemma MQ_Split_push_mrecv : forall [MQ I O] n v,
      MQ_Split MQ I O <->
        MQ_Split (MQ ++ [EvRecv n v]) I O.

  Proof. eattac. Qed.

  #[export] Hint Immediate MQ_Split_push_mrecv : LTS.


  (** Pushing a monitor msg to the queue is reflected in the split *)
  Lemma MQ_Split_push_mrecvs : forall [MQ MQ' I O],
      MQ_Clear MQ' ->
      MQ_Split (MQ ++ MQ') I O <-> MQ_Split MQ I O.

  Proof. eattac. Qed.

  #[export] Hint Rewrite -> MQ_Split_push_mrecvs using solve [auto 4 with datatypes] : LTS_R LTS_concl_R.


  Fixpoint MQ_r (MQ : list Event) : Que Val :=
    match MQ with
    | [] => []
    | TrRecv n v :: MQ' => (n, v) :: MQ_r MQ'
    | _ :: MQ' => MQ_r MQ'
    end.


  Fixpoint MQ_s (MQ : list Event) : Que Val :=
    match MQ with
    | [] => []
    | TrSend n v :: MQ' => (n, v) :: MQ_s MQ'
    | _ :: MQ' => MQ_s MQ'
    end.


  Definition mq_dI MS := pq_I (mq_S MS) ++ MQ_r (mq_MQ MS).
  Definition mq_dP MS := pq_P (mq_S MS).
  Definition mq_dO MS := MQ_s (mq_MQ MS) ++ pq_O (mq_S MS).

  #[export] Hint Transparent mq_dI mq_dP mq_dO : LTS.


  Lemma MQ_Split_rs MQ : MQ_Split MQ (MQ_r MQ) (MQ_s MQ).
  Proof. induction MQ; eattac. destruct a; eattac. Qed.

  Lemma r_MQ_Split [MQ I] {O} : MQ_Split MQ I O -> I = MQ_r MQ.
  Proof.
    revert I O.
    induction MQ; intros; eattac; kill H; apply IHMQ in H0; attac.
  Qed.

  Lemma s_MQ_Split [MQ I O] : MQ_Split MQ I O -> O = MQ_s MQ.
  Proof.
    revert I O.
    induction MQ; intros; eattac; kill H; apply IHMQ in H0; attac.
  Qed.

  #[export] Hint Immediate MQ_Split_rs : LTS.
  #[export] Hint Resolve r_MQ_Split s_MQ_Split : LTS.

  Lemma MQ_Split_rs_inv MQ I O : MQ_Split MQ I O <-> I = MQ_r MQ /\ O = MQ_s MQ.
  Proof. eattac. Qed.

  #[export] Hint Rewrite -> MQ_Split_rs_inv using assumption : LTS.


  Lemma MQ_r_In [MQ n v] : List.In (TrRecv n v) MQ -> List.In (n, v) (MQ_r MQ).
  Proof. intros; induction MQ; intros; hsimpl in *; attac.
         destruct H; subst; simpl in *; attac. destruct a; attac.
  Qed.

  Lemma MQ_s_In [MQ n v] : List.In (TrSend n v) MQ -> List.In (n, v) (MQ_s MQ).
  Proof. intros; induction MQ; intros; hsimpl in *; attac.
         destruct H; subst; simpl in *; attac. destruct a; attac.
  Qed.

  Lemma In_MQ_r MQ n v : List.In (n, v) (MQ_r MQ) -> List.In (TrRecv n v) MQ.
  Proof. intros; induction MQ; intros; hsimpl in *; attac.
         destruct a; attac. destruct H; hsimpl in *; eattac.
  Qed.

  Lemma In_MQ_s [MQ n v] : List.In (n, v) (MQ_s MQ) -> List.In (TrSend n v) MQ.
  Proof. intros; induction MQ; intros; hsimpl in *; attac.
         destruct a; attac. destruct H; hsimpl in *; eattac.
  Qed.

  #[export] Hint Immediate MQ_r_In MQ_s_In In_MQ_r In_MQ_s : LTS.
  #[export] Hint Resolve MQ_r_In MQ_s_In : LTS. (* strategy: the rewriter will reduce the other way, so solver has to infer it back*)


  Lemma MQ_r_In_inv MQ n v : List.In (TrRecv n v) MQ <-> List.In (n, v) (MQ_r MQ).
  Proof. split; intros; eauto with LTS. Qed.

  Lemma MQ_s_In_inv MQ n v : List.In (TrSend n v) MQ <-> List.In (n, v) (MQ_s MQ).
  Proof. split; intros; eauto with LTS. Qed.

  #[export] Hint Rewrite <- MQ_r_In_inv MQ_s_In_inv using assumption : LTS LTS_concl.


  Lemma MQ_r_app MQ0 MQ1 : MQ_r (MQ0 ++ MQ1) = MQ_r MQ0 ++ MQ_r MQ1.
  Proof. induction MQ0; simpl in *; eattac. destruct a; eattac. Qed.

  Lemma MQ_s_app MQ0 MQ1 : MQ_s (MQ0 ++ MQ1) = MQ_s MQ0 ++ MQ_s MQ1.
  Proof. induction MQ0; simpl in *; eattac. destruct a; eattac. Qed.

  #[export] Hint Rewrite -> @MQ_r_app MQ_s_app using assumption : LTS LTS_concl.
  #[export] Hint Resolve MQ_r_app MQ_s_app : LTS.


  Lemma MQ_r_mrecv_nil MQ : MQ_Clear MQ -> MQ_r MQ = [].
  Proof. induction MQ; eattac. Qed.

  Lemma MQ_s_mrecv_nil MQ : MQ_Clear MQ -> MQ_s MQ = [].
  Proof. induction MQ; eattac. Qed.

  Lemma MQ_nil_mrecv MQ : MQ_r MQ = [] -> MQ_s MQ = [] -> MQ_Clear MQ.
  Proof. induction MQ; eattac. destruct a; eattac. Qed.

  #[export] Hint Rewrite -> @MQ_r_mrecv_nil @MQ_s_mrecv_nil using assumption : LTS LTS_concl.
  #[export] Hint Resolve MQ_r_mrecv_nil MQ_s_mrecv_nil MQ_nil_mrecv : LTS.


  Lemma MQ_r_app_mrecv MQ0 MQ1 : MQ_Clear MQ1 -> MQ_r (MQ0 ++ MQ1) = MQ_r MQ0.
  Proof. eattac. Qed.

  Lemma MQ_s_app_mrecv MQ0 MQ1 : MQ_Clear MQ1 -> MQ_s (MQ0 ++ MQ1) = MQ_s MQ0.
  Proof. eattac. Qed.

  Lemma MQ_r_mrecv_app MQ0 MQ1 : MQ_Clear MQ0 -> MQ_r (MQ0 ++ MQ1) = MQ_r MQ1.
  Proof. eattac. Qed.

  Lemma MQ_s_mrecv_app MQ0 MQ1 : MQ_Clear MQ0 -> MQ_s (MQ0 ++ MQ1) = MQ_s MQ1.
  Proof. eattac. Qed.

  #[export] Hint Rewrite -> @MQ_r_app_mrecv @MQ_s_app_mrecv @MQ_r_mrecv_app MQ_s_mrecv_app using assumption : LTS_R LTS_concl_r.
  #[export] Hint Resolve MQ_r_app_mrecv MQ_s_app_mrecv MQ_r_mrecv_app MQ_s_mrecv_app : LTS.


  Lemma MQ_r_clear_mrecv_nil (MQ : MQ_clear) : MQ_r (proj1_sig MQ) = [].
  Proof. induction MQ; eattac. Qed.

  Lemma MQ_s_clear_mrecv_nil (MQ : MQ_clear) : MQ_s (proj1_sig MQ) = [].
  Proof. induction MQ; eattac. Qed.

  #[export] Hint Rewrite -> @MQ_r_clear_mrecv_nil @MQ_s_clear_mrecv_nil using assumption : LTS LTS_concl.
  #[export] Hint Resolve MQ_r_clear_mrecv_nil MQ_s_clear_mrecv_nil : LTS.


  Lemma MQ_r_clear_app_mrecv (MQ0 MQ1 : MQ_clear) : MQ_r (proj1_sig MQ0 ++ proj1_sig MQ1) = MQ_r (proj1_sig MQ0).
  Proof. eattac. Qed.

  Lemma MQ_s_clear_app_mrecv (MQ0 MQ1 : MQ_clear) : MQ_s (proj1_sig MQ0 ++ proj1_sig MQ1) = MQ_s (proj1_sig MQ0).
  Proof. eattac. Qed.

  Lemma MQ_r_clear_mrecv_app (MQ0 MQ1 : MQ_clear) : MQ_r (proj1_sig MQ0 ++ proj1_sig MQ1) = MQ_r (proj1_sig MQ1).
  Proof. eattac. Qed.

  Lemma MQ_s_clear_mrecv_app (MQ0 MQ1 : MQ_clear) : MQ_s (proj1_sig MQ0 ++ proj1_sig MQ1) = MQ_s (proj1_sig MQ1).
  Proof. eattac. Qed.

  #[export] Hint Rewrite -> @MQ_r_clear_app_mrecv @MQ_s_clear_app_mrecv @MQ_r_clear_mrecv_app @MQ_s_clear_mrecv_app using assumption : LTS LTS_concl.
  #[export] Hint Immediate MQ_r_clear_app_mrecv MQ_s_clear_app_mrecv MQ_r_clear_mrecv_app MQ_s_clear_mrecv_app : LTS.


  (** Deinstrumentation. Strips off monitoring and disassembles monitor's queue. *)
  Definition deinstr (MS0 : MQued) : PQued :=
    match MS0 with
    | (mq MQ0 _ (pq I0 P0 O0)) => (pq (I0 ++ (MQ_r MQ0)) P0 (MQ_s MQ0 ++ O0))
    end.

  #[reversible=no] Coercion deinstr : MQued >-> PQued.


  (** Deinstrumentation is inversion of instrumentation *)
  Theorem deinstr_instr : forall MQ M S, deinstr (instr MQ M S) = S.

  Proof.
    intros.
    destruct S.
    induction MQ; simpl; attac.
  Qed.

  #[export] Hint Rewrite @deinstr_instr using assumption : LTS.
  #[export] Hint Resolve deinstr_instr : LTS.


  Lemma deinstr_In_recv [MQ M S I P O n v] :
    List.In (TrRecv n v) MQ ->
    deinstr (mq MQ M S) = (pq I P O) ->
    List.In (n, v) I.

  Proof.
    revert I P O n v.

    induction MQ; intros; attac.
    destruct S.
    hsimpl.
    destruct H; attac.
    destruct a; attac.
  Qed.


  Lemma deinstr_In_send [MQ M S I P O n v] :
    List.In (TrSend n v) MQ ->
    deinstr (mq MQ M S) = (pq I P O) ->
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
    | MActM (Send _ _) => True (* Monitor may need to send to reach ready state*)
    | MActM (Recv _ _) => False
    | MActM Tau        => True (* Monitor may need to tau to reach ready state*)
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
      (mq MQ0 M0 (pq I0 P0 O0) =(a)=> mq MQ1 M1 (pq I1 P1 O1)) ->
      Flushing_act a ->
      exists MQ', MQ0 = MQ' ++ MQ1.

  Proof.
    intros.
    inversion H; subst; inversion H0; subst; simpl in *; ltac1:(try contradiction).
    - exists []. auto.
    - exists [EvRecv n v]. auto.
    - exists []. auto.
    - exists [TrSend n v]. auto.
    - exists [TrRecv n v]. auto.
  Qed.


  (** Flushing path can be reapplied with a bigger monitor queue, and the residue will remain. *)
  Lemma Flushing_cont : forall [mpath] [MQ0 M0 S0] [MQ1 M1 S1] MQ',
      (mq MQ0 M0 S0 =[mpath]=> mq MQ1 M1 S1) ->
      Forall Flushing_act mpath ->
      (mq (MQ0 ++ MQ') M0 S0 =[mpath]=> mq (MQ1 ++ MQ') M1 S1).

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
      kill T0; try (contradiction).
      eapply IHmpath in T1; auto.
      unshelve eapply (path_seq1 _ T1)...
    - case (MActM ?x).
      kill T0; try (contradiction)...
      eapply IHmpath in T1; auto.
      unshelve eapply (path_seq1 _ T1)...
      destruct M3. eattac.
  Qed.


  (** Flushing act can be reapplied with a shorter monitor queue*)
  Lemma Flushing_retract1 : forall [a] [MQ0 M0 S0] [MQ1 M1 S1] MQ',
      (mq (MQ0 ++ MQ') M0 S0 =(a)=> mq (MQ1 ++ MQ') M1 S1) ->
      Flushing_act a ->
      (mq MQ0 M0 S0 =(a)=> mq MQ1 M1 S1).

  Proof.
    intros.
    destruct M1.
    consider (_ =(_)=> _); eattac 10.
  Qed.


  (** Flushing path can be reapplied with a shorter monitor queue *)
  Lemma Flushing_retract : forall [mpath] [MQ0 M0 S0] [MQ1 M1 S1] MQ',
      (mq (MQ0 ++ MQ') M0 S0 =[mpath]=> mq (MQ1 ++ MQ') M1 S1) ->
      Forall Flushing_act mpath ->
      (mq MQ0 M0 S0 =[mpath]=> mq MQ1 M1 S1).

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
        enough (mq MQ0 M0 S0 =( a )=> mq MQ1 M1 S1); eauto using Flushing_retract1 with LTS.
      }

      clear - H1 H2.
      generalize dependent MQ1' M1 S1.
      induction mpath; eattac.
      destruct N1 as [MQ11' M11 S11].
      assert (exists MQ11, MQ11' = MQ11 ++ MQ'); eattac.

      consider (_ =(a)=> _); eattac.
  Qed.


  Definition flush1 (MQ : list Event) (M : Mon) : option MAct :=
    match state M with
    | MRecv _ =>
        match MQ with
        | [] => None
        | TrRecv nc v :: _ => Some (MActP (Recv nc v))
        | TrSend nc v :: _ => Some (MActT (Send nc v))
        | EvRecv nc e :: _ => Some (MActM (Recv nc e))
        end
    | MSend nc e _ => Some (MActM (Send nc e))
    end.

  Fixpoint mcode_measure (M : MCode) : (nat * MState) :=
    match M with
    | MRecv s => (O, s)
    | MSend nc e Mc =>
        let (n, s) := mcode_measure Mc
        in (S n, s)
    end.
  Fixpoint flush_measure (MQ : list Event) (M : Mon) : nat :=
    match MQ with
    | [] =>
        let (n, _) := mcode_measure (state M) in
        n
    | e :: MQ' =>
        let (n, s) := mcode_measure (state M) in
        S n + flush_measure MQ' {|handle:=handle M; state:=handle M e s|}
    end.

  Definition Event_to_MAct (e : Event) : MAct :=
    match e with
    | TrRecv nc v => MActP (Recv nc v)
    | TrSend nc v => MActT (Send nc v)
    | EvRecv nc e => MActM Tau
    end.

  Fixpoint flush_mcode (M : MCode) : list MAct :=
    match M with
    | MRecv s => []
    | MSend nc e Mc => MActM (Send nc e) :: flush_mcode Mc
    end.

  Fixpoint mk_flush_path (MQ : list Event) (M : Mon) : list MAct :=
    match MQ with
    | [] => flush_mcode (state M)
    | e :: MQ' =>
        let mpath0 := flush_mcode (state M) in
        let mpath1 := mk_flush_path MQ' {|handle:=handle M; state:=handle M e (next_state (state M))|} in
        mpath0 ++ Event_to_MAct e :: mpath1
    end.

  Fixpoint flush_Mstate (MQ : list Event) (M : Mon) : MState :=
    match MQ with
    | [] => next_state (state M)
    | e :: MQ' =>
        flush_Mstate MQ' {|handle:=handle M; state:=handle M e (next_state (state M))|}
    end.

  Definition flush_M MQ M := {|handle:=handle M;state:=MRecv (flush_Mstate MQ M)|}.
  Definition flush_S MQ S := match S with pq I0 P0 O0 => pq (I0 ++ MQ_r MQ) P0 O0 end.
  Definition flush_path MS := match MS with mq MQ M _ => mk_flush_path MQ M end.
  Definition flush_MS MS0 := match MS0 with mq MQ0 M0 S0 => mq [] (flush_M MQ0 M0) (flush_S MQ0 S0) end.

  #[export] Hint Unfold flush_M : LTS.
  #[export] Hint Transparent flush_M flush_S flush_path flush_MS : LTS.


  Lemma flush_S_Clear MQ S0 : MQ_Clear MQ -> flush_S MQ S0 = S0.
  Proof. destruct S0; attac. Qed.

  #[export] Hint Rewrite -> flush_S_Clear using spank : LTS LTS_concl.


  Lemma flush_skip_M MQ nc e h s:
    flush_M MQ {|handle:=h; state:=MSend nc e s|} = flush_M MQ {|handle:=h; state:=s|}.

  Proof.
    generalize dependent nc e h s.
    induction MQ; attac.
  Qed.

  Lemma flush_cont_M MQ0 MQ1 M :
    flush_M (MQ0 ++ MQ1) M = flush_M MQ1 (flush_M MQ0 M).

  Proof.
    unfold flush_M.
    destruct M as [h s].
    generalize dependent s MQ1.
    induction MQ0; attac.
    induction MQ1; attac.
  Qed.

  #[export] Hint Rewrite -> flush_skip_M flush_cont_M using assumption : LTS LTS_concl.


  Lemma mk_flush_cont_path MQ0 MQ1 M :
    mk_flush_path (MQ0 ++ MQ1) M =
    mk_flush_path MQ0 M ++ mk_flush_path MQ1 (flush_M MQ0 M).

  Proof.
    unfold flush_M.
    destruct M as [h s].
    generalize dependent s MQ1.
    induction MQ0; attac.
    induction MQ1; attac.
    repeat (rewrite <- app_assoc in * ).
    repeat (rewrite <- app_comm_cons in * ).
    attac.
  Qed.


  Lemma flush_M_go : forall MQ M h s S,
      handle M = h ->
      state M = s ->
      mq MQ M S =[flush_mcode s]=> mq MQ {|handle:=handle M;state:=MRecv (next_state s)|} S.
  Proof.
    intros.
    destruct M; attac.
    generalize dependent h S.
    induction s; eattac.
  Qed.


  Lemma flush_go : forall MQ0 M0 S0,
    mq MQ0 M0 S0 =[ mk_flush_path MQ0 M0 ]=> mq [] (flush_M MQ0 M0) (flush_S MQ0 S0).

  Proof.
    intros.
    destruct M0 as [h s].
    destruct S0 as [I0 P0 O0].
    generalize dependent h s I0 P0 O0.
    induction MQ0; attac.
    - induction s; eattac.
    - eapply path_seq.
      1: eauto using flush_M_go.

      destruct a; eapply path_seq1; eattac 15.
      now replace (I0 ++ (n, v) :: MQ_r MQ0) with ((I0 ++ [(n, v)]) ++ MQ_r MQ0) by eattac.
  Qed.

  Lemma flush_go_MS : forall {MS0}, MS0 =[flush_path MS0]=> flush_MS MS0.
  Proof.
    unfold flush_MS.
    destruct MS0 as [MQ0 M0 S0].
    eauto using flush_go.
  Qed.

  #[export] Hint Resolve flush_go_MS flush_go : LTS.


  Lemma Event_to_MAct_Flushing : forall e, Flushing_act (Event_to_MAct e).
  Proof. destruct e; attac. Qed.

  Lemma flush_M_Flushing : forall M, Forall Flushing_act (flush_mcode M).
  Proof. induction M; attac. Qed.

  #[export] Hint Resolve Event_to_MAct_Flushing flush_M_Flushing : LTS.


  Lemma flush_path_Flushing : forall MQ M, Forall Flushing_act (mk_flush_path MQ M).
  Proof. induction MQ; hsimpl in *; attac. Qed.

  #[export] Hint Resolve flush_path_Flushing : LTS.


  Lemma flush_M_admin : forall M, flush_mcode M >:~ [].
  Proof. induction M; attac. Qed.

  #[export] Hint Resolve flush_M_admin : LTS.


  Lemma flush_path_admin : forall MQ M, MQ_Clear MQ -> mk_flush_path MQ M >:~ [].
  Proof.
    induction MQ; attac.

    enough ( MPath_to_PPath (flush_mcode (state M)) ++
               MPath_to_PPath
               (mk_flush_path MQ {| handle := handle M; state := handle M (EvRecv n msg) (next_state (state M)) |}) = [] ++ []
           ) by attac.

    rewrite <- MPath_to_PPath_app.
    eapply path_corr_app; eattac.
  Qed.

  #[export] Hint Resolve flush_path_admin : LTS.


  Hint Unfold flush_MS : LTS.
  Lemma flush_go_Clear : forall MQ M S, MQ_Clear MQ -> mq MQ M S =[mk_flush_path MQ M]=> mq [] (flush_M MQ M) S.
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

  Definition nil_Clear : MQ_clear := exist _ [] (Forall_nil _).

  Definition flush_instr : instr_t :=
    fun MQc Mr S => instr nil_Clear (flush_Mr (proj1_sig MQc) (proj1_sig Mr)) S.


  Lemma flush_go_instr : forall MQc Mr S0,
      instr MQc Mr S0 =[flush_path (instr MQc Mr S0)]=> flush_instr MQc Mr S0.

  Proof.
    unfold flush_instr, instr.
    intros.
    destruct S0 as [I0 P0 O0].
    attac.
  Qed.


  Lemma recv_is_ready h s :
    ready {|handle:=h;state:=MRecv s|}.

  Proof.
    eattac.
  Qed.

  #[export] Hint Resolve recv_is_ready : LTS.


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
      (mq (MQ0 ++ MQ1) M0 S0 =[ mk_flush_path MQ0 M0 ]=> mq MQ1 (flush_M MQ0 M0) (flush_S MQ0 S0)).

  Proof with ltac2:(eauto with LTS).
    destruct S0.
    intros.
    eapply Flushing_cont with (MQ0:=MQ0)(MQ1:=[])...
  Qed.


  (** Any state of a monitored process can be dragged to a "canonical" one, where the monitor is ready
  and has empty queue. **)
  Theorem flush_go_until_Clear : forall MQ0 MQ1 M0 S0,
      MQ_Clear MQ0 ->
      (mq (MQ0 ++ MQ1) M0 S0 =[ mk_flush_path MQ0 M0 ]=> mq MQ1 (flush_M MQ0 M0) S0).

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
      (mq MQ0 M0 (pq I0 P0 O0) =(ma)=> mq MQ1 M1 (pq I1 P1 O1)) ->
      (pq (I0 ++ MQ_r MQ0) P0 (MQ_s MQ0 ++ O0) =[MPath_to_PPath [ma]]=> pq (I1 ++ MQ_r MQ1) P1 (MQ_s MQ1 ++ O1)).

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
      (mq MQ0 M0 (pq I0 P0 O0) =[mpath]=> mq MQ1 M1 (pq I1 P1 O1)) ->
      (pq (I0 ++ MQ_r MQ0) P0 (MQ_s MQ0 ++ O0) =[MPath_to_PPath mpath]=> pq (I1 ++ MQ_r MQ1) P1 (MQ_s MQ1 ++ O1)).

  Proof with (eauto with LTS).
    induction mpath; intros.
    1: { attac. }

    hsimpl in * |-.

    destruct N1 as [MQ0' M0' [I0' P0' O0']].
    rewrite MPath_to_PPath_cons.

    eapply path_seq with (middle := pq (I0' ++ MQ_r MQ0') P0' (MQ_s MQ0' ++ O0'));
      eauto using corr_extraction1.
  Qed.


  Instance PQued_Transp_M : LTS MAct PQued | 10 :=
    {
      trans := fun (ma : MAct) (S0 S1 : PQued) =>
                 match MAct_to_PAct ma with
                 | None => S1 = S0
                 | Some a => @trans PAct PQued trans_pqued a S0 S1
                 end
    }.


  Lemma PQued_Transp_act [ma : MAct] [a : PAct] [S0 S1 : PQued] :
    ma >:- a ->
    (S0 =(ma)=> S1) <-> (S0 =(a)=> S1).

  Proof.
    unfold trans, PQued_Transp_M.
    intros.
    attac.
  Qed.


  Lemma PQued_Transp_skip [ma : MAct] [S0 S1 : PQued] :
    MAct_to_PAct ma = None ->
    (S0 =(ma)=> S1) <-> S1 = S0.

  Proof.
    unfold trans, PQued_Transp_M.
    intros.
    attac.
  Qed.

  #[export] Hint Rewrite -> PQued_Transp_act PQued_Transp_skip using spank : LTS LTS_concl.
  #[export] Hint Immediate PQued_Transp_act PQued_Transp_skip : LTS.
  #[export] Hint Resolve <- PQued_Transp_act PQued_Transp_skip : LTS.


  Lemma PQued_Transp_M_path : forall (mpath : list MAct) (S0 S1 : PQued),
      (S0 =[mpath]=> S1) <-> (S0 =[MPath_to_PPath mpath]=> S1).

  Proof.
    induction mpath; split; attac; unfold trans, PQued_Transp_M in *.
    - destruct (MAct_to_PAct a) eqn:?.
      + enough (N1 =[MPath_to_PPath mpath]=> S1) by attac.
        apply IHmpath; eattac.
      + eapply IHmpath; eattac.
    - destruct (MAct_to_PAct a) eqn:?; attac.
      + enough ((S0 =(a)=> N1) /\ (N1 =[mpath]=> S1)) by attac.
        split.
        * unfold trans, PQued_Transp_M; attac.
        * eapply IHmpath; eattac.
      + assert (S0 =(a)=> S0) by eattac.
        enough (S0 =[mpath]=> S1) by attac.
        eapply IHmpath; eattac.
  Qed.

  #[export] Hint Rewrite -> PQued_Transp_M_path using spank : LTS LTS_concl.
  #[export] Hint Immediate PQued_Transp_M_path : LTS.
  #[export] Hint Resolve <- PQued_Transp_M_path : LTS.


  (** If a monitored process progresses over a path, then the unmonitored process can follow a
  corresponding path, if the traces in the monitor's queue are converted to unconsumed sends and
  receives of the process. *)
  Theorem corr_extraction_instr : forall [mpath MS0 MS1],
      (MS0 =[mpath]=> MS1) ->
      (deinstr MS0 =[mpath]=> deinstr MS1).

  Proof with (attac).
    intros.

    destruct MS0 as [MQ0 M0 [I0 P0 O0]].
    destruct MS1 as [MQ1 M1 [I1 P1 O1]].

    eauto using corr_extraction with LTS.
  Qed.


  Notation "MS0 =[*]=> MS1" := (MS0 =[flush_path MS0]=> MS1) (at level 80) : type_scope.

  Theorem Transp_soundness_base : forall [mpath0 : list MAct] [MS0 MS1 : MQued],
      (MS0 =[ mpath0 ]=> MS1) ->
      (deinstr MS0 =[ mpath0 ++ flush_path MS1 ]=> deinstr (flush_MS MS1)).

  Proof.
    intros.

    assert (deinstr MS0 =[ mpath0 ]=> deinstr MS1) by eauto using corr_extraction_instr.
    enough  (deinstr MS1 =[ flush_path MS1 ]=> deinstr (flush_MS MS1)) by attac.
    enough (MS1 =[ flush_path MS1 ]=> flush_MS MS1) by eauto using corr_extraction_instr.
    eauto using flush_go_MS.
  Qed.


  Lemma Transp_completeness_tau : forall [S0 S1] MQ0 M0,
      (S0 =( Tau )=> S1) ->
      (instr MQ0 M0 S0 =(MActP Tau)=> instr MQ0 M0 S1).

  Proof.
    ltac1:(intros until M0).
    intros T. kill T; eattac 10.
  Qed.


  Lemma Transp_completeness_send_prep : forall [n v] [S0 S1] MQ0 M0,
      (S0 =( Send n v )=> S1) ->
      (mq MQ0 M0 S0 =[MActP (Send n v) :: mk_flush_path MQ0 M0]=> (mq [TrSend n v] (flush_M MQ0 M0) (flush_S MQ0 S1))).

  Proof.
    intros.

    eenough (mq (MQ0 ++ [TrSend n v]) M0 S1 =[mk_flush_path MQ0 M0]=> _) by eattac.
    eapply flush_go_until.
  Qed.


  Lemma Transp_completeness_send : forall [n v] [S0 S1] MQ0 M0,
      (S0 =( Send n v )=> S1) ->
      (mq MQ0 M0 S0 =[MActP (Send n v) :: mk_flush_path MQ0 M0 ++ [MActT (Send n v)]]=>
         (mq [] {|handle:=handle M0; state:=handle M0 (TrSend n v) (flush_Mstate MQ0 M0)|} (flush_S MQ0 S1))).

  Proof.
    intros.

    eenough (mq [TrSend n v] (flush_M MQ0 M0) (flush_S MQ0 S1) =(MActT (Send n v))=> _)
      by (rewrite app_comm_cons; eauto using Transp_completeness_send_prep with LTS).

    eattac.
  Qed.


  Lemma Flushing_clear1 [a] [MQ0 M0 S0 MS1] :
    (mq MQ0 M0 S0 =(a)=> MS1) ->
    MQ_Clear MQ0 ->
    Flushing_act a ->
    [a] >:~ [].

  Proof.
    intros.
    destruct_ma a; attac.
  Qed.


  Lemma Flushing_clear [mpath] [MQ0 M0 S0 MS1] :
    (mq MQ0 M0 S0 =[mpath]=> MS1) ->
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


  Definition handle_Mr (e : Event) (Mr : Mon_ready) : Mon :=
    {|handle:=handle (proj1_sig Mr); state:=handle (proj1_sig Mr) e (next_state (state (proj1_sig Mr)))|}.

  Definition plain [A : Type] : (list Event -> Mon -> A) -> (MQ_clear -> Mon_ready -> A) :=
    fun f => fun MQc Mr => f (proj1_sig MQc) (proj1_sig Mr).


  Lemma Transp_completeness_send_instr : forall [n v] [S0 S1] MQ0 M0,
      (S0 =( Send n v )=> S1) ->
        (instr MQ0 M0 S0 =[MActP (Send n v) :: flush_path (instr MQ0 M0 S0) ++ [MActT (Send n v)]]=>
           (mq [] (handle_Mr (TrSend n v) (plain flush_Mr MQ0 M0)) S1)).

  Proof with eattac.
    intros.

    destruct MQ0 as [MQ0 HMQ0].
    destruct M0 as [M0 HM0].

    unfold handle_Mr, instr, flush_Mr, plain.
    simpl.

    ltac1:(replace S1 with (flush_S MQ0 S1) by eauto using flush_S_Clear with LTS).
    eauto using Transp_completeness_send.
  Qed.


  Lemma Transp_completeness_recv_prep : forall n v MQ0 M0 S0,
    (mq MQ0 M0 S0 =[MActT (Recv n v) :: mk_flush_path MQ0 M0]=> mq [TrRecv n v] (flush_M MQ0 M0) (flush_S MQ0 S0)).

  Proof.
    intros.

    eenough ( mq (MQ0 ++ [TrRecv n v]) M0 S0 =[mk_flush_path MQ0 M0]=> _) by eattac.
    eapply flush_go_until.
  Qed.


  Lemma Transp_completeness_recv : forall [n v] [S0 S1] MQ0 M0,
      MQ_Clear MQ0 ->
      (S0 =( Recv n v )=> S1) ->
      (mq MQ0 M0 S0 =[MActT (Recv n v) :: mk_flush_path MQ0 M0 ++ [MActP (Recv n v)]]=> mq [] {|handle:=handle M0; state:=handle M0 (TrRecv n v) (flush_Mstate MQ0 M0)|} S1).

  Proof.
    intros.

    eenough (mq [TrRecv n v] (flush_M MQ0 M0) (flush_S MQ0 S0) =(MActP (Recv n v))=> _)
      by (rewrite app_comm_cons; eauto using Transp_completeness_recv_prep with LTS).

    eattac 10.
  Qed.


  Theorem Transp_completeness1 : forall [a S0 S1] MQ0 M0,
      (S0 =( a )=> S1) ->
      exists mpath0 ma mpath1 M1,
        (instr MQ0 M0 S0 =[ mpath0 ++ ma :: mpath1]=> mq [] M1 S1)
        /\ mpath0 >:~ []
        /\ ma >:- a
        /\ mpath1 >:~ [].

  Proof.
    intros.
    destruct a.
    - exists (MActP (Send n v) :: plain mk_flush_path MQ0 M0), (MActT (Send n v)), [].
      eexists.
      split.
      1: eapply Transp_completeness_send_instr; eauto. (* TODO why? *)
      eattac.
    - exists [], (MActT (Recv n v)), (plain mk_flush_path MQ0 M0 ++ [MActP (Recv n v)]).
      eexists.
      split.
      1: eapply Transp_completeness_recv; eauto. (* TODO why? *)
      all: eattac.
    - exists [], (MActP Tau).
      exists (flush_path (instr MQ0 M0 S1)).
      eexists.

      split.
      + enough (instr MQ0 M0 S0 =(MActP Tau)=> instr MQ0 M0 S1) by (hsimpl; attac).
        eauto using Transp_completeness_tau.
      + eattac.
  Qed.


  Theorem Transp_completeness1_instr : forall [a S0 S1] MQ0 M0,
      (S0 =( a )=> S1) ->
      exists mpath0 ma mpath1 M1,
        (instr MQ0 M0 S0 =[ mpath0 ++ ma :: mpath1]=> instr nil_Clear M1 S1)
        /\ mpath0 >:~ []
        /\ ma >:- a
        /\ mpath1 >:~ [].

  Proof.
    intros.

    consider ( exists mpath0 ma mpath1 M1,
                 (### instr MQ0 M0 S0 =[ mpath0 ++ ma :: mpath1]=> mq [] M1 S1)
                 /\ mpath0 >:~ []
                 /\ ma >:- a
                 /\ mpath1 >:~ []
           ) by eauto using Transp_completeness1.

    assert (mq [] M1 S1 =[*]=> mq [] (flush_M [] M1) S1) by eauto using flush_go with LTS.

    exists mpath0, ma, (mpath1 ++ mk_flush_path [] M1).
    replace (mpath0 ++ ma :: mpath1 ++ mk_flush_path [] M1)
      with  ((mpath0 ++ ma :: mpath1) ++ mk_flush_path [] M1)
      by attac.
    unshelve eexists (exist _ (flush_M [] M1) _); eattac.
  Qed.


  (** The Completeness. For any path of an unmonitored process, there exists a corresponding path if
  monitoring is applied. The final state is also a result of generic monitor application. *)
  Theorem Transp_completeness : forall [path S0 S1] MQ0 M0,
      (S0 =[ path ]=> S1) ->
      exists mpath M1,
        (instr MQ0 M0 S0 =[ mpath ]=> instr (exist _ [] (Forall_nil _)) M1 S1)
        /\ mpath >:~ path.

  Proof with eattac.
    induction path; intros.
    - exists (plain mk_flush_path MQ0 M0), (plain flush_Mr MQ0 M0).
      eattac.

    - hsimpl in *.
      rename S1 into S2.
      rename N1 into S1.

      consider (exists mpath0 ma mpath1 M1,
                 (### instr MQ0 M0 S0 =[ mpath0 ++ ma :: mpath1]=> instr (exist _ [] (Forall_nil _)) M1 S1)
                 /\ mpath0 >:~ []
                 /\ ma >:- a
                 /\ mpath1 >:~ []) by eauto using Transp_completeness1_instr.

      consider (
          exists mpath2 M2,
            (### instr (exist _ [] (Forall_nil is_EvRecv)) M1 S1 =[ mpath2 ]=> instr (exist _ [] (Forall_nil is_EvRecv)) M2 S2)
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
  Proof. destruct MQ, M, state0; attac. Qed.

  #[export] Hint Rewrite -> flushing_nil_MQ using spank : LTS LTS_concl.

  #[export] Hint Resolve flushing_nil_M : LTS.


  Fixpoint flushing_M_artifact (self : Name) (M : MCode) (n : Name) : list Event :=
    match M with
    | MRecv _ => []
    | MSend (n', t) e M' =>
        let MQ := flushing_M_artifact self M' n in
        if NAME.eqb n n' then EvRecv (self, t) e :: MQ else MQ
    end.

  Fixpoint flushing_artifact (self : Name) (MQ : list Event) (M : Mon) (n : Name) : list Event :=
    match MQ with
    | [] => flushing_M_artifact self (state M) n
    | e :: MQ' =>
        let MQ0 := flushing_M_artifact self (state M) n in
        let MQ1 := flushing_artifact self MQ' {|handle:=handle M; state:=handle M e (next_state (state M))|} n in
        MQ0 ++ match e with
          | TrSend (n', t) v => if NAME.eqb n n' then TrRecv (self, t) v :: MQ1 else MQ1
          | _ => MQ1
          end
    end.


  Fixpoint path_artifact (self : Name) (mpath : list MAct) (n : Name) : list Event :=
    match mpath with
    | [] => []
    | MActM (Send (n', t) e) :: mpath' =>
        if NAME.eqb n n' then EvRecv (self, t) e :: path_artifact self mpath' n else path_artifact self mpath' n
    | MActT (Send (n', t) v) :: mpath' =>
        if NAME.eqb n n' then TrRecv (self, t) v :: path_artifact self mpath' n else path_artifact self mpath' n
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

    destruct M as [h s].
    generalize dependent s.
    induction MQ0; attac.
    - blast_cases; destruct MQ1; attac.
    - blast_cases; rewrite IHMQ0; attac.
  Qed.

End MON_F.

Module Type MON(Conf : MON_PROC_CONF) := Conf <+ MON_PARAMS <+ MON_F.
