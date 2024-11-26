From Coq Require Import Structures.Equalities.

Require Import DlStalk.Tactics.
Require Import DlStalk.LTS.

Close Scope nat.

Module Empty.
End Empty.


Module Type UsualDecidableSet.
  Parameter Inline t' : Set.
  Include UsualDecidableTypeFull with Definition t := t'.
End UsualDecidableSet.


Module UsualDecidableSetHints(Import M : UsualDecidableSet).
  #[global] Hint Transparent t : core.
  #[global] Hint Unfold t : core.


  Lemma eqb_neq_inv : forall n0 n1, eqb n0 n1 = false <-> n0 <> n1.
  Proof. split; intros; destruct (eqb n0 n1) eqn:HE; auto;
           try (apply eqb_eq in HE); subst; try (congruence).
         intros X. apply eqb_eq in X; subst; try (congruence).
  Qed.


  Lemma same_eqb_inv : forall n, eqb n n = true.
  Proof. intros; destruct (eqb n n) eqn:HE; auto.
         rewrite eqb_neq_inv in HE. congruence.
  Qed.


  Lemma neq_neqb_inv : forall n0 n1, n0 <> n1 -> eqb n0 n1 = false.
  Proof. intros. apply eqb_neq_inv. auto.
  Qed.


  #[global] Hint Rewrite -> eqb_eq eqb_neq_inv using spank : LTS.
  #[global] Hint Rewrite <- eqb_eq eqb_neq_inv using spank : LTS_concl.
  #[global] Hint Rewrite -> same_eqb_inv neq_neqb_inv using spank : LTS LTS_concl.
  #[global] Hint Resolve eq_dec eqb_eq : LTS.
End UsualDecidableSetHints.


Module Type MODEL_PARAMS.
  Declare Module Val : UsualDecidableSet.
  Declare Module Name : UsualDecidableSet.
  Declare Module Tag : UsualDecidableSet.
End MODEL_PARAMS.


Module Type MODEL_DEFS(Model : MODEL_PARAMS).

  #[global] Definition Val := Model.Val.t'.
  #[global] Definition Name := Model.Name.t'.
  #[global] Definition Tag := Model.Tag.t'.


  #[global] Hint Transparent Name Tag : core.
  #[global] Hint Unfold Name Tag : core.


  #[global] Definition NChan : Set := (Name * Tag)%type.
  #[global] Hint Transparent NChan : core.


  Fact NChan_eq_dec : forall (n0 n1 : NChan), {n0 = n1} + {n0 <> n1}.

  Proof.
    intros.
    destruct n0; destruct n1.
    destruct (Model.Name.eq_dec n n0); destruct (Model.Tag.eq_dec t t0);
      subst; first [left; now auto | right; congruence].
  Qed.

  #[export] Hint Resolve NChan_eq_dec : LTS.


  Class gen_Act (Act : Set) (Payload : Set) :=
    {
      send : NChan -> Payload -> Act;
      recv : NChan -> Payload -> Act;
      tau : Act;
      ia : Act -> Prop;

      ia_disjoint : forall n v, not (ia (recv n v)) /\ not (ia (send n v));
      ia_tau : ia tau;
      send_recv : forall n v, send n v <> recv n v;
    }.


  Inductive Act (Payload : Set) : Set :=
  | Send (n : NChan) (v : Payload) : Act Payload
  | Recv (n : NChan) (v : Payload) : Act Payload
  | Tau
  .
  #[export] Hint Constructors Act : LTS.

  Arguments Send {Payload}.
  Arguments Recv {Payload}.
  Arguments Tau {Payload}.

  Module Export NameHints := UsualDecidableSetHints(Model.Name).
  Module Export TagHints := UsualDecidableSetHints(Model.Tag).
End MODEL_DEFS.

Module Type MODEL := MODEL_PARAMS <+ MODEL_DEFS.


(* NET_MAP MON_DATA PROC  MON QUE PQUED MQUED NET PNET MNET LOCKS RAD RAD_NET SRPC SRPC_NET SOUND COMPL *)

Module Type NET_MAP(Name : UsualDecidableSet).
  Parameter Node : Set.

  Parameter t : Type -> Type.

  (** Accessing process *)
  Parameter get : Name.t -> t Node -> Node.

  (** Updating process *)
  Parameter put : Name.t -> Node -> t Node -> t Node.

  (** Initializing network from function *)
  Parameter init : (Name.t -> Node) -> t Node.

  (** Initialization sets processes as said *)
  Axiom init_get : forall i n, get n (init i) = i n.

  (** Subsequent puts are redundant *)
  Axiom put_put_eq : forall n S0 S1 N,
      put n S1 (put n S0 N) = put n S1 N.

  (** Putting order does not matter *)
  Axiom put_put_neq : forall n n' S0 S1 N,
      n <> n' ->
      put n S1 (put n' S0 N) = put n' S0 (put n S1 N).

  (** Putting overwrites *)
  Axiom get_put_eq : forall n S N,
      get n (put n S N) = S.

  (** Putting does not change others *)
  Axiom get_put_neq : forall n n' S N,
      n <> n' ->
      get n (put n' S N) = get n N.

  (** Putting existing is identity *)
  Axiom put_get_eq : forall n N,
      put n (get n N) N = N.

  (** Networks are defined by the processes *)
  Axiom extensionality : forall N0 N1, (forall n, get n N0 = get n N1) -> N0 = N1.

End NET_MAP.


Module Type PROC_PARAMS.
  Declare Module Model : MODEL.
  Export Model.
End PROC_PARAMS.

Module Type PROC_DEFS(Import ProcParams : PROC_PARAMS).
  Definition PAct : Set := Act Val.
  #[global] Hint Unfold PAct : LTS.
  #[global] Hint Transparent PAct : LTS.


  #[export] Instance gen_Act_PAct : gen_Act PAct Val :=
    {
      send := Send;
      recv := Recv;
      tau := Tau;
      ia a := a = Tau;

      ia_tau := ltac:(intros; split; discriminate);
      ia_disjoint := ltac:(intros; split; discriminate);
      send_recv := ltac:(intros; discriminate);
    }.

  #[export] Hint Unfold gen_Act_PAct : LTS.
  #[export] Hint Transparent gen_Act_PAct : LTS.

  #[export] Hint Extern 10 (ia _) => unfold ia; simpl : LTS.
  #[export] Hint Extern 10 (send _) => unfold send; simpl : LTS.
  #[export] Hint Extern 10 (recv _) => unfold recv; simpl : LTS.


  Lemma ia_PAct_inv : forall (a : PAct), ia a <-> a = Tau.
  Proof. split; intros H; inversion H; auto; constructor. Qed.

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
    Instance Proc_LTS : LTS PAct Proc  :=
    {
      trans := ProcTrans
    }.
  #[export] Hint Unfold Proc_LTS : LTS.
  #[export] Hint Transparent Proc_LTS : LTS.

End PROC_DEFS.

Module Type PROC := PROC_PARAMS <+ PROC_DEFS.


Module Type MON_PARAMS.
  Declare Module Model : MODEL.
  Parameters MonVal MState : Set.
End MON_PARAMS.

Module Type MON_TYPES(MonParams : MON_PARAMS).
  Import MonParams.
  Import Model.

  Inductive Event :=
  | TrSend : NChan -> Val -> Event
  | TrRecv : NChan -> Val -> Event
  | EvRecv : NChan -> MonVal -> Event
  .
  (* #[export] Hint Constructors Event : LTS. *)


  Inductive Mon :=
  | MRecv (state : MState)
  | MSend (to : NChan) (msg : MonVal) (M : Mon)
  .
  (* #[export] Hint Constructors MonAct : LTS. *)


  Inductive MonAct : Set :=
  | MonRecv : Event -> MonAct
  | MonSend : NChan -> MonVal -> MonAct
  | MonTau : MonAct
  .
  (* #[export] Hint Constructors MonAct : LTS. *)

End MON_TYPES.

Module Type MON_PARAM_TYPES := MON_PARAMS <+ MON_TYPES.

Module Type MON_ALG (Params : MON_PARAM_TYPES).
  Import Params.
  Parameter handle : Event -> MState -> Mon.
End MON_ALG.

Module Type MON_DEFS(Params : MON_PARAM_TYPES)(Alg : MON_ALG(Params)).
  Import Params.
  Import Alg.

  Inductive MonTrans : MonAct -> Mon -> Mon -> Prop :=
  | MonTSend : forall {n msg M},
      MonTrans
        (MonSend n msg)
        (MSend n msg M)
        M
  | MonTRecv : forall {ev s handle},
      MonTrans
        (MonRecv ev)
        (MRecv s)
        (handle ev s)
  .
  #[export] Hint Constructors MonTrans : LTS.


  #[export]
    Instance Mon_LTS : LTS MonAct Mon  :=
    {
      trans := MonTrans
    }.

  #[export] Hint Unfold Mon_LTS : LTS.
  #[export] Hint Transparent Mon_LTS : LTS.
End MON_DEFS.

Module Type MON := MON_PARAMS <+ MON_TYPES <+ MON_ALG <+ MON_DEFS.


Module Type QUE(Import Model : MODEL).
  From Coq Require Import Lists.List.
  Import ListNotations.

  Definition Que (E : Set) := list (NChan * E).

  Inductive QAct (E : Set) :=
  | QEnq (n : NChan) (e : E) : QAct E
  | QDeq (n : NChan) (e : E) : QAct E
  .
  #[export] Hint Constructors QAct : LTS.

  Arguments QEnq [E].
  Arguments QDeq [E].


  Inductive QTrans {E : Set} : QAct E -> Que E -> Que E -> Prop :=
  | QPush (n : NChan) (e : E) (Q : Que E)
    : QTrans (QEnq n e) Q (Q ++ [(n, e)])
  | QPop (n : NChan) (e : E) (Q : Que E)
    : QTrans (QDeq n e) ((n, e)::Q) Q
  | QSeek (n : NChan) (e : E) {n' : NChan} {e' : E}
      (Q0 Q1 : Que E)
      (HSkip : n <> n')
      (HSeek : QTrans (QDeq n e) Q0 Q1)
    : QTrans (QDeq n e) ((n', e')::Q0) ((n', e')::Q1)
  .
  #[export] Hint Constructors QTrans : LTS.


  #[export] Instance Que_LTS {E : Set} : LTS (QAct E) (Que E) :=
    {
      trans := QTrans
    }.

  #[export] Hint Unfold Que_LTS : LTS.
  #[export] Hint Transparent Que_LTS : LTS.


  Notation Enq n v Q0 Q1 := (QTrans (QEnq n v) Q0 Q1).
  Notation Deq n v Q0 Q1 := (QTrans (QDeq n v) Q0 Q1).
End QUE.


Module Type PQUED_PARAMS.
  Declare Module Proc : PROC.
  Declare Module Que : QUE(Proc.Model).

  Export Proc Que.
End PQUED_PARAMS.

Module Type PQUED_DEFS(Import PQuedParams : PQUED_PARAMS).
  From Coq Require Import Lists.List.
  Import ListNotations.

  Inductive PQued := pq : Que Val -> Proc -> Que Val -> PQued.
  #[export] Hint Constructors PQued : LTS.

  Inductive PTrans : PAct -> PQued -> PQued -> Prop :=
  | PTRecv [n v I0 I1 P O]
      (HEnq : Enq n v I0 I1)
    : PTrans (recv n v) (pq I0 P O) (pq I1 P O)

  | PTPick [n v I0 I1 P0 P1 O]
      (HDeq : Deq n v I0 I1)
    : (P0 =(recv n v)=> P1) ->
      PTrans tau (pq I0 P0 O) (pq I1 P1 O)

  | PTSend [n v I P0 P1 O0 O1]
      (HEnq : Enq n v O0 O1)
    : (P0 =(send n v)=> P1) ->
      PTrans tau (pq I P0 O0) (pq I P1 O1)

  | PTPush {n v I P O}
    : PTrans (send n v) (pq I P ((n, v)::O)) (pq I P O)

  | PTTau {I P0 P1 O}
    : (P0 =(tau)=> P1) ->
      PTrans tau (pq I P0 O) (pq I P1 O)
  .

  #[export] Hint Constructors PTrans : LTS.


  #[export]
    Instance PQued_LTS : LTS PAct PQued  :=
    {
      trans := PTrans
    }.

  #[export] Hint Unfold PQued_LTS : LTS.
  #[export] Hint Transparent PQued_LTS : LTS.
End PQUED_DEFS.

Module Type PQUED := PQUED_PARAMS <+ PQUED_DEFS.


Module Type MQUED_PARAMS.
  Declare Module PQued : PQUED.
  Declare Module Mon : MON with Module Model := PQued.Proc.Model.

  Export Mon PQued.
End MQUED_PARAMS.

Module Type MQUED_DEFS(Import MQuedParams : MQUED_PARAMS).
  From Coq Require Import Lists.List.
  Import ListNotations.


  Inductive MVal :=
  | MValM : MonVal -> MVal
  | MValP : Val -> MVal
  .
  #[export] Hint Constructors MVal : LTS.


  Inductive MAct :=
  | MActP : PAct -> MAct
  | MActT : PAct -> MAct
  | MActM : Act MonVal -> MAct
  .
  #[export] Hint Constructors MAct : LTS.

  #[global] Coercion MValM : MonVal >-> MVal.
  #[global] Coercion MValP : Val >-> MVal.


  #[export]
    Instance gen_Act_MAct : gen_Act MAct MVal :=
    {
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

      tau := MActM Tau;

      ia a :=
        match a with
        | MActM Tau | MActP _ => True
        | _ => False
        end;

      ia_tau := ltac:(attac);
      send_recv := ltac:(intros; destruct v; auto; discriminate);
      ia_disjoint := ltac:(intros; split; destruct v; auto; discriminate);
    }.

  #[export] Hint Unfold gen_Act_MAct : LTS.
  #[export] Hint Transparent gen_Act_MAct : LTS.


  Inductive MQued := mq : list Event -> Mon -> PQued -> MQued.


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
    Instance MQued_LTS : LTS MAct MQued  :=
    {
      trans := MTrans
    }.

  #[export] Hint Unfold MQued_LTS : LTS.
  #[export] Hint Transparent MQued_LTS : LTS.
End MQUED_DEFS.

Module Type MQUED := MQUED_PARAMS <+ MQUED_DEFS.


Module Type NET_PARAMS.
  Parameter Node : Set.
  Parameter Label : Set.
  Parameter Msg : Set.

  Declare Module Model : MODEL.
  Declare Module NetMap : NET_MAP(Model.Name) with Definition Node := Node.


  Parameter Label_gen_Act : Model.gen_Act Label Msg.
  Existing Instance Label_gen_Act.

  Parameter Label_Node_LTS : LTS Label Node.
  Existing Instance Label_Node_LTS.
End NET_PARAMS.

Module Type NET_DEFS(NetParams : NET_PARAMS).
  Import NetParams.
  Import Model.
  Import NetMap.

  Definition Net := NetMap.t Node.

  (** Network can perform two types of actions:
        - Internal action of some process
        - Communication between two (or one!) processes
   *)
  Inductive NAct :=
  | NTau : Name -> Label -> NAct
  | NComm : Name -> Name -> Tag -> Msg -> NAct
  .

  Hint Constructors NAct : LTS.


  (** Auxilary type of transition used to observe that a process has progressed over some
   *process* action. This does not have to be valid transition of the entire network --- it is only
    to picture how the network changes when a process is given a chance. This rule acts solely as a
    helper for the main [NTrans] transition type. *)
  Inductive NVTrans : Name -> Label -> Net -> Net -> Prop :=
  | NT_Vis [n : Name] [a : Label] [S : Node] [N : Net] :
    (get n N =(a)=> S) ->
    NVTrans n a N (put n S N)
  .
  Notation "N0 ~( n @ a )~> N1" := (NVTrans n a N0 N1) (at level 70): type_scope.

  Hint Constructors NVTrans : LTS.

    (** Network transition. It has two rules to match [NAct]:
        - [NT_Tau] allows processes to perform internal actions.
        - [NT_Comm] describes communication between processes. This is described in two steps:

            1. The sending process performs the send
            2. The receiving process receives the message

         Note that from the perspective of transition, this division is invisible, thus the
         communication is atomic. The receiving step is later proven to be always available.
     *)
    Inductive NTrans : NAct -> Net -> Net -> Prop :=
    | NT_Tau [n : Name] [a : Label] [N0 N1 : Net] :
      ia a ->
      N0 ~(n @ a)~> N1 ->
      NTrans (NTau n a) N0 N1

    | NT_Comm [n n' : Name] [t : Tag] [v : Msg] [N0 N0' N1] :
      N0 ~(n @ send (n', t) v)~> N0' ->
      N0' ~(n' @ recv (n, t) v)~> N1 ->
      NTrans (NComm n n' t v) N0 N1
    .

    Hint Constructors NTrans : LTS.


    #[export]
      Instance Net_LTS : LTS NAct Net :=
      {
        trans := NTrans
      }.
    Hint Unfold Net_LTS : LTS.
    #[export] Hint Transparent Net_LTS : LTS.

End NET_DEFS.

Module Type NET := NET_PARAMS <+ NET_DEFS.


Module Type PNET_PARAMS(PQued : PQUED) :=
  NET_PARAMS
  with Definition Node := PQued.PQued
  with Definition Label := PQued.Proc.PAct
  with Definition Msg := PQued.Proc.Model.Val
  with Definition Label_Node_LTS := PQued.PQued_LTS.

Module Type MNET_PARAMS(MQued : MQUED) :=
  NET_PARAMS
  with Definition Node := MQued.MQued
  with Definition Label := MQued.MAct
  with Definition Msg := MQued.MVal
  with Definition Label_Node_LTS := MQued.MQued_LTS.


Module Type TRANSP_PARAMS(PQued : PQUED)(Mon : MON).
  Declare Module PNet : PNET(PQued).
  Declare Module MNet : MNET with 

Module Type TRANSP(PNet : PNET)(MNet : MNET).















Module Type PROC := PROC_PARAMS <+ PROC_DEFS.



Module Type QUE_DEFS(Import Model : MODEL).
  Import Model.

  Inductive Q := Q_val.
  #[export] Hint Constructors Q.
End QUE_DEFS.

Module Type QUE := MODEL <+ QUE_DEFS.


Module Type PROC_DEFS(Import Que : QUE).
  Inductive P := P_val (a : Q).
  Inductive PA := PA_send | PA_recv | PA_tau.
  Inductive PT : PA -> P -> P -> Prop := PT_ : forall Q, PT PA_tau (P_val Q) (P_val Q).

  #[export] Instance gen_Act_PAct : gen_Act PA :=
    {
      Payload := Val;
      send := fun _ _ => PA_send;
      recv := fun _ _ => PA_recv;
      ia a := a = PA_tau;

      ia_disjoint := ltac:(intros; split; discriminate);
      send_recv := ltac:(intros; discriminate);
    }.

  #[export] Instance PT_LTS : LTS PA P :=
    {
      trans := PT
    }.

  #[export] Hint Constructors P.
End PROC_DEFS.

Module Type PROC := QUE <+ PROC_DEFS.


Module Type MON_PARAMS.
  Parameter Msg : Set.
  Parameter MState : Set.
End MON_PARAMS.

Module Type MON_DEFS(Proc : PROC)(Mon : MON_PARAMS).
  Inductive M := M_val (p : Proc.P).
  Inductive MA :=  MA_send | MA_recv | MA_tau.
  Inductive MT : MA -> M -> M -> Prop := MT_ : forall P, MT MA_tau (M_val P) (M_val P).

  #[export] Instance gen_Act_MAct : Proc.gen_Act MA :=
    {
      Payload := Proc.Val;
      send := fun _ _ => MA_send;
      recv := fun _ _ => MA_recv;
      ia a := a = MA_tau;

      ia_disjoint := ltac:(intros; split; discriminate);
      send_recv := ltac:(intros; discriminate);
    }.


  #[export] Instance MT_LTS : LTS MA M :=
    {
      trans := MT
    }.


  #[export] Hint Constructors M.
End MON_DEFS.

Module Type MON := PROC <+ MON_PARAMS <+ MON_DEFS.


Module Type NET_STRUCT(Name : UsualDecidableSet).
  Parameter t : Type -> Type.

  Section Single.
    Context [Node : Set].

    Parameter get : Name.t -> t Node -> Node.
  End Single.
End NET_STRUCT.

Require Import DlStalk.LTS.

Module Type NET_PARAMS.
  Declare Module Model : MODEL.
  Declare Module NetStruct : NET_STRUCT(Model.Name).

  Parameter Node : Set.
  Parameter Label : Set.

  #[local] Parameter Label_gen_Act : Model.gen_Act Label.
  Existing Instance Label_gen_Act.

  #[local] Parameter Label_Node_LTS : LTS Label Node.
  Existing Instance Label_Node_LTS.
End NET_PARAMS.


Module Type NET_DEFS(Import Net : NET_PARAMS).
  Definition t := NetStruct.t Node.

  Inductive NA := NA_ (a : Label).

  Inductive NT : NA -> t -> t -> Prop :=
    NT_ [a : Label] [N0 N1 : t] [n : Model.Name] : (NetStruct.get n N0 =(a)=> NetStruct.get n N1) -> NT (NA_ a) N0 N1.

  #[export] Instance MT_LTS : LTS NA (NetStruct.t Node) :=
    {
      trans := NT
    }.
End NET_DEFS.

Module Type TEST(Model : MODEL).
  Module Que := Empty <+ QUE.
  Module Proc := Empty <+ PROC_DEFS(Que).

  Module Type PNET_PARAMS(Model : MODEL)(NetStruct : NET_STRUCT(Model.Name)) :=
    NET_PARAMS with Definition Node := Proc.P.



  Module Mon : MON with Definition Msg := nat.
