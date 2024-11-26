From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Std.

From Ltac2 Require Fresh.
From Ltac2 Require Import Control.
From Ltac2 Require Import Message.
From Ltac2 Require Import Std.
From Ltac2 Require Import Printf.
From Ltac2 Require Import Notations.

Close Scope nat.

From Coq Require Import Lists.List.
Import ListNotations.


Require Import DlStalk.LTS.
Require Import DlStalk.Tactics.
Require Import DlStalk.Model.
Require Import DlStalk.ModelData.
Require Import DlStalk.Que.


Module Type NET(Name : UsualDecidableSet).

  Parameter t : Type -> Type.

  Section Node.
    Context {Node : Type}.

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
  End Node.

  #[export] Hint Resolve
    put_put_eq
    put_put_neq
    get_put_eq
    get_put_neq
    put_get_eq
    : LTS.


  Section Node2.
    Context {Node Node' : Type}.

    (** Application of a function on every process *)
    Parameter map : (Name.t -> Node -> Node') -> t Node -> t Node'.

    (** Map is homomorphic over get *)
    Axiom get_map : forall (f : Name.t -> Node -> Node') n (N : t Node),
        get n (map f N) = f n (get n N).

    (** Map is homomorphic over put *)
    Axiom put_map : forall (f : Name.t -> Node -> Node') n (N : t Node) (S : Node),
        map f (put n S N) = put n (f n S) (map f N).
  End Node2.

  #[export] Hint Resolve
    get_map
    put_map
    : LTS.

End NET.


Module Net(Import MD : MODEL_DATA)(NetMod : NET(MD.NAME)).

  Module Import Model := Model(MD).
  Export Model.


  (** Coercion to function *)
  Definition NetGet (A : Set) : NetMod.t A -> Name -> A := fun MN n => @NetMod.get A n MN.
  #[export] Hint Transparent NetGet : LTS typeclass_instances.
  #[global] Coercion NetGet : NetMod.t >-> Funclass.


  Lemma put_put_eq_inv [T] (N : NetMod.t T) n S S' :
    (NetMod.put n S (NetMod.put n S' N)) = NetMod.put n S N.
  Proof. apply NetMod.put_put_eq. Qed.

  Lemma get_put_eq_inv [T] (N : NetMod.t T) n S :
    (NetMod.get n (NetMod.put n S N)) = S.
  Proof. apply NetMod.get_put_eq. Qed.

  Lemma get_put_neq_inv [T] (N : NetMod.t T) n n' S' :
    n <> n' ->
    (NetMod.get n (NetMod.put n' S' N)) = NetMod.get n N.
  Proof. apply NetMod.get_put_neq. Qed.

  Lemma put_get_eq_inv [T] (N : NetMod.t T) n :
    (NetMod.put n (NetMod.get n N) N) = N.
  Proof. apply NetMod.put_get_eq. Qed.

  Lemma get_map_inv [T A] (N : NetMod.t T) (f : Name -> T -> A) n :
    (NetMod.get n (NetMod.map f N)) = f n (NetMod.get n N).
  Proof. apply NetMod.get_map. Qed.

  Lemma put_map_inv [T A] (N : NetMod.t T) (f : Name -> T -> A) n S :
    (NetMod.map f (NetMod.put n S N)) = NetMod.put n (f n S) (NetMod.map f N).
  Proof. apply NetMod.put_map. Qed.

  Lemma put_inj [T] n (N : NetMod.t T) S S' : NetMod.put n S N = NetMod.put n S' N <-> S = S'.
  Proof. split; eattac. erewrite <- NetMod.get_put_eq. rewrite <- H. rewrite NetMod.get_put_eq. auto. Qed.

  #[export] Hint Rewrite -> @put_put_eq_inv @get_put_eq_inv @get_put_neq_inv @put_get_eq_inv @get_map_inv @put_map_inv @put_inj using spank : LTS LTS_concl.


  Section General.
    Context [Node Act : Set].
    Context {gen_Act_Act : gen_Act Act}.
    Context {LTS_node : LTS Act Node}.

    Notation Net := (NetMod.t Node).


    (** Network can perform two types of actions:
        - Internal action of some process
        - Communication between two (or one!) processes
     *)
    Inductive NAct :=
    | NTau : Name -> Act -> NAct
    | NComm : Name -> Name -> Tag -> Payload -> NAct
    .

    Hint Constructors NAct : LTS.


    (** Auxilary type of transition used to observe that a process has progressed over some
     *process* action. This does not have to be valid transition of the entire network --- it is only
    to picture how the network changes when a process is given a chance. This rule acts solely as a
    helper for the main [NTrans] transition type. *)
    Inductive NVTrans : Name -> Act -> Net -> Net -> Prop :=
    | NT_Vis [n : Name] [a : Act] [S : Node] [N : Net] :
      (NetMod.get n N =(a)=> S) ->
      NVTrans n a N (NetMod.put n S N)
    .
    Notation "N0 ~( n @ a )~> N1" := (NVTrans n a N0 N1) (at level 70): type_scope.

    Hint Constructors NVTrans : LTS.


    Lemma NVTrans_inv n a N0 N1 :
      (N0 ~(n @ a)~> N1) <-> exists S, (NetMod.get n N0 =(a)=> S) /\ N1 = NetMod.put n S N0.

    Proof.
      split; intros.
      kill H; eattac. hsimpl in *. eattac.
    Qed.

    Hint Rewrite -> @NVTrans_inv using spank : LTS.


    (** Network transition. It has two rules to match [NAct]:
        - [NT_Tau] allows processes to perform internal actions.
        - [NT_Comm] describes communication between processes. This is described in two steps:

            1. The sending process performs the send
            2. The receiving process receives the message

         Note that from the perspective of transition, this division is invisible, thus the
         communication is atomic. The receiving step is later proven to be always available.
     *)
    Inductive NTrans : NAct -> Net -> Net -> Prop :=
    | NT_Tau [n : Name] [a : Act] [N0 N1 : Net] :
      ia a ->
      N0 ~(n @ a)~> N1 ->
      NTrans (NTau n a) N0 N1

    | NT_Comm [n n' : Name] [t : Tag] [v : Payload] [N0 N0' N1] :
      N0 ~(n @ send (n', t) v)~> N0' ->
      N0' ~(n' @ recv (n, t) v)~> N1 ->
      NTrans (NComm n n' t v) N0 N1
    .

    Hint Constructors NTrans : LTS.


    #[export]
      Instance trans_net : LTS NAct Net :=
      {
        trans := NTrans
      }.
    Hint Unfold trans_net : LTS.
    #[export] Hint Transparent trans_net : LTS.


    Lemma NTrans_Comm_neq_inv n n' t v N0 N1 :
      n <> n' ->
      (N0 =(NComm n n' t v)=> N1) <->
        exists S S', (NetMod.get n N0 =(send (n', t) v)=> S) /\ (NetMod.get n' N0 =(recv (n, t) v)=> S')
                     /\ N1 = NetMod.put n' S' (NetMod.put n S N0).

    Proof.
      split; intros. kill H0; kill H1; kill H2. eattac.
      hsimpl in *. econstructor. eattac. eattac.
    Qed.

    Lemma NTrans_Comm_eq_inv n t v N0 N1 :
      (N0 =(NComm n n t v)=> N1) <->
        exists S S', (NetMod.get n N0 =(send (n, t) v)=> S) /\ (S =(recv (n, t) v)=> S')
                     /\ N1 = NetMod.put n S' N0.

    Proof.
      split; intros. kill H; kill H0; kill H1; eattac.
      hsimpl in *. econstructor. eattac.
      replace (NetMod.put n S' N0) with (NetMod.put n S' (NetMod.put n &S N0)) by attac.
      eattac.
    Qed.

    Lemma NTrans_Tau_inv n a N0 N1 :
      (N0 =(NTau n a)=> N1) <-> exists S, (NetMod.get n N0 =(a)=> S) /\ N1 = NetMod.put n S N0 /\ ia a.
    Proof.
      split; intros. kill H. kill H1. eattac.
      hsimpl in *; constructor; eattac.
    Qed.

    Hint Rewrite -> NTrans_Comm_eq_inv NTrans_Comm_neq_inv NTrans_Tau_inv using spank : LTS.


    (** If process wants a tau, network allows it. *)
    Lemma ia_available : forall [n : Name] [a S] [N0 : Net],
        ia a ->
        (NetMod.get n N0 =(a)=> S) ->
        exists N1, NVTrans n a N0 N1
                   /\ S = NetMod.get n N1.

    Proof.
      intros.
      apply NT_Vis in H0.
      exists (NetMod.put n &S N0); eattac.
    Qed.


    (** The path a node took within the network, given the network path. *)
    Inductive Path_of (n : Name) : list NAct -> list Act -> Prop :=
    | PO_nil : Path_of _ [] []

    | PO_tau [a] [npath ppath] :
      Path_of _ npath ppath ->
      Path_of _ (NTau n a :: npath) (a :: ppath)

    | PO_comm_send [n' t v] [npath ppath] :
      n' <> n ->
      Path_of _ npath ppath ->
      Path_of _ (NComm n n' t v :: npath) (send (n', t) v :: ppath)

    | PO_comm_recv [n' t v] [npath ppath] :
      n' <> n ->
      Path_of _ npath ppath ->
      Path_of _ (NComm n' n t v :: npath) (recv (n', t) v :: ppath)

    | PO_comm_self [t v] [npath ppath] :
      Path_of _ npath ppath ->
      Path_of _ (NComm n n t v :: npath) (send (n, t) v :: recv (n, t) v :: ppath)

    | PO_skip_tau [n' a] [npath ppath] :
      n' <> n ->
      Path_of _ npath ppath ->
      Path_of _ (NTau n' a :: npath) ppath

    | PO_skip_comm [n' n'' t] [v] [npath ppath] :
      n <> n' ->
      n <> n'' ->
      Path_of _ npath ppath ->
      Path_of _ (NComm n' n'' t v :: npath) ppath
    .

    Hint Constructors Path_of : LTS.

    Arguments PO_tau [_ _ _ _] HPo.
    Arguments PO_comm_send [_ _ _ _ _ _] _ HPo.
    Arguments PO_comm_recv [_ _ _ _ _ _] _ HPo.
    Arguments PO_comm_self [_ _ _ _ _] HPo.
    Arguments PO_skip_tau [_ _ _ _ _] _ HPo.
    Arguments PO_skip_comm [_ _ _ _ _ _ _] _ _ HPo.


    Lemma Path_of_nil_inv n ppath : Path_of n [] ppath <-> ppath = [].
    Proof. intros; eattac. Qed.

    Lemma Path_of_tau_inv n npath ppath a : Path_of n (NTau n a :: npath) ppath <-> exists ppath', (HPo |: Path_of n npath ppath') /\ ppath = a :: ppath'.
    Proof. eattac. kill H. eattac. Qed.

    Lemma Path_of_tau_skip_inv n n' npath ppath a : n <> n' -> Path_of n (NTau n' a :: npath) ppath <-> (HPo |: Path_of n npath ppath).
    Proof. eattac. Qed.

    Lemma Path_of_comm_send_inv n m t v npath ppath : n <> m -> Path_of n (NComm n m t v :: npath) ppath <-> exists ppath', (HPo |: Path_of n npath ppath') /\ ppath = (send (m, t) v :: ppath').
    Proof. eattac. kill H0. eattac. Qed.

    Lemma Path_of_comm_recv_inv n m t v npath ppath : n <> m -> Path_of n (NComm m n t v :: npath) ppath <-> exists ppath', (HPo |: Path_of n npath ppath') /\ ppath = (recv (m, t) v :: ppath').
    Proof. eattac. kill H0. eattac. Qed.

    Lemma Path_of_comm_skip_inv n m0 m1 t v npath ppath : n <> m0 -> n <> m1 -> Path_of n (NComm m0 m1 t v :: npath) ppath <-> (HPo |: Path_of n npath ppath).
    Proof. eattac. Qed.

    Lemma Path_of_comm_self_inv n t v npath ppath : Path_of n (NComm n n t v :: npath) ppath <-> exists ppath', (HPo |: Path_of n npath ppath') /\ ppath = (send (n, t) v :: recv (n, t) v :: ppath').
    Proof. eattac. kill H. eattac. Qed.

    Hint Rewrite -> Path_of_nil_inv Path_of_tau_inv Path_of_tau_skip_inv Path_of_comm_send_inv Path_of_comm_recv_inv Path_of_comm_skip_inv Path_of_comm_self_inv using spank : LTS LTS_concl.


    (** For any network path, you can get the path of any node *)
    Lemma path_of_exists : forall (n : Name) npath,
      exists ppath, Path_of n npath ppath.

    Proof using Type.
      intros n npath.
      induction npath.
      1: eattac.

      kill IHnpath.
      destruct a; smash_eq n n0; eattac.
      all: smash_eq n n1; eattac.
    Qed.

    Hint Resolve path_of_exists : LTS.


    (** The node within the network indeed moves as declared *)
    Lemma path_of_ptrans : forall [n : Name] [npath ppath] [N0 N1],
        Path_of n npath ppath ->
        (N0 =[npath]=> N1) ->
        (NetMod.get n N0 =[ppath]=> NetMod.get n N1).

    Proof with (eauto with LTS).
      induction npath; intros ppath N0 N1 HPo NT.
      1: eattac.

      kill HPo; hsimpl in *.

      all: ltac1:(eassert (Path_of n npath _) as HPo by eauto).
      all: try (eapply IHnpath in HPo > [|progress eauto ]); eattac.

      smash_eq n' n''; hsimpl in *; eattac. (* todo why hsimpl needed? *)
    Qed.


    (** Empty network path does not involve any processes *)
    Lemma path_of_nil : forall (n : Name) [path],
        Path_of n [] path -> path = [].

    Proof. eattac. Qed.


    (** If network does not move, so each process. *)
    Lemma path_of_nil_stay : forall [n : Name] [npath] [N0 N1],
        Path_of n npath [] ->
        (N0 =[npath]=> N1) ->
        NetMod.get n N0 = NetMod.get n N1.

    Proof.
      intros.
      apply (path_of_ptrans H) in H0.
      kill H0.
    Qed.


    (** Splitted network path can be used to split a process path *)
    Lemma path_of_split : forall [n : Name] [npath0 npath1 path],
        Path_of n (npath0 ++ npath1) path ->
        exists path0 path1,
          path = path0 ++ path1          /\ Path_of n npath0 path0
          /\ Path_of n npath1 path1.

    Proof with (eauto with LTS).
      induction npath0; intros until path; intros HPo.

      simpl in *. exists [], path...

      simpl in *.
      kill HPo; hsimpl in *.
      all: ltac1:(eassert (Path_of n _ _) as HPo by eauto).
      all: apply IHnpath0 in HPo as (path0 & path1 & HEq & HPo0 & HPo1); subst.
      all: try (solve [eexists _, path1; eattac]).
    Qed.


    (** Splitted network path can be used to split a process path *)
    Lemma path_of_split1 : forall (n : Name) [na npath path],
        Path_of n (na :: npath) path ->
        exists path0 path1,
          path = path0 ++ path1
          /\ Path_of n [na] path0
          /\ Path_of n npath path1.

    Proof.
      intros.
      assert (na :: npath = [na] ++ npath). auto.
      rewrite H0 in H.
      apply (path_of_split H).
    Qed.


    (** Path extraction is homomorphic (cons version) *)
    Lemma path_of_seq1 : forall (n : Name) [na npath1 path0 path1],
        Path_of n [na] path0 ->
        Path_of n npath1 path1 ->
        Path_of n (na :: npath1) (path0 ++ path1).

    Proof with (attac).
      intros.

      kill H; eattac.
    Qed.


    (** Path extraction is homomorphic *)
    Lemma path_of_seq : forall (n : Name) [npath0 npath1 path0 path1],
        Path_of n npath0 path0 ->
        Path_of n npath1 path1 ->
        Path_of n (npath0 ++ npath1) (path0 ++ path1).

    Proof.
      induction npath0; intros until path1; intros HPo0 HPo1; simpl in *.
      apply path_of_nil in HPo0. subst. simpl. apply HPo1.

      apply path_of_split1 in HPo0 as (path00 & path01 & HEq & HPo00 & HPo01); subst.
      rewrite <- app_assoc.
      specialize (IHnpath0 _ _ _ HPo01 HPo1).
      apply path_of_seq1; auto.
    Qed.


    (** If a node can perform a sequence of internal actions, then the network can too. *)
    Lemma ia_path_NVTrans : forall
        [n : Name] [path : list Act] [N : Net] [S : Node],
        Forall ia path ->
        (NetMod.get n N =[path]=> S) ->
        exists npath,
          (N =[npath]=> NetMod.put n S N)
          /\ Path_of n npath path.

    Proof.
      induction path; intros.
      1: eattac.

      hsimpl in *.
      specialize (IHpath (NetMod.put n N1 N) &S).
      hsimpl in *.
      specialize IHpath as (npath & NT1 & HPO); eauto.
      eattac.
    Qed.


    (** NVTrans does not change other processes *)
    Lemma NV_stay [n n' a N0 N1] :
      NVTrans n a N0 N1 ->
      n <> n' ->
      NetMod.get n' N0 = NetMod.get n' N1.

    Proof. eattac. Qed.


    (** Internal actions preserve all unrelated members *)
    Lemma trans_preserve_ia_neq [n n'] :
      n <> n' ->
      trans_preserve (NetMod.get n) (fun na => exists a, na = NTau n' a).

    Proof.
      unfold trans_preserve.
      eattac.
    Qed.

    Hint Resolve trans_preserve_ia_neq : inv LTS.


    (** Processes participating in a network action. *)
    Definition act_particip (a : NAct) : list Name :=
      match a with
      | NTau n _ => [n]
      | NComm n0 n1 _ _ => [n0; n1]
      end.


    (** Processes participating in a network path. *)
    Fixpoint path_particip (path : list NAct) : list Name :=
      match path with
      | [] => []
      | a :: path0 => act_particip a ++ path_particip path0
      end.


    (** Only participants are modified after action. *)
    Theorem act_particip_stay : forall [n : Name] [a : NAct] [N0 N1 : Net],
        not (In n (act_particip a)) ->
        (N0 =(a)=> N1) ->
        NetMod.get n N0 = NetMod.get n N1.

    Proof.
      intros.
      kill H0.
      - smash_eq n n0; attac.
      - smash_eq n n0; attac.
    Qed.


    (** Only participants are modified after path. *)
    Theorem path_particip_stay : forall [n : Name] [path : list NAct] [N0 N1 : Net],
        not (In n (path_particip path)) ->
        (N0 =[path]=> N1) ->
        NetMod.get n N0 = NetMod.get n N1.

    Proof.
      induction path; intros.
      1: eattac.

      hsimpl in *.

      transitivity '(NetMod.get n N2).
      2: eattac.
      eapply act_particip_stay; eattac.
    Qed.


    (** A bit complicated, yet powerful statement. In human words:

        We start with a network with a global property [NP]. We want to move this network to such a
        state, that not only [NP] is retained, but also every process has a property [P].
        Thankfully, only a finite number of processes might not have [P] (members of the [chans]
        list).

        The theorem says that in order to find such a transition, it is sufficient to be able to
        make [P] hold for an arbitrarily selected process, as long as we do not break [P] for
        processes which initially had it and preserve [NP] during that move. This is because we can
        iteratively apply this operation on every process that did not have [P] initially. Since the
        number of processes to fix is finite, we will eventually reach a state where there are no
        outliers.

        --------------------------------------------------------------------------------------------
        Proc: P0 (F) =======> P0' (T)  ->  ->  P0'' (T)          P0'' (T)
        Proc: P1 (F) ->       P1' (F) =======> P1'' (T)          P1'' (T)
        Proc: P2 (F)    ->    P2' (F)          P2'  (F) =======> P2'' (T)
        --------------------------------------------------------------------------------------------
        Net:  N     ========> N'      =======> N''      =======> N''' (All ok)
        --------------------------------------------------------------------------------------------
     *)
    Lemma net_induction :
      forall [NP : Net -> Prop] [P : Node -> Prop] [chans : list Name] ,
        (forall n N0,
            NP N0 ->
            exists npath N1,
              (N0 =[ npath ]=> N1)
              /\ (forall m, (n = m \/ P (NetMod.get m N0)) -> P (NetMod.get m N1))
              /\ NP N1
        ) ->
        (forall N0,
            (forall n, not (In n chans) -> P (NetMod.get n N0)) ->
            NP N0 ->
            exists npath N1,
              (N0 =[ npath ]=> N1)
              /\ (forall n, P (NetMod.get n N1))
              /\ NP N1
        ).

      intros NP P chans HLoc0.
      induction chans; intros N0 HStay0 HGlob0.
      exists []. exists N0. repeat split; auto. constructor.

      rename a into n.
      specialize (HLoc0 n N0 HGlob0) as (npath0 & N0' & TN0 & HLoc0' & HGlob0').

      assert (forall n : Name, ~ In n chans -> P (NetMod.get n N0')) as Ind_in.
      intros.

      destruct (NAME.eq_dec n0 n); subst.
      apply HLoc0'. left; auto.

      apply HLoc0'. right.

      apply HStay0.
      unfold not.
      intros.
      kill H0.

      specialize (IHchans N0' Ind_in HGlob0') as (npath1 & N1 & TN1 & HLoc1 & HG1).

      exists (npath0 ++ npath1), N1.
      repeat split; auto.
      apply (path_seq TN0 TN1).
    Qed.


    (** Simplified variant of [net_induction] which disregards the global property *)
    Lemma net_induction' :
      forall [P : Node -> Prop] [chans : list Name],
        (forall n N0,
          exists npath N1,
            (N0 =[ npath ]=> N1)
            /\ (forall m, (n = m \/ P (NetMod.get m N0)) -> P (NetMod.get m N1))
        ) ->
        (forall N0,
            (forall n, not (In n chans) -> P (NetMod.get n N0)) ->
            exists npath N1,
              (N0 =[ npath ]=> N1)
              /\ (forall n, P (NetMod.get n N1))
        ).

    Proof.
      intros P chans HLoc N0 HStay.

      assert
        (forall n N0,
            ((fun (_ : Net) => True) N0) ->
            exists npath N1,
              (N0 =[ npath ]=> N1)
              /\ (forall m, (n = m \/ P (NetMod.get m N0)) -> P (NetMod.get m N1))
              /\ ((fun (_ : Net) => True) N1)
        ) as HLoc'.
      intros n N0' _.
      specialize (HLoc n N0') as (npath' & N1' & T' & F').
      exists npath', N1'. repeat split; auto.
      clear HLoc.

      specialize (net_induction HLoc' N0 HStay)
        as (npath & N1 & T & F & _G); auto.
      clear HLoc'.

      exists npath, N1.
      repeat split; auto.
    Qed.


    Lemma conscious_replace : forall {Node1 Node2} (n : Name) (f0 f1 : Name -> Node1 -> Node2) (N0 : NetMod.t Node1),
        NetMod.map (fun n' S => if NAME.eqb n n' then f1 n S else f0 n' S) N0
        = NetMod.put n (f1 n (NetMod.get n N0)) (NetMod.map f0 N0).
    Proof.
      intros.
      apply NetMod.extensionality.
      intros.

      rewrite NetMod.get_map.
      smash_eq n0 n; attac.
    Qed.
  End General.

  #[export] Hint Constructors NAct NVTrans NTrans Path_of : LTS.
  #[export] Hint Resolve path_of_exists : LTS.
  #[export] Hint Immediate act_particip_stay path_particip_stay : LTS.
  #[export] Hint Unfold trans_net : LTS.

  #[export] Hint Resolve trans_preserve_ia_neq : inv LTS.

  #[export] Hint Rewrite -> @NVTrans_inv using spank : LTS.
  #[export] Hint Rewrite -> @NTrans_Comm_eq_inv @NTrans_Comm_neq_inv @NTrans_Tau_inv using spank : LTS.
  #[export] Hint Rewrite -> @Path_of_nil_inv @Path_of_tau_inv @Path_of_tau_skip_inv @Path_of_comm_send_inv @Path_of_comm_recv_inv @Path_of_comm_skip_inv @Path_of_comm_self_inv using spank : LTS LTS_concl.

  #[global] Notation "N0 ~( n @ a )~> N1" := (NVTrans n a N0 N1) (at level 70): type_scope.

  Ltac2 hsimpl_net_ (h : ident option) :=
    repeat (Control.enter (fun _ =>
                             match!goal with
                               [h' : context [NetMod.get ?n0 (NetMod.put ?n1 _ _)] |- _] =>
                                 if Ident.equal h' (match h with Some h => h | None => h' end) then
                                   if Constr.equal n0 n1 then fail
                                   else destruct (NAME.eq_dec $n1 $n0); hsimpl in *
                                 else fail
                             end)).

  Ltac2 Notation "hsimpl_net" h(opt(ident)) := hsimpl_net_ h.
End Net.

