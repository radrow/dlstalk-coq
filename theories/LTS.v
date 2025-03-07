From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Std.

From Ltac2 Require Fresh.
From Ltac2 Require Import Control.
From Ltac2 Require Import Message.
From Ltac2 Require Import Std.
From Ltac2 Require Import Printf.
Import Ltac2.Notations.

From Coq Require Import Lists.List.
Import ListNotations.


Require Import DlStalk.Tactics.


Declare Scope lts_scope.
Delimit Scope lts_scope with lts.

Open Scope lts_scope.


Class LTS (Label Node : Type) :=
  trans : Label -> Node -> Node -> Prop.

Notation "P0 =( p )=> P1" := (trans p P0 P1) (at level 90) : lts_scope.


#[export] Hint Transparent trans : LTS.

(* This trick provides unfolding for the auto solver, but prevents destroying notations with
autounfold *)
#[export] Hint Extern 20 (trans _ _ _) => unfold trans : LTS.


Inductive ptrans [Label Node : Type] [lts : LTS Label Node] :
  list Label -> Node -> Node -> Prop :=
| STnil : forall N, ptrans [] N N
| STcons : forall [a path N0 N1 N']
             (T0 : N0 =(a)=> N1)
             (T1 : ptrans path N1 N'),
    ptrans (a::path) N0 N'
.

Notation "P0  =[  p  ]=>  P1" :=
  (ptrans p P0 P1)
    (at level 90).

Notation "P0 =[]=> P1" :=
  (ptrans [] P0 P1)
    (at level 90) .

Notation "P  ={ a }=>  Q " :=
  (ptrans (cons a nil) P Q)
    (at level 90) : type_scope.
Notation "P ={ a ,  b ,  .. ,  c }=> Q " :=
  (ptrans (cons a (cons b .. (cons c nil) ..)) P Q)
    (at level 90) : type_scope.

#[export] Hint Constructors ptrans : LTS.


Definition trans_invariant
  [Label Node] `{LTS Label Node}
  (PN : Node -> Prop) (PL : Label -> Prop) :=
  forall (N0 N1 : Node) (a : Label),
    (N0 =(a)=> N1) -> PN N0 -> PL a ->
    PN N1.


Fact trans_invariant_true : forall [Label Node] `{LTS Label Node},
    trans_invariant (fun (_ : Node) => True) (fun (_ : Label) => True).

Proof.
  unfold trans_invariant.
  intros.
  constructor.
Qed.

#[export] Hint Resolve trans_invariant_true : LTS.


Definition path_invariant
  [Label Node] `{LTS Label Node}
  (PN : Node -> Prop) (PP : list Label -> Prop) :=
  forall (N0 N1 : Node) (path : list Label),
    (N0 =[path]=> N1) -> PN N0 -> PP path ->
    PN N1.


#[export] Hint Unfold trans_invariant path_invariant : LTS.
#[export] Hint Transparent trans_invariant path_invariant : LTS.


Definition trans_preserve
  [A Label Node] `{LTS Label Node}
  (F : Node -> A) (PL : Label -> Prop) :=
  forall (N0 N1 : Node) (a : Label),
    (N0 =(a)=> N1) -> PL a ->
    F N0 = F N1.


Definition path_preserve
  [A Label Node] `{LTS Label Node}
  (F : Node -> A) (PP : list Label -> Prop) :=
  forall (N0 N1 : Node) (path : list Label),
    (N0 =[path]=> N1) -> PP path ->
    F N0 = F N1.


#[export] Hint Unfold trans_preserve path_preserve : LTS.
#[export] Hint Transparent trans_preserve path_preserve : LTS.


Section PathFacts.
  Context [Label : Type].
  Context [Node : Type].
  Context `{lts : LTS Label Node}.


  Lemma path_nil : forall {N0 N1}, N0 =[]=> N1 -> N0 = N1.

  Proof.
    intros.
    inversion_clear H.
    reflexivity.
  Qed.

  #[global] Arguments path_nil source target : rename.


  Lemma path_seq0 : forall [a] [N0 N1],
      N0 =( a )=> N1  ->  N0 ={ a }=> N1.

  Proof.
    intros.
    apply (STcons H).
    apply STnil.
  Qed.

  #[global] Arguments path_seq0 act source target : rename.


  Lemma path_seq1 : forall [a path N0 N1 N'],
      (N0 =( a )=> N1) ->
      (N1 =[ path ]=> N') ->
      (N0 =[ a::path ]=> N').

  Proof.
    intros.
    apply (STcons H).
    assumption.
  Qed.

  #[global] Arguments path_seq1 act path source middle target : rename.


  Lemma path_seq : forall [path1 path2] [P1] P2 [P3],
      (P1 =[ path1 ]=> P2) ->
      (P2 =[ path2 ]=> P3) ->
      (P1 =[ path1 ++ path2 ]=> P3).

  Proof.
    induction path1; intros path2 P1 P2 P3 T1 T2.
    - inversion_clear T1; auto.
    - inversion_clear T1.
      apply (STcons T0).
      apply (IHpath1 _ _ P2); auto.
  Qed.

  #[global] Arguments path_seq path_left path_right source middle target : rename.


  Lemma path_seq1' : forall [path a P1 P2 P3],
      (P1 =[ path ]=> P2) ->
      (P2 =(a)=> P3) ->
      (P1 =[ path ++ [a] ]=> P3).

  Proof.
    intros.
    eapply path_seq; eauto.
    apply path_seq0; auto.
  Qed.

  #[global] Arguments path_seq1' path act source middle target : rename.


  Lemma path_split0 : forall [a] [N0 N1],
      N0 ={ a }=> N1  ->  N0 =( a )=> N1.

  Proof.
    intros.
    inversion_clear H.
    apply path_nil in T1.
    subst.
    assumption.
  Qed.

  #[global] Arguments path_split0 act source target : rename.


  Lemma path_split1 : forall {a path N0 N'},
      ptrans (a :: path) N0 N' <->
        exists N1, trans a N0 N1 /\  ptrans path N1 N'.

  Proof.
    split; intros.
    - inversion_clear H.
      exists N2.
      auto.
    - ltac1:(decompose record H).
      econstructor; eauto.
  Qed.

  #[global] Arguments path_split1 act path source target : rename.


  Lemma path_split : forall {path1 path2 P0 P2},
      ptrans (path1 ++ path2) P0 P2 <->
        exists P1, ptrans path1 P0 P1 /\ ptrans path2 P1 P2.

  Proof with (auto with LTS).
    induction path1; split; intros; simpl in *.
    - exists P0...
    - destruct H as [P1 [T0 T1]].
      inversion_clear T0.
      auto.
    - apply path_split1 in H as (P0' & T0 & T0').
      eapply IHpath1 in T0' as (P1 & T0' & T1).
      exists P1...
      split...
      apply (path_seq1 T0 T0').
    - destruct H as [P1 [T0 T1]].
      inversion_clear T0.
      apply path_seq1 with (middle := N1); auto.
      apply path_seq with (middle := P1); auto.
  Qed.

  #[global] Arguments path_split path_left path_right source target : rename.


  Lemma path_split1' : forall [path a P0 P2],
      ptrans (path ++ [a]) P0 P2 ->
      exists P1, ptrans path P0 P1 /\ trans a P1 P2.

  Proof.
    intros *.
    intro T.
    apply path_split in T as [P1 [T0 T1]].
    apply path_split0 in T1.
    exists P1; auto.
  Qed.

  #[global] Arguments path_split1' path path_act source target : rename.


  Lemma path_split_In : forall [path a P0 P1],
      In a path ->
      ptrans path P0 P1 ->
      exists P0' P1' path0' path1',
        ptrans path0' P0 P0'
        /\ trans a P0' P1'
        /\ ptrans path1' P1' P1.

  Proof with (eauto with LTS).
    induction path; intros a' P0 P1 HIn...
    inversion HIn.

    intro T.
    apply path_split1 in T as [P0' [T0 T1]].
    destruct HIn; subst.
    + exists P0, P0', [], path...
    + specialize (IHpath _ P0' P1 H).
      destruct (IHpath T1) as (P0'' & P1' & path0' & path1' & T0' & Ta & T1').
      exists P0'', P1', (a::path0'), path1'...
  Qed.

  #[global] Arguments path_split_In path act source target : rename.


  Section Inversions.
    Lemma path0_inv : forall a N0 N1,
        (N0 ={a}=> N1) <-> (N0 =(a)=> N1).
    Proof. split; auto using path_split0, path_seq0. Qed.


    Lemma path_nil_inv : forall N0 N1,
        (N0 =[]=> N1) <-> N0 = N1.

    Proof.
      split; intros.
      - auto using path_nil.
      - subst; constructor.
    Qed.
  End Inversions.


  Lemma path_trans_invariant
    [PN : Node -> Prop] [PL : Label -> Prop] :
    trans_invariant PN PL -> path_invariant PN (Forall PL).

  Proof with (eauto with LTS).
    unfold path_invariant.
    intros H *.
    generalize dependent N0.
    induction path; intros N0 T PN0 PLp.
    apply path_nil in T; congruence.

    eapply path_split1 in T as (N0' & T0 & T1); subst.
    apply (IHpath N0')...
    - apply H in T0...
      apply T0...
      apply (Forall_inv PLp).
    - apply (Forall_inv_tail PLp).
  Qed.


  Lemma path_trans_preserve
    [A] [F : Node -> A] [PL : Label -> Prop] :
    trans_preserve F PL -> path_preserve F (Forall PL).

  Proof with (eauto with LTS).
    unfold path_preserve.
    intros H *.
    generalize dependent N0.
    induction path; intros N0 T PLp.
    apply path_nil in T; congruence.

    eapply path_split1 in T as (N0' & T0 & T1); subst.
    rewrite (H _ _ _ T0 (Forall_inv PLp)).
    apply (IHpath N0')...
    apply (Forall_inv_tail PLp).
  Qed.
End PathFacts.


#[export] Hint Resolve path_trans_invariant : inv LTS.
#[export] Hint Resolve path_trans_preserve : inv LTS.
#[export] Hint Resolve path_seq : LTS.


#[export] Hint Rewrite -> @path_split1 @path_split @path_nil_inv using spank : LTS.
#[export] Hint Rewrite -> @path0_inv using spank : LTS_concl.


Notation always := (fun _ => True).


Fact Forall_True : forall [A] (l : list A), Forall always l.
Proof. induction l; auto. Qed.

#[export] Hint Resolve Forall_True : inv LTS.


Fact apply_invariant [Label Node] `{LTS Label Node} [N0 N1 a P PL] :
  trans_invariant P PL -> (N0 =(a)=> N1) -> PL a -> P N0 -> P N1.
Proof. eauto. Qed.


Fact apply_invariant_path [Label Node] `{LTS Label Node} [N0 N1 path P PL] :
  trans_invariant P PL -> (N0 =[path]=> N1) -> Forall PL path -> P N0 -> P N1.
Proof.
  intros. eapply path_trans_invariant; eauto.
Qed.


Fact apply_preserve [Label Node] `{LTS Label Node} [A : Type] [F : Node -> A] [N0 N1 a PL] :
  trans_preserve F PL -> (N0 =(a)=> N1) -> PL a -> F N0 = F N1.
Proof. eauto. Qed.


Fact apply_preserve_path [Label Node] `{LTS Label Node} [A : Type] [F : Node -> A] [N0 N1 path PL] :
  trans_preserve F PL -> (N0 =[path]=> N1) -> Forall PL path -> F N0 = F N1.
Proof. intros. eapply path_trans_preserve; eauto. Qed.


Definition prop_transport_r [Node0 Node1]
  (P0 : Node0 -> Prop) (P1 : Node1 -> Prop)
  (F : Node0 -> Node1) :=
  (forall N0 N1, N1 = F N0 -> P0 N0 -> P1 N1).

Definition prop_transport_l [Node0 Node1]
  (P0 : Node0 -> Prop) (P1 : Node1 -> Prop)
  (F : Node0 -> Node1) :=
  (forall N0 N1, N1 = F N0 -> P1 N1 -> P0 N0).


Lemma transport_invariant_r
  [Node0 Label0] `{lts : LTS Label0 Node0}
  [Node1]
  [P0 : Node0 -> Prop] [P1 : Node1 -> Prop] [PL : Label0 -> Prop]
  [F : Node0 -> Node1]
  [N0 N1 : Node0] [a : Label0] :
  trans_invariant P0 PL ->
  prop_transport_r P0 P1 F ->
  (N0 =(a)=> N1) -> PL a -> P0 N0 -> P1 (F N1).

Proof.
  intros.
  eapply H0; eauto with LTS.
Qed.

Lemma transport_invariant_path_r
  [Node0 Label0] `{lts : LTS Label0 Node0}
  [Node1]
  [P0 : Node0 -> Prop] [P1 : Node1 -> Prop] [PL : Label0 -> Prop]
  [F : Node0 -> Node1]
  [N0 N1 : Node0] [path : list Label0] :
  trans_invariant P0 PL ->
  prop_transport_r P0 P1 F ->
  (N0 =[path]=> N1) -> Forall PL path -> P0 N0 -> P1 (F N1).

Proof.
  intros.
  eapply H0; eauto with LTS.
  eapply (apply_invariant_path); eauto.
Qed.

Lemma transport_invariant_l
  [Node0 Label0] `{lts : LTS Label0 Node0}
  [Node1]
  [P0 : Node0 -> Prop] [P1 : Node1 -> Prop] [PL : Label0 -> Prop]
  [F : Node0 -> Node1]
  [N0 N1 : Node0] [a : Label0] :
  trans_invariant P0 PL ->
  prop_transport_l P0 P1 F ->
  (N0 =(a)=> N1) -> PL a -> P1 (F N0) -> P0 N1.

Proof.
  intros.
  enough (P0 N0) by eauto with LTS.
  eapply H0; eauto with LTS.
Qed.


Ltac2 find_transport solver target new_target p :=
  let transp_v := Fresh.in_goal @H in
  ltac1:(transp_v p |- eassert (@prop_transport_r _ _ _ p _)
          as transp_v by solve [trivial with inv])
          (Ltac1.of_ident transp_v) (Ltac1.of_constr p);
  let transp_h := hyp transp_v in

  let htr_t := Constr.type transp_h in
  let htr_t := (eval red in $htr_t) in
  let (p', convert) := match! htr_t with
                       | prop_transport_r ?p' _ ?convert => (p', convert)
                       end in

  replace $target with ($convert $new_target) by solver ();

  enough ($p' $new_target) by solver ();
  p'.


Ltac2 solve_invariant solver :=
  let (pred, trans_hyp, from, label, one_step) :=
    (multi_match! goal with
     | [ trans : ?x0 =(?a)=> ?x1 |- ?p ?x] =>
         replace $x with $x1 by solver ();
         (p, hyp trans, x0, a, true)
     | [ trans : ?x0 =(?a)=> ?x1 |- ?p ?x] =>
         let p' := find_transport solver x x1 p
         in (p', hyp trans, x0, a, true)
     | [ trans : ?x0 =[?a]=> ?x1 |- ?p ?x] =>
         replace $x with $x1 by solver ();
         (p, hyp trans, x0, a, false)
     | [ trans : ?x0 =[?a]=> ?x1 |- ?p ?x] =>
         let p' := find_transport solver x x1 p
         in (p', hyp trans, x0, a, false)
     | [ _ : ?p ?x0 |- ?p ?x1 ] =>
         (* Desperation. We try to find another node from which we may find any connection. *)
         let trans := Fresh.in_goal @H in
         ltac1:(x0 x1 trans |- eassert (x0 =(_)=> x1) as trans)
                 (Ltac1.of_constr x0) (Ltac1.of_constr x1) (Ltac1.of_ident trans)
               > [solve [solver ()] | ];
         let trans_h := hyp trans in

         let trans_t := Constr.type trans_h in
         (* let trans_t := (eval red in $trans_t) in *)
         let label_t :=
           match! trans_t with
           | (_ =(?t)=> _) => t
           end in
         (p, trans_h, x0, label_t, true)
     end)
  in

  let h_inv := Fresh.in_goal @H in
  ltac1:(pred h_inv |- eassert (trans_invariant pred _) as h_inv by (now trivial with inv))
          (Ltac1.of_constr pred) (Ltac1.of_ident h_inv);
  let h_inv_h := hyp h_inv in

  let h_inv_t := Constr.type h_inv_h in
  (* let tl := (eval red in $h_inv_t) in *)
  let pred_l :=
    match! h_inv_t with
    | trans_invariant _ ?q => if one_step then '($q) else '(Forall $q)
    end in

  let h_label := Fresh.in_goal @H in
  assert ($pred_l $label) as $h_label by solver ();
  let h_label_h := hyp h_label in

  (if one_step
   then apply (apply_invariant $h_inv_h $trans_hyp $h_label_h)
   else apply (apply_invariant_path $h_inv_h $trans_hyp $h_label_h)
  ).


Ltac solve_invariant := ltac2:(solve_invariant (fun () => eauto with LTS)).
