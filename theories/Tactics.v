Require Import Coq.Program.Equality.

From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Bool.
From Coq Require Import String.
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


Ltac2 print_kind c :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Rel _ => printf "rel"
  | Constr.Unsafe.Var _ => printf "var"
  | Constr.Unsafe.Meta _ => printf "meta"
  | Constr.Unsafe.Evar _ _ => printf "evar"
  | Constr.Unsafe.Sort _ => printf "sort"
  | Constr.Unsafe.Cast _ _ _ => printf "cast"
  | Constr.Unsafe.Prod _ _ => printf "prod"
  | Constr.Unsafe.Lambda _ _ => printf "lambda"
  | Constr.Unsafe.LetIn _ _  _ => printf "letin"
  | Constr.Unsafe.App _ _ => printf "app"
  | Constr.Unsafe.Constant _ _ => printf "constant"
  | Constr.Unsafe.Ind _ _ => printf "ind"
  | Constr.Unsafe.Constructor _ _ => printf "constructor"
  | Constr.Unsafe.Case _ _ _ _ _ => printf "case"
  | Constr.Unsafe.Fix _ _ _ _ => printf "fix"
  | Constr.Unsafe.CoFix _ _ _ => printf "cofix"
  | Constr.Unsafe.Proj _ _ _ => printf "proj"
  | Constr.Unsafe.Uint63 _ => printf "uint63"
  | Constr.Unsafe.Float _ => printf "float"
  | Constr.Unsafe.Array _ _ _ _ => printf "array"
  | Constr.Unsafe.String _ => printf "String"
  end.


(** Unshelves all evars that arose due to an existential tactic *)
Ltac2 unshelve tac :=
  let result := { contents := (fun () => Control.throw Not_found) } in
  let f := ltac1:(tac |- unshelve (tac ())) in
  let () := f (Ltac1.lambda (fun _ => let res := tac () in (result.(contents) := fun () => res); ltac1val:(idtac))) in
  result.(contents) ().

Ltac2 Notation "unshelve" t(thunk(tactic)) := unshelve (t); auto.


Local Ltac2 replace_in (lhs: constr) (rhs: constr) (in_ : ident option) solver :=
  match in_ with
  | None => ltac1:(lhs rhs |- replace lhs with rhs in * )
                   (Ltac1.of_constr lhs) (Ltac1.of_constr rhs)
  | Some in_ =>
      ltac1:(lhs rhs h |- replace lhs with rhs in h)
              (Ltac1.of_constr lhs) (Ltac1.of_constr rhs) (Ltac1.of_ident in_)
  end >
    [ | match solver with
        | None => ()
        | Some solver => solve [solver ()]
        end
    ].

Ltac2 Notation "replace"
  lhs(open_constr) "with" rhs(constr)
  h(opt(seq("in", ident)))
  s(opt(seq("by", thunk(tactic))))
  := replace_in lhs rhs h s.


(* Local Ltac2 replace_p (lhs: constr) (rhs: constr) (in_ : ident option) solver_l solver_r := *)
(*   let equiv_l := Fresh.in_goal @EQUIV_L in *)
(*   let equiv_r := Fresh.in_goal @EQUIV_R in *)
(*   enough '($rhs -> $lhs) *)
(*     as $equiv_l *)
(*        > *)
(*          [ *)

(*          ] *)
(*   match in_ with *)
(*   | None => ltac1:(lhs rhs |- replace lhs with rhs in * ) *)
(*                    (Ltac1.of_constr lhs) (Ltac1.of_constr rhs) *)
(*   | Some in_ => *)
(*       ltac1:(lhs rhs h |- replace lhs with rhs in h) *)
(*               (Ltac1.of_constr lhs) (Ltac1.of_constr rhs) (Ltac1.of_ident in_) *)
(*   end > *)
(*     [ | match solver with *)
(*         | None => () *)
(*         | Some solver => solve [solver ()] *)
(*         end *)
(*     ]. *)


Ltac2 smart_inv h :=
  let destr () :=
    let h0 := hyp h in
    let t := Constr.type h0 in
    let t_old := (eval cbv in $t) in
    let cleanup () :=
      let h1 := hyp h in
      let t := Constr.type h1 in
      let t_new := (eval cbv in $t) in
      if Constr.equal t_old t_new
      then clear $h
      else ()
    in
    ltac1:(h |- inversion h as []) (Ltac1.of_constr h0); (* ltac2 inversion screws up naming *)
    Control.enter cleanup
  in
  Control.enter destr.


Ltac2 congruence_ () := ltac1:(congruence).
Ltac2 Notation "congruence" := congruence_ ().

Ltac2 Notation "contradiction" c(opt(seq(constr, bindings))) :=  contradiction c.


Ltac2 Notation "rename" i(ident) "into" n(ident) := rename [(i, n)].

Ltac2 exfalso_ () := ltac1:(exfalso).
Ltac2 Notation "exfalso" := exfalso_ ().


Ltac2 kill h :=
  smart_inv h; subst; try (congruence); try (contradiction).

Ltac2 Notation "kill" h(ident) := kill h.


Ltac2 split_app c : constr * constr list :=
  let rec go c acc :=
    lazy_match! c with
    | ?f ?a => go f (a::acc)
    | _ => (c, acc)
    end in
  go c [].

Ltac2 rec get_left_app c :=
  lazy_match! c with
  | ?f _ => get_left_app f
  | _ => c
  end.

Ltac2 is_constructor_app c := Constr.is_constructor (get_left_app c).


Inductive HAVE (P : Prop) := HAVE_ : P -> HAVE P.
Notation "### P" := (HAVE P) (at level 200) : type_scope.

Lemma HAVE_inv : forall P, (### P) <-> P.
Proof. split; intros H. inversion H; eauto. constructor. eauto. Qed.

Ltac2 re_have_ (f : unit -> unit) :=
  let havs := List.map_filter
                (fun (h, _v, t) =>
                   let hh := hyp h in
                   let h' := Fresh.in_goal h in
                   match! t with
                   | HAVE ?t' => assert $t' as $h' by (destruct $hh; assumption); Some h'
                   | _ => None
                   end
                )
                (Control.hyps ())
  in f ();
     List.iter (fun h => clear $h) havs;
     ().

Ltac2 Notation "re_have" t(thunk(tactic)) := Control.enter (fun _ => re_have_ t).


Ltac2 spank () := solve [re_have (eauto 1 with datatypes LTS)].
Ltac2 Notation "spank" := spank ().
Ltac spank := ltac2:(spank).


Ltac2 rec generalize_dependent (is : ident list) :=
  match is with
  | [] => ()
  | i::rest =>
      ltac1:(i |- generalize dependent i) (Ltac1.of_ident i);
      generalize_dependent rest
  end.
Ltac2 Notation "generalize" "dependent" i(list1(ident)) := generalize_dependent i.


Ltac2 lia_ () := ltac1:(lia).
Ltac2 Notation lia := lia_ ().


Create HintDb LTS.
Create HintDb LTS_concl.
Create HintDb LTS_early.
Create HintDb LTS_concl_early.
Create HintDb rew.
Create HintDb bs.

(* https://github.com/coq/coq/issues/14028 *)
Lemma hintdb_teaser : 21 + 16 = 37. simpl. auto. Qed.
Hint Rewrite hintdb_teaser : LTS LTS_concl.


(** "bad statement" --- tactic to brutally find contradictions *)
Ltac2 bs_ (on : (constr * (unit -> unit) option) option) :=
  repeat (intros ?);
  match on with
  | None => ()
  | Some (c, s) =>
      let s :=
        (match s with
                | None => fun () => subst; eauto with LTS bs datatypes
                | Some s => s
               end)
      in
      assert $c by (s ())
  end;

  simpl in *;
  try (ltac1:(autorewrite with bs in * ));
  solve
    [ contradiction
    | congruence
    | lia
    | List.iter (fun (h, _, _) => try (kill $h)) (hyps ())
    | match! goal with
      | [h : ?p |- _] =>
          if (Constr.equal (Constr.type p) 'Prop) then () else fail;
          let hh := hyp h in
          lazy_match! p with
          | not _ =>
              exfalso;
              apply $hh;
              solve [eauto 3 with bs LTS datatypes]
          | _ =>
              absurd $p > [| exact $hh ];
              solve [eauto 3 with bs LTS datatypes]
          end
      end
    ].

Ltac2 bs_or
  (on : (constr * (unit -> unit) option) option)
  (or_catch : unit -> unit) :=
  orelse (fun () => bs_ on) (fun _ => or_catch ()).


Ltac2 Notation "bs"
  on(opt(seq(
             open_constr,
             opt(seq("by", thunk(tactic)))
  ))) :=
  Control.enter (fun () => bs_or on
                          (fun () => Control.zero (Init.Tactic_failure (Some (Message.of_string "Nothing to bs about"))))
    ).


Ltac2 Notation "doubt"
  on(opt(seq(
             open_constr,
             opt(seq("by", thunk(tactic)))
  ))) :=
  Control.enter (fun () => Control.once (fun () => try (bs_ on))).


Ltac2 ssubst_ () : unit :=
  match! goal with
  | [|- ?_a = ?_b -> _] => intro
  | [h : ?_a = ?_a |- _] => clear $h
  | [h : ?_x = ?_y |- _] =>
      first
        [ assert False by ltac1:(h |- dependent destruction h) (Ltac1.of_ident h);
          clear $h
        | ltac1:(h |- dependent destruction h) (Ltac1.of_ident h)
        ]
  end.

Ltac2 Notation ssubst := repeat (ssubst_ ()).


(** Replaces all parameters with fresh variables. Returns hypos to destruct. *)
Ltac2 rec unsubst (t : constr) : ident list :=
  match! t with
  | ?f ?x =>
      if Bool.or (Constr.is_var x)
           (Bool.or (Constr.is_ind x) (Constr.is_const x))
      then unsubst f
      else
        (let i := Fresh.in_goal @arg in
         let e := Fresh.in_goal @HEq in
         remember $x as $i eqn:$e;
         (e :: unsubst f)
        )
  | _ => []
  end.


Ltac2 inversion_stable (c : constr) (i : intro_pattern option) : unit :=
  let var := Fresh.in_goal @x in
  let to_kill := unsubst (Constr.type c) in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var v => rename $v into $var
  | _ => remember $c as $var
  end;
  Std.inversion FullInversion (ElimOnIdent var) i None;
  Control.enter (
      fun () =>
        let _ := List.map (
                     fun i =>
                       ltac1:(i |- dependent destruction i) (Ltac1.of_constr (hyp i))
                   ) to_kill
        in
        try (clear $var); ssubst
    ).

Ltac2 Notation "inversion_stable"
  arg(constr)
  pat(opt(seq("as", intropattern))) :=
  inversion_stable arg pat.


Ltac2 rec smash_eq_on_ (n0 : ident) (ns : ident list) :=
  match ns with
  | [] => ()
  | n1 :: rest =>
      let h := Fresh.in_goal @HEq in
      let n1_h := hyp n1 in
      let n0_h := hyp n0 in
      assert ({$n1_h = $n0_h}+{$n1_h <> $n0_h}) as [$h|$h] by eauto 3 with LTS;
      try (congruence);
      Control.enter (fun () => smash_eq_on_ n0 rest)
  end.

Ltac2 rec smash_eq_ (ns : ident list) :=
  match ns with
  | [] => ()
  | n0 :: rest =>
      Control.enter (fun () => smash_eq_on_ n0 rest);
      smash_eq_ rest;
      try (subst $n0; clear $n0)
  end.

Ltac2 cleanup_eq () :=
  repeat (Control.enter(
              fun () =>
                match! goal with
                | [h : ?_a = ?_a |- _] => clear $h
                end
    )).

Ltac2 Notation "smash_eq_on" n(ident) ns(list1(ident)) := smash_eq_on_ n ns; cleanup_eq ().
Ltac2 Notation "smash_eq" ns(list1(ident)) := smash_eq_ ns; cleanup_eq ().


Ltac2 rec strip_exists h :=
  let t := Constr.type (hyp h) in
  lazy_match! (eval simpl in $t) with
  | ex ?body =>
      match (Constr.Unsafe.kind body) with
      | Constr.Unsafe.Lambda arg _val =>
          let hh := hyp h in
          let arg_n := match Constr.Binder.name arg with
                       | None => Fresh.in_goal @x
                       | Some n => Fresh.in_goal n
                       end in
          destruct $hh as [$arg_n $h];
          strip_exists h
      | _ =>
          let hh := hyp h in
          destruct $hh as [? $h];
          strip_exists h
      end
  | ?t =>
      t
  end.

Ltac2 Notation "strip" "exists" h(ident) := let _ := strip_exists h in ().


Inductive INV (P : Prop) := INV_intro : P -> INV P.
#[export] Hint Constructors INV : LTS.

Lemma INV_inv {P} : INV P <-> P. (* https://github.com/coq/coq/issues/14028 *)
Proof. split; intros. kill H. constructor. auto. Qed.
#[export] Hint Rewrite -> @INV_inv using auto : LTS_concl.

Notation "!!! P" := (INV P) (at level 200) : type_scope.


Lemma not_or_inv P Q : ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof. ltac1:(intuition). Qed.

Lemma or_neg_inv P Q : ~ Q -> P \/ Q <-> P.
Proof. ltac1:(intuition). Qed.

Lemma neg_or_inv P Q : ~ P -> P \/ Q <-> Q.
Proof. ltac1:(intuition). Qed.

Lemma or_False_inv P : P \/ False <-> P.
Proof. ltac1:(intuition). Qed.

Lemma False_or_inv P : False \/ P <-> P.
Proof. ltac1:(intuition). Qed.

Lemma and_False_inv P : P /\ False <-> False.
Proof. ltac1:(intuition). Qed.

Lemma False_and_inv P : False /\ P <-> False.
Proof. ltac1:(intuition). Qed.

Lemma or_True_inv P : P \/ True <-> True.
Proof. ltac1:(intuition). Qed.

Lemma True_or_inv P : True \/ P <-> True.
Proof. ltac1:(intuition). Qed.

Lemma and_True_inv P : P /\ True <-> P.
Proof. ltac1:(intuition). Qed.

Lemma True_and_inv P : True /\ P <-> P.
Proof. ltac1:(intuition). Qed.

Lemma and_imp_inv : forall A B P, (A /\ B -> P) <-> (A -> B -> P).
Proof. ltac1:(intuition). Qed.

Lemma True_imp_inv P : (True -> P) <-> P.
Proof. ltac1:(intuition). Qed.

Lemma imp_True_inv P : (P -> True) <-> True.
Proof. ltac1:(intuition). Qed.

Lemma False_imp_inv P : (False -> P) <-> True.
Proof. ltac1:(intuition). Qed.

Lemma imp_False_inv P : (P -> False) <-> ~ P.
Proof. ltac1:(intuition). Qed.

Ltac2 introsmash () :=
  repeat (
      let h := Fresh.in_goal @INTROSMASH in
      intros $h;
      let hh := hyp h in
      try (inversion $hh)
    ).

#[export] Hint Rewrite
-> or_neg_inv neg_or_inv
    using (solve [congruence | ltac2:(introsmash ()); subst; auto 1 using eq_sym]) : LTS LTS_concl.

#[export] Hint Rewrite
-> not_or_inv and_imp_inv
    or_False_inv False_or_inv
    and_False_inv False_and_inv
    or_True_inv True_or_inv
    and_True_inv True_and_inv
    True_imp_inv imp_True_inv
    False_imp_inv imp_False_inv
    using assumption : LTS LTS_concl.


Ltac2 debs (h : ident) :=
  let hh := hyp h in
  let ht := Constr.type hh in
  let equiv := Fresh.in_goal @EQUIV in
  match! eval cbv in $ht with
  | context c [?a = ?b] =>
      if Constr.equal a b
      then
        assert ($a = $b <-> True) as $equiv by ((split; intros) > [constructor | reflexivity]);
        ltac1:(equiv h |- rewrite_strat bottomup progress equiv in h) (Ltac1.of_ident equiv) (Ltac1.of_ident h);
        clear $equiv
      else
        let (fa, aa) := split_app a in
        let (fb, ab) := split_app b in
        if Bool.and (Constr.is_constructor fa) (Constr.is_constructor fb)
        then
          if Constr.equal fa fb
          then
            let ht' := List.fold_right (fun (xa, xb) acc =>
                                          if Constr.equal xa xb then acc
                                          else if Constr.equal acc 'True
                                               then '($xa = $xb)
                                               else '($xa = $xb /\ $acc)
                         )
                         (List.combine aa ab)
                         'True
            in
            assert ($a = $b <-> $ht') as $equiv
                by
                (split; intros $equiv) >
                  [
                    let he := hyp equiv in inversion $he; intros; subst; repeat split
                  |
                    kill $equiv
                  ];
            ltac1:(equiv h |- rewrite_strat bottomup progress equiv in h) (Ltac1.of_ident equiv) (Ltac1.of_ident h);
            clear $equiv

          else
            let _ := Pattern.instantiate c 'False in
            assert ($a = $b <-> False) as $equiv by (split; intros $equiv; kill $equiv);
            ltac1:(equiv h |- rewrite_strat bottomup progress equiv in h) (Ltac1.of_ident equiv) (Ltac1.of_ident h);
            clear $equiv
        else fail
  end.


Ltac2 rec split_hyp (h : ident) : ident list :=
  let hh := hyp h in
  let ht := Constr.type hh in
  match! (eval simpl in $ht) with

  | False => clear - $h; []
  | True => clear $h; []

  | ?_a = ?_a => clear $h; []
  | existT _ _ _ = existT _ _ _ =>
      ltac1:(h |- dependent destruction h) (Ltac1.of_ident h);
      []
  | ?a = ?b =>
      match Constr.Unsafe.kind a, Constr.Unsafe.kind b with
      | Constr.Unsafe.Var i, _ => subst $i
      | _, Constr.Unsafe.Var i => subst $i
      | _, _ => fail
      end; []

  | ?a = ?b =>
      let al := get_left_app a in
      let bl := get_left_app b in
      if Bool.and (Constr.is_constructor al) (Constr.is_constructor bl)
      then
        if Constr.equal (eval cbv in $al) (eval cbv in $bl)
        then
          let rec collect () :=
            match! goal with
            | [|- ?_ht -> _] =>
                let h' := Fresh.in_goal h in
                intros $h';
                List.append (split_hyp h') (collect ())
            | [|-_] => []
            end in

          injection $hh;
          clear $h;
          collect ()
        else
          let i := Fresh.in_goal @BS in
          assert False as $i by kill $h;
          clear - $i;
          [i]
      else (fail; [])


  | ?a = ?b =>
      if Bool.and (is_constructor_app a)
           (Bool.neg (is_constructor_app b))
      then
        apply eq_sym in $h;
        []
      else (fail; [])

  | ?x = ?c =>
      if Bool.and (is_constructor_app c) (Bool.neg (is_constructor_app x))
      then match! goal with
           | [h' : ?x' = ?c' |- _] =>
               if Bool.and
                    (is_constructor_app c')
                    (Bool.and (Constr.equal x x') (Bool.neg (Ident.equal h h')))
               then let hh' := hyp h' in rewrite $hh' in $h; split_hyp h
               else (fail; [])
           end
      else (fail; [])

  | _ /\ _ =>
      let h1 := Fresh.in_goal h in
      destruct $hh as [$h $h1];
      let l0 := split_hyp h in
      orelse
        (* Might not exist anymore! *)
        (fun () => List.append l0 (split_hyp h1))
        (fun _ => l0)

  | _ <-> _ =>
      unfold iff in $h;
      split_hyp h
  | ex _ => let _ := strip_exists h in split_hyp h
  | context [match ?p with _ => _ end] =>
      match! goal with
      | [h' : ?p' = ?c |- _] =>
          if Bool.and (is_constructor_app c) (Constr.equal p p')
          then let hh' := hyp h' in rewrite $hh' in $h; simpl in $h; split_hyp h
          else (fail; [])
      end
  | INV _ =>
      destruct $hh as ($h);
      ltac1:(h |- dependent destruction h) (Ltac1.of_ident h);
      []
  | _ => [h]
  end.


Notation "n |: p" := (exists n : p, True) (at level 80) : type_scope.


#[export] Hint Rewrite <- app_comm_cons app_assoc using assumption : LTS_L_prep.
#[export] Hint Rewrite -> app_comm_cons app_assoc using assumption : LTS_R_prep.


Lemma Falsify_inv P : False -> P <-> False.
Proof. ltac1:(intuition). Qed.
Hint Rewrite -> Falsify_inv using assumption : bs.


Ltac autorewrite_hyp_LTS h :=
  rewrite_strat choice
    (
      hints bs
    )
    (
      topdown progress hints LTS
    )
    (
      try (bottomup progress hints LTS_L_prep);
      topdown progress hints LTS_L
    )
    (
      try (bottomup progress hints LTS_R_prep);
      topdown progress hints LTS_R
    )
    in h.

Ltac autorewrite_concl_LTS :=
  rewrite_strat choice
    (
      hints bs
    )
    (
      topdown progress hints LTS_concl
    )
    (
      try (bottomup progress hints LTS_L_prep);
      topdown progress hints LTS_concl_L
    )
    (
      try (bottomup progress hints LTS_R_prep);
      topdown progress hints LTS_concl_R
    ).


Ltac2 autorewrite_LTS (h : ident option) :=
  match h with
  | Some h =>
      ltac1:(h |- autorewrite_hyp_LTS h) (Ltac1.of_ident h)
  | None =>
      ltac1:(autorewrite_concl_LTS)
  end.


Ltac2 autorewrite_LTS_lite (h : ident option) :=
  match h with
  | Some h =>
      ltac1:(h |- rewrite_strat choice (hints bs) (topdown progress hints LTS) in h) (Ltac1.of_ident h)
  | None =>
      ltac1:(rewrite_strat choice (hints bs) (topdown progress hints LTS_concl))
  end.


Ltac2 autorewrite_compat (h : ident option) :=
  match h with
  | Some h =>
      ltac1:(h |- autorewrite with LTS in h) (Ltac1.of_ident h)
  | None =>
      ltac1:( autorewrite with LTS_concl)
  end.


Ltac2 rec hammer_prep_hyp_iter hs (rewriter : ident -> unit) :=
  match hs with
  | [] => ()
  | h::hs =>
      orelse
        (fun _ =>
           let _ := hyp h in (* To check if it's still a hyp *)
           simpl in $h;
           ltac1:(h |- autounfold with rew in h) (Ltac1.of_ident h);

           let hs' :=
             orelse
               (fun _ =>
                  progress (rewriter h; simpl in $h);
                  [h]
               )
               (fun _ =>
                  simpl in $h;
                  Control.progress (fun _ => repeat (debs h); split_hyp h)
               )
           in
           match Control.numgoals () with
           | 0 => ()
           | 1 => hammer_prep_hyp_iter (List.append hs' hs) rewriter
           | n =>
               let msg_0 := Message.of_string "Splitting hypothesis " in
               let msg_h := Message.of_ident h in
               let msg_1 := Message.of_string " lead to goal explosion: " in
               let msg_n := Message.of_int n in
               let msg := List.fold_right Message.concat [msg_0; msg_h; msg_1] msg_n in
               Control.throw (Init.Tactic_failure (Some msg))
           end
        )
        (fun _ => hammer_prep_hyp_iter hs rewriter)
  end.

Ltac2 hammer_prep_hyp h rewriter :=
  hammer_prep_hyp_iter [h] rewriter.


Ltac2 simpl_match () :=
  match! goal with
  | [|- context [match ?x with _ => _ end]] =>
      match! goal with
      | [h : ?x' = ?c |- _] =>
          if Bool.and (is_constructor_app c) (Constr.equal x x')
          then let hh := hyp h in rewrite $hh; simpl
          else fail
      | [h : ?c = ?x' |- _] =>
          if Bool.and (is_constructor_app c) (Constr.equal x x')
          then let hh := hyp h in rewrite <- $hh; simpl
          else fail
      | [|- _] =>
          destruct $x eqn:?;
            match Control.numgoals () with
            | 1 => ()
            | _ => fail
            end
      end
  end.


Ltac2 hsimpl_ (c : clause option) (rewriter : (ident option -> unit) option) : unit :=
  let rewriter :=
    match rewriter with
    | None => fun h => autorewrite_LTS h
    | Some rewriter => rewriter
    end
  in
  let (on_hyps, on_concl) :=
    match c with
    | None => ([], AllOccurrences)
    | Some {on_hyps;on_concl} =>
        let on_hyps :=
          match on_hyps with
          | None => (* Star *)
              let selector (h, _, _) := (h, AllOccurrences, InHyp) in
              List.map selector (List.rev (Control.hyps ()))
          | Some hs => hs
          end
        in
        let on_hyps :=
          let selector cl :=
            match cl with
            | (h, AllOccurrences, _) => [h]
            | (_, NoOccurrences, _) => []
            | (h, _, _) =>
                let msg_0 := Message.of_string "Unsupported hyp clause in hsimpl for " in
                let msg_h := Message.of_ident h in
                Control.throw (Init.Tactic_failure (Some (Message.concat msg_0 msg_h)))
            end in
          List.flat_map selector on_hyps (* TODO: handle locations :) *)
        in
        (on_hyps, on_concl)
    end
  in
  let _ := hammer_prep_hyp_iter on_hyps (fun h => rewriter (Some h)) in

  match on_concl with
  | AllOccurrences =>
      simpl in |- *;
      try (rewriter None);
      simpl in |- *;
      repeat (simpl_match ());
      simpl in |- *
  | NoOccurrences => ()
  | _ =>
      let msg := Message.of_string "Unsupported concl occurrences in hsimpl" in
      Control.throw (Init.Tactic_failure (Some msg))
  end.

Ltac2 Notation "hsimpl" cl(opt(clause)) rewriter(opt(seq("with", thunk(tactic)))) :=
  Control.enter (fun () => hsimpl_ cl rewriter).

Ltac2 Notation "compat_hsimpl" cl(opt(clause)) :=
  Control.enter (fun () => hsimpl_ cl (Some autorewrite_compat)).

Hint Rewrite -> in_app_iff using assumption : LTS LTS_concl.


Ltac2 hammer solver :=
  repeat (first [split | progress intros]);
  try (solve [repeat (first [split | intros ?]); eauto 5 with datatypes LTS; congruence]);

  Control.enter (
      fun () =>
        hsimpl in *;
        subst;
        simpl in *;
        repeat (first [split | progress intros]);
        try (solve
               [ simpl; eauto 5 with datatypes LTS
               | bs
               | solver ()
               ]
          )
    ).

Ltac2 attac_ n :=
  let n := match n with None => 7 | Some n => n end in
  hammer (fun () => re_have (auto n with datatypes LTS)).

Ltac2 Notation "attac" n(opt(tactic)) := attac_ n.

#[global] Ltac attac_ n :=
  let t := solve [auto n with datatypes LTS ] in
  let f := ltac2:(t |- hammer (fun () => re_have (Ltac1.run t))) in
  f t.

#[global] Tactic Notation "attac" := ltac2:(attac).
#[global] Tactic Notation "attac" natural(n) := attac_ n.


Ltac2 eattac_ n :=
  let n := match n with None => 7 | Some n => n end in
  hammer (fun () => solve [repeat eexists; re_have (eauto n with datatypes LTS)]).

Ltac2 Notation "eattac" n(opt(tactic)) := eattac_ n.

#[global] Ltac eattac_ n :=
  let t := solve [repeat eexists; eauto n with datatypes LTS] in
  let f := ltac2:(t |- hammer (fun () => re_have (Ltac1.run t))) in
  f t.

#[global] Tactic Notation "eattac" := ltac2:(eattac).
#[global] Tactic Notation "eattac" natural(n) := eattac_ n.


Ltac2 tattac_ n :=
  let n := match n with None => 7 | Some n => n end in
  hammer (fun () => repeat eexists; re_have (typeclasses_eauto n with core datatypes LTS)).

Ltac2 Notation "tattac" n(opt(tactic)) := tattac_ n.

#[global] Tactic Notation "tattac" := ltac2:(tattac).


(* this sucks, needs to get ident from Constructor and Ind *)
Ltac2 rec guess_head_name t :=
  match! t with
  | not ?x => guess_head_name x
  | ?f ?x => guess_head_name f
  | forall _, ?t => guess_head_name t
  | exists _, ?t => guess_head_name t
  | ?x => match Constr.Unsafe.kind x with
         | Constr.Unsafe.Var i => Fresh.in_goal i
         | _ => Fresh.in_goal @H
         end
  end.


Ltac2 have_ (i : ident option) (t : constr) (solv : (unit -> unit) option) :=
  let i :=
    match i with
    | Some i => i
    | None => guess_head_name t
    end
  in
  let solv :=
    match solv with
    | Some solv => solv
    | None => fun () => attac
    end
  in
  assert (HAVE $t) as $i by (constructor; solv ()).


Ltac2 ehave_ (i : ident option) (t : constr) (solv : (unit -> unit) option) :=
  let i :=
    match i with
    | Some i => i
    | None => guess_head_name t
    end
  in
  let solv :=
    match solv with
    | Some solv => solv
    | None => fun () => eattac
    end
  in
  ltac1:(i t |- eassert (HAVE t) as i) (Ltac1.of_ident i) (Ltac1.of_constr t)
        > [solve [constructor; solv ()]|].


Ltac2 Notation "have" t(constr) i(opt(seq("as", ident))) solv(opt(seq("by", thunk(tactic)))) :=
  have_ i t solv.

Ltac2 Notation "ehave" t(open_constr) i(opt(seq("as", ident))) solv(opt(seq("by", thunk(tactic)))) :=
  ehave_ i t solv.


Definition id_Prop := @id Prop.
#[export] Hint Transparent id_Prop : LTS.
Hint Unfold id_Prop : LTS.
Lemma un_HAVE_id : forall (P : Prop), HAVE P -> id_Prop P.
Proof. intros. kill H. apply H0. Defined.
Coercion un_HAVE_id : HAVE >-> id_Prop.

Lemma un_HAVE : forall [P : Prop], HAVE P -> P.
Proof. intros. kill H. Defined.


Ltac2 find_h (t : constr) (solv : (unit -> unit) option) : constr :=
  let solv :=
    (match solv with
     | Some solv => solv
     | None => fun () =>
                if Constr.has_evar t
                then eauto with LTS
                else auto with LTS
     end) in
  (multi_match! goal with
   | [h : ?t' |- _] =>
       let tc := (eval cbv in $t) in
       let tc' := (eval cbv in $t') in
       unify $tc $tc';
       hyp h
   | [h : HAVE ?t' |- _] =>
       let tc := (eval cbv in $t) in
       let tc' := (eval cbv in $t') in
       unify $tc $tc';
       let hh := hyp h in
       '(un_HAVE $hh)

   | [|- _] =>
       let i := Fresh.in_goal (guess_head_name t) in

       ltac1:(t i |- eassert t as i) (Ltac1.of_constr t) (Ltac1.of_ident i)
             > [solve [solv () | shelve ()]|];
       hyp i
   end
  ).

Ltac2 find_i (t : constr) (solv : (unit -> unit) option) : ident :=
  let solv :=
    (match solv with
     | Some solv => fun () => solve [solv ()]
     | None => fun () =>
                solve
                  [ if Constr.has_evar t
                    then eauto with LTS
                    else auto with LTS
                  | shelve ()
                  ]
     end) in
  (multi_match! goal with
   | [h : ?t' |- _] =>
       let tc := (eval cbv in $t) in
       let tc' := (eval cbv in $t') in
       unify $tc $tc';
       h
   | [h : HAVE ?t' |- _] =>
       let tc := (eval cbv in $t) in
       let tc' := (eval cbv in $t') in
       unify $tc $tc';
       h

   | [|- _] =>
       let i := Fresh.in_goal (guess_head_name t) in

       ltac1:(t i |- eassert t as i) (Ltac1.of_constr t) (Ltac1.of_ident i)
             > [repeat (setoid_rewrite HAVE_inv); solv ()|];
       i
   end
  ).


Notation "`( t )" :=
  (ltac2:(let x :=
            Ltac2.Constr.Pretype.pretype
              Constr.Pretype.Flags.open_constr_flags
              Constr.Pretype.expected_without_type_constraint
              t
          in
          let proof := find_h x None in
          exact $proof
  ))
    (only parsing).

Notation "``( t )" :=
  (ltac2:(let x :=
            Ltac2.Constr.Pretype.pretype
              Constr.Pretype.Flags.open_constr_flags
              Constr.Pretype.expected_without_type_constraint
              t
          in
          find_i x None
  ))
    (only parsing).


Ltac2 consider_ (t : constr) (solver : (unit -> unit) option) :=
  let i := find_i t solver in
  try (autorewrite_LTS (Some i));
  first [progress (hsimpl in $i)| kill $i].

Ltac2 Notation "consider" t(thunk(open_constr)) s(opt(seq("by", thunk(tactic)))) :=
  Control.enter (fun () => unshelve (consider_ (t ()) s)).


Ltac2 blast_cases_ () :=
  match! goal with
  | [_h : context [let (_, _) := ?t in _] |- _] =>
      destruct $t eqn:?
  | [_h : context [match ?t with _ => _ end] |- _] =>
      destruct $t eqn:?
  | [|- context [let (_, _) := ?t in _]] =>
      destruct $t eqn:?
  | [|- context [match ?t with _ => _ end]] =>
      destruct $t eqn:?
  end.

Ltac2 Notation blast_cases :=
  repeat (Control.enter (fun _ => blast_cases_ ())).


Inductive MARK (s : string) (P : Prop) := MARK_ (p : P).


Definition CASE_lock_str : string. refine '("use tac" : string). Qed.
Lemma CASE_lock : forall (P : Prop), MARK CASE_lock_str P -> P. intros. inversion H. auto. Qed.

Definition CASE_remember_str : string. refine '("remember me" : string). Qed.
Lemma unmark_remember : forall (P : Prop), MARK CASE_remember_str P -> P. intros. inversion H. auto. Qed.
Lemma mark_remember : forall (P : Prop), P -> MARK CASE_remember_str P. intros. constructor. auto. Qed.

Ltac2 lock () := apply CASE_lock.
Ltac2 Notation "lock" := lock ().
Ltac2 unlock () :=
  lazy_match! goal with
  | [|- MARK CASE_lock_str _] => apply MARK_
  | [|-_] => ()
  end.

Ltac2 mk_int_ident (base : string) (i : int) : ident :=
  let i := Message.to_string (Message.of_int i) in
  let str := String.app base i in
  match Ident.of_string str with
  | Some id => id
  | None => throw (Tactic_failure (Some (Message.of_string (String.app "Failed to make id: " str))))
  end.

Ltac2 mk_case_ident (i : int) : ident :=
  mk_int_ident "CASE_GUARDED__________________" i.

Ltac2 mk_rem_ident (i : int) : ident :=
  mk_int_ident "CASE_GUARDED_REM__________________" i.

Ltac2 check_case (i : int option) (p : pattern) :=
  let c' := hyp (mk_case_ident (Option.default 0 i)) in
  match! goal with
  | [h : MARK CASE_remember_str (?c = ?v) |- _] =>
      if Constr.equal c c'
      then
        let matches := Pattern.matches p v in
        List.iter (fun (i, v) => remember $v as $i) matches;
        clear $h
      else fail
  end.

Ltac2 Notation "case" p(pattern) i(opt(seq("as", tactic))) := check_case i p; unlock ().

Ltac2 switch_ (i : int option) (c : constr) :=
  lock;
  let id := mk_case_ident (Option.default 0 i) in
  let id_rem := mk_rem_ident (Option.default 0 i) in
  remember $c as $id eqn:$id_rem;
  let ih := hyp id_rem in
  try (rewrite $ih in * );
  apply mark_remember in $id_rem.

Ltac2 Notation "switch" c(constr) i(opt(seq("as", tactic))) := switch_ i c.
Ltac2 Notation "switch" "type" c(constr) i(opt(seq("as", tactic))) := switch_ i (find_h c None).


Ltac2 rewrite_hyp (h : ident) (cl : clause option) tac :=
  let cl := default_on_concl cl in
  first
    [ Std.rewrite
        false
        [{rew_orient := None; rew_repeat := Precisely 1; rew_equatn := fun () => (hyp h, NoBindings)}]
        cl
        tac
    | let {on_hyps:=oh;on_concl:=oc} := cl in
      Std.setoid_rewrite
        LTR
        (fun () => (hyp h, NoBindings))
        oc
        None;

      List.iter (fun (h, o, _) =>
                   Std.setoid_rewrite
                     LTR
                     (fun () => (hyp h, NoBindings))
                     o
                     (Some h)
        ) (Option.default [] oh)
    ].

Ltac2 rec match_rew (t0 : constr) (t1 : constr) : unit :=
  multi_match! t1 with
  | _ => unify $t0 $t1
  | ?f _ => match_rew t0 f
  | _ => fail
end.

Ltac2 get_rewrite_hyp (t : constr) : ident :=
  multi_match! goal with
  | [h : ?t' = _ |- _] =>
      match_rew t t'; h
  | [h : _ = ?t' |- _] =>
      match_rew t t'; h
  | [h : ?t' |- _] =>
      match_rew t t'; h
end.

Ltac2 hrewrite_ (t : constr) (cl : clause option) tac : unit :=
  let h := get_rewrite_hyp t in
  rewrite_hyp h cl tac.

Ltac2 Notation "hrewrite"
  t(open_constr)
  cl(opt(clause))
  tac(opt(seq("by", thunk(tactic)))) :=
  Control.once (fun _ => hrewrite_ t cl tac).
