From Coq Require Import Structures.Equalities.

Require Import DlStalk.Tactics.

Close Scope nat.

Module Empty. End Empty. (* `<+` identity *)


Module Type UsualDecidableSet.
  Parameter t' : Set.
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

  #[global] Hint Rewrite -> eqb_eq eqb_neq_inv using spank : LTS LTS_concl.
  #[global] Hint Rewrite -> same_eqb_inv neq_neqb_inv using spank : LTS LTS_concl.

  #[global] Hint Resolve eq_dec eqb_eq same_eqb_inv : LTS.
End UsualDecidableSetHints.


Module Type CHANNEL_CONF.
  Parameter Val : Set.

  Declare Module NAME : UsualDecidableSet.
  Declare Module TAG : UsualDecidableSet.
End CHANNEL_CONF.

Module Type CHANNEL_PARAMS(Conf : CHANNEL_CONF).
End CHANNEL_PARAMS.

Module Type CHANNEL_F(Import Conf : CHANNEL_CONF)(Import Params : CHANNEL_PARAMS(Conf)).
  #[global] Definition Name := NAME.t'.
  #[global] Definition Tag := TAG.t'.

  #[global] Hint Transparent Name Tag : core.
  #[global] Hint Unfold Name Tag : core.

  Definition Name_t_t' : NAME.t -> NAME.t'.
    intros. apply X. Defined.
  #[global] Coercion Name_t_t' : NAME.t >-> NAME.t'.
  Definition Name_t'_t : NAME.t' -> NAME.t.
    intros. apply H. Defined.
  #[global] Coercion Name_t'_t : NAME.t' >-> NAME.t.
  Definition Name_t' : Name -> NAME.t'.
    intros. apply H. Defined.
  #[global] Coercion Name_t' : Name >-> NAME.t'.
  Definition Name_'t : NAME.t' -> Name.
    intros. apply H. Defined.
  #[global] Coercion Name_'t : NAME.t' >-> Name.

  #[global] Definition NChan : Set := (Name * Tag)%type.
  #[global] Hint Transparent NChan : core.
  (* TODO understand and fix this crap above *)

  Fact NChan_eq_dec : forall (n0 n1 : NChan), {n0 = n1} + {n0 <> n1}.

  Proof.
    intros.
    destruct n0; destruct n1.
    destruct (NAME.eq_dec n n0); destruct (TAG.eq_dec t t0);
      subst; first [left; now auto | right; congruence].
  Qed.


  Lemma NChan_neq_Name_inv : forall [n0 n1 : Name] [t0 t1 : Tag],
      n0 <> n1 ->
      (n0, t0) <> (n1, t1).
  Proof. attac. Qed.

  Lemma NChan_neq_Tag_inv : forall [n0 n1 : Name] [t0 t1 : Tag],
      t0 <> t1 ->
      (n0, t0) <> (n1, t1).
  Proof. attac. Qed.

  #[export] Hint Resolve NChan_neq_Name_inv NChan_neq_Tag_inv : core. (* fuck coq *)


  Class gen_Act (Act : Set) :=
    {
      Payload : Set;
      send : NChan -> Payload -> Act;
      recv : NChan -> Payload -> Act;
      ia : Act -> Prop;

      ia_disjoint : forall n v, not (ia (recv n v)) /\ not (ia (send n v));
      send_recv : forall n v, send n v <> recv n v;

      gact_rec : forall [P : Act -> Type] (a : Act),
                   (forall (nc : NChan) (v : Payload), P (send nc v)) ->
                   (forall (nc : NChan) (v : Payload), P (recv nc v)) ->
                   (ia a -> P a) ->
                   P a
    }.


  Module Export NAME_H := UsualDecidableSetHints(NAME).
  Module Export TAG_H := UsualDecidableSetHints(TAG).
End CHANNEL_F.

Module Type CHANNEL(Conf : CHANNEL_CONF) := Conf <+ CHANNEL_PARAMS <+ CHANNEL_F.
