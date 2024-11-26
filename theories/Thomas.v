

  Module ThomasNet.
    Parameter nat_Name : nat -> Name.
    Parameter Name_nat : Name -> nat.
    Axiom nat_Name_bij : forall n, nat_Name (Name_nat n) = n.
    Axiom Name_nat_bij : forall n, Name_nat (nat_Name n) = n.

    CoInductive Mover (N : PNet) : Name -> Prop :=
    | mover_ [n0 n1] : Mover N n0 -> net_lock_on N n0 n1 -> Mover N n1.

    CoFixpoint Echo : Proc :=
            PRecv (
                fun m =>
                  let (c, t) := m in
                  match t with
                  | R => None
                  | Q => Some (fun v => PSend (c, R) v Echo)
                  end
              ).

    Definition MoverFinger (self : Name) : Proc :=
      PRecv (
          fun m =>
            let (s, t) := m in
            match t with
            | Q => None
            | R => if S (Name_nat s) =? Name_nat self
                  then Some (fun v => PSend (nat_Name (S (Name_nat self)), R) v Echo)
                  else None
            end
        ).

    Definition MoverNail : Proc :=
      PSend (nat_Name 0, Q) some_val (MoverFinger (nat_Name 1)).


    Lemma Decisive_Echo : Decisive Echo.
      ltac1:(cofix C).
      unfold Echo.
      rewrite unfold_Proc.
      apply DecRecv; intros.
      - kill H.
        split; auto.
        intros.
        constructor.
        Guarded.
        assumption.
      - split; try (bullshit).
    Qed.

    Lemma SRPC_Echo : SRPC Free Echo.
      ltac1:(cofix C).
      unfold Echo in *.
      rewrite unfold_Proc.
      constructor; intros.
      - eexists.
        attac.
      - kill H.
        destruct n as [c [|]]; doubt.
        exists c, v.
        split; auto.
        hsimpl in *.
        constructor; intros; auto; doubt.
        + constructor; bullshit.
        + kill H.
          apply C.
    Qed.

    Lemma SRPC_Finger : forall n, SRPC (Lock (nat_Name (S (S n))) (nat_Name n)) (MoverFinger (nat_Name (S n))).
      intros.
      constructor; intros; doubt.
      - constructor; intros; doubt.
        + eexists; econstructor.
          rewrite Name_nat_bij in *.
          rewrite Name_nat_bij in *.
          rewrite PeanoNat.Nat.eqb_refl.
          attac.
        + kill H.
          exists v.
          destruct n0, t0; doubt.
          rewrite Name_nat_bij in *.
          destruct (Name_nat n0 =? n) eqn:?; doubt.
          rewrite PeanoNat.Nat.eqb_eq in Heqb; attac.
          now rewrite nat_Name_bij in *.
        + kill H.
          destruct n0, t0; doubt.
          rewrite Name_nat_bij in *.
          destruct (Name_nat n0 =? n) eqn:?; doubt.
          hsimpl in *.
          constructor; intros; doubt.
      - unfold MoverFinger in H.
        kill H.
        rewrite Name_nat_bij in *.
        destruct (Name_nat s =? n) eqn:?; doubt.
        rewrite PeanoNat.Nat.eqb_eq in Heqb.
        hsimpl in *.
        constructor; intros; doubt.
        1: constructor; intros; doubt; auto.
        kill H.
        apply SRPC_Echo.
    Qed.


    Lemma SRPC_Nail : SRPC (Work (nat_Name 2)) MoverNail.
      constructor; intros; doubt.
      - assert (SRPC (Lock (nat_Name 2) (nat_Name 0)) (MoverFinger (nat_Name 1)))
          by apply SRPC_Finger.

        constructor; intros; doubt.
        kill H; attac.
      - kill H; attac.
        apply SRPC_Finger.
    Qed.

    Lemma SRPC_sane_Echo : SRPC_pq_in_net Free (pq [] Echo []).
      constructor; intros; doubt.
      - auto using SRPC_Echo.
      - solve_mut_exclusive true; bullshit.
    Qed.

    Lemma SRPC_sane_Finger : forall n, SRPC_pq_in_net (Lock (nat_Name (S (S n))) (nat_Name n)) (pq [] (MoverFinger (nat_Name (S n))) []).
      intros.
      constructor; intros; doubt.
      - auto using SRPC_Finger.
      - solve_mut_exclusive true; bullshit.
    Qed.

    Lemma SRPC_sane_Nail : SRPC_pq_in_net (Work (nat_Name 2)) (pq [] MoverNail []).
      constructor; intros; doubt.
      - auto using SRPC_Nail.
      - solve_mut_exclusive true; bullshit.
    Qed.

    Example t_Net : {N : PNet | Mover N (nat_Name 1) /\ net_sane N}.
    pose (N := NetMod.init
         (
           fun n => (pq [] (
                      match Name_nat n with
                      | 0 => Echo
                      | S 0 => MoverNail
                      | n' => MoverFinger (nat_Name n')
                      end
                    ) [])
         )).
    exists N.

    assert (forall n, Decisive_q (NetMod.get n N)) as HD.
    {
      clear C.
      intros.
      subst N.
      rewrite NetMod.init_get.
      simpl.

      destruct (Name_nat n) eqn:?.
      - apply Decisive_Echo.
      - destruct n0; unfold MoverNail, MoverFinger.
        + constructor.
          constructor; attac.
          rewrite Name_nat_bij in *.
          destruct (Name_nat n0 =? 0); doubt.
          hsimpl in *.
          constructor.
          apply Decisive_Echo.
        + constructor; split; intros; auto; doubt.
          rewrite Name_nat_bij in *.
          destruct (S (Name_nat n1) =? S (S n0)); doubt.
          hsimpl in *.
          constructor.
          apply Decisive_Echo.
    }

    split.
    - enough (forall n, n <> 0 -> Mover N (nat_Name n)) by auto.
      ltac1:(cofix C).

      subst N.
      intros.
      constructor 1 with (n0:=(nat_Name (S n)))(n1:=(nat_Name n)); auto; doubt.
      unfold net_lock_on, net_lock.
      exists [nat_Name n].
      split. 1: attac.
      rewrite NetMod.init_get.

      constructor.
      + rewrite Name_nat_bij.
        destruct n; doubt.
        clear C H.
        revert n.
        ltac1:(cofix C).
        intros.
        specialize (HD (nat_Name (S (S n)))).
        rewrite NetMod.init_get in HD.
        rewrite Name_nat_bij in HD.
        constructor; split; intros; auto; doubt.
        rewrite Name_nat_bij in *.
        destruct (S (Name_nat n0) =? S (S n)) eqn:?; doubt.
        unfold MoverFinger in *.
        simpl in *.
        kill HD.
        rewrite Name_nat_bij in *.
        specialize (HDecR n0 P).
        rewrite Heqb in HDecR.
        specialize (HDecR H).
        attac.
      + rewrite Name_nat_bij.
        destruct n; doubt.
        constructor; auto.
        split; intros.
        * rewrite Name_nat_bij.
          kill H0.
          rewrite Name_nat_bij.
          rewrite PeanoNat.Nat.eqb_refl.
          attac.
        * rewrite Name_nat_bij in *.
          destruct (S (Name_nat n0) =? S (S n)) eqn:?; doubt.
          apply PeanoNat.Nat.eqb_eq in Heqb.
          hsimpl in * |-.
          constructor.
          rewrite <- Heqb.
          now rewrite nat_Name_bij.
      + bullshit.
    - assert (forall n, n <> 0 -> net_lock_on N (nat_Name (S n)) (nat_Name n)) as HL.
      {
        intros.
        exists [nat_Name n]; split; attac.
        unfold net_lock.
        destruct n; doubt. clear H.
        specialize (HD (nat_Name (S (S n)))).
        subst N.
        rewrite NetMod.init_get in *.
        rewrite Name_nat_bij in *.
        simpl in HD.
        constructor; auto.
        clear HD.
        constructor; split; intros; rewrite Name_nat_bij in *.
        - kill H.
          rewrite Name_nat_bij in *.
          rewrite PeanoNat.Nat.eqb_refl.
          attac.
        - destruct (S (Name_nat n0) =? S (S n)) eqn:?; doubt.
          apply PeanoNat.Nat.eqb_eq in Heqb.
          kill Heqb.
          rewrite nat_Name_bij. attac.
      }

      assert (forall n, n <> 0 -> pq_client (nat_Name (S n)) (NetMod.get (nat_Name n) N)) as HC.
      {
        intros.
        clear HL HD.
        subst N.
        rewrite NetMod.init_get.
        rewrite Name_nat_bij.
        destruct n; doubt. clear H.
        constructor 2.
        destruct n.
        - econstructor 1. apply SRPC_Nail.
        - econstructor 1. apply SRPC_Finger.
      }

      assert (forall n0 n1, net_lock_on N n1 n0 -> S (Name_nat n0) = (Name_nat n1) /\ Name_nat n0 <> 0) as HL'.
      {
        intros.
        subst N.
        unfold net_lock_on, net_lock in H.
        hsimpl in *.
        rewrite NetMod.init_get in *.
        kill H0.
        assert (AnySRPC (match Name_nat n1 with
                         | 0 => Echo
                         | 1 => MoverNail
                         | S (S n1) => MoverFinger (nat_Name (S (S n1)))
                         end)).
        {
          destruct (Name_nat n1).
          eexists; eauto using SRPC_Echo.
          destruct n; eexists; eauto using SRPC_Finger, SRPC_Nail.
        }
        assert (proc_lock [n0] (match Name_nat n1 with
                                | 0 => Echo
                                | 1 => MoverNail
                                | S (S n1) => MoverFinger (nat_Name (S (S n1)))
                                end)).
        {
          edestruct (SRPC_get_lock).
          apply H0.
          apply H2.
          enough (n0 = x) by (subst; auto).
          enough (List.In n0 [x]) by attac.
          apply (proc_lock_incl `(proc_lock L _)); auto.
        }
        destruct (Name_nat n1) eqn:?.
        - eapply lock_SRPC_Lock in H0.
          + hsimpl in *.
            absurd (Lock c n0 = Free); attac.
            eapply SRPC_inv; eauto using SRPC_Echo.
          + auto.
        - clear H2 H3.
          eapply lock_SRPC_Lock in H4. 2: auto.
          hsimpl in *.
          destruct n.
          + absurd (Lock c n0 = Work (nat_Name 2)); doubt.
            eapply SRPC_inv; eauto using SRPC_Nail.
          + assert (Lock c n0 = Lock (nat_Name (S (S (S n)))) (nat_Name (S n))); doubt.
            eapply SRPC_inv; eauto using SRPC_Finger.
            hsimpl in *.
            rewrite Name_nat_bij.
            attac.
      }

      assert (forall n0 n1, pq_client n1 (NetMod.get n0 N) -> S (Name_nat n0) = (Name_nat n1) /\ Name_nat n0 <> 0) as HC'.
      {
        intros.
        subst N.
        rewrite NetMod.init_get in *.
        kill H.
        kill H0; doubt.
        destruct (Name_nat n0) eqn:?; doubt.
        - absurd (Busy x = Free); attac.
          eapply SRPC_inv; eauto using SRPC_Echo.
        - destruct n.
          + split; attac.

            assert (SRPC (Work (nat_Name (2))) MoverNail) by auto using SRPC_Nail.
            apply (SRPC_inv H0) in H.
            hsimpl in *.
            now rewrite Name_nat_bij.
          + split; attac.
            assert (SRPC (Lock (nat_Name (S (S (S n)))) (nat_Name (S n))) (MoverFinger (nat_Name (S (S n))))) by auto using SRPC_Finger.
            apply (SRPC_inv H0) in H.
            hsimpl in *.
            now rewrite Name_nat_bij.
      }

      constructor.
      + intros n.
        subst N.
        rewrite NetMod.init_get.
        destruct (Name_nat n) eqn:?.
        * eexists; eapply SRPC_sane_Echo.
        * destruct n0 eqn:?.
          -- eexists; eapply SRPC_sane_Nail.
          -- eexists; eapply SRPC_sane_Finger.
      + intros n0 n1 HL0.
        apply HL' in HL0.
        hsimpl in *.
        specialize (HC (Name_nat n1) ltac:(auto)).
        rewrite <- HL0 in *.
        rewrite nat_Name_bij in *.
        rewrite nat_Name_bij in *.
        auto.
      + intros n0 n1 HC0.
        apply HC' in HC0.
        hsimpl in *.
        specialize (HL (Name_nat n1) ltac:(auto)).
        rewrite <- HC0 in *.
        rewrite nat_Name_bij in *.
        rewrite nat_Name_bij in *.
        auto.
    Qed.

  End ThomasNet.

