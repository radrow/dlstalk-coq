From DlStalk Require ModelData.
From DlStalk Require Network.
From DlStalk Require Compl.
From DlStalk Require Sound.

Require dpdgraph.dpdgraph.

Module Deps.
  Module DetConf <: Compl.DETECT_CONF.
    Parameter Val : Set.
    Declare Module NAME : ModelData.UsualDecidableSet.
    Declare Module NetMod : Network.NET_MOD(NAME).

    Module TAG := Locks.Tag_.
    Definition Msg := @Compl.MProbe' NAME.t'.
    Definition MState := @Compl.MState' NAME.t'.
  End DetConf.

  Module ComplMod := ModelData.Empty <+ Compl.COMPL(DetConf).
  Module SoundMod := ModelData.Empty <+ Sound.SOUND(DetConf).

  Module Correct.
    Definition compl := Deps.ComplMod.detection_completeness.
    Definition sound := Deps.SoundMod.detection_soundness.
    (* Definition correct := conj Deps.ComplMod.detection_completeness Deps.SoundMod.detection_soundness. *)
    Definition correct := conj sound compl.
  End Correct.
End Deps.

(* Check Deps.compl. *)
(* Check Deps.sound. *)


Set DependGraph File "../graphs/Transp_completeness.dpd".
Print DependGraph Deps.ComplMod.Transp.Mon.Transp_completeness.

Set DependGraph File "../graphs/Transp_soundness.dpd".
Print DependGraph Deps.ComplMod.Transp.Mon.Transp_soundness_base. (* todo, full *)


Set DependGraph File "../graphs/Net_Transp_completeness.dpd".
Print DependGraph Deps.ComplMod.Transp.Net_Transp_completeness.

Set DependGraph File "../graphs/Net_Transp_soundness.dpd".
Print DependGraph Deps.ComplMod.Transp.Net_Transp_soundness.


Set DependGraph File "../graphs/deadset_dep_self.dpd".
Print DependGraph Deps.ComplMod.SrpcNet.deadset_dep_self.

Set DependGraph File "../graphs/dep_self_deadset.dpd".
Print DependGraph Deps.ComplMod.SrpcNet.dep_self_deadset.


Set DependGraph File "../graphs/trans_invariant_net_sane.dpd".
Print DependGraph Deps.ComplMod.SrpcNet.trans_invariant_net_sane.


Set DependGraph File "../graphs/KIC.dpd".
Print DependGraph Deps.ComplMod.KIC_invariant.

Set DependGraph File "../graphs/KIS.dpd".
Print DependGraph Deps.SoundMod.KIS_invariant.


Set DependGraph File "../graphs/compl.dpd".
Print DependGraph Deps.ComplMod.detection_completeness.

Set DependGraph File "../graphs/sound.dpd".
Print DependGraph Deps.SoundMod.detection_soundness.


Set DependGraph File "../graphs/correctness.dpd".
Print DependGraph Deps.Correct.correct.

(* Set DependGraph File "modules.dpd". *)
(* Print FileDependGraph Deps. *)
