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

  Module Sound := ModelData.Empty <+ Sound.SOUND(DetConf).
  Module Compl := Sound. (* TODO fix separation *)
  (* Module Compl := ModelData.Empty <+ Compl.COMPL(DetConf). *)

  Module Correct.
    Definition compl := Deps.Compl.detection_completeness.
    Definition sound := Deps.Sound.detection_soundness.
    (* Definition correct := conj Deps.Compl.detection_completeness Deps.Sound.detection_soundness. *)
    Definition correct := conj sound compl.
  End Correct.
End Deps.

(* Check Deps.compl. *)
(* Check Deps.sound. *)


Set DependGraph File "../graphs/Transp_completeness.dpd".
Print DependGraph Deps.Compl.Transp.Mon.Transp_completeness.

Set DependGraph File "../graphs/Transp_soundness.dpd".
Print DependGraph Deps.Compl.Transp.Mon.Transp_soundness_base. (* todo, full *)


Set DependGraph File "../graphs/transp_complete.dpd".
Print DependGraph Deps.Compl.Transp.transp_complete.

Set DependGraph File "../graphs/transp_sound_instr.dpd".
Print DependGraph Deps.Compl.Transp.transp_sound_instr.


Set DependGraph File "../graphs/deadset_dep_self.dpd".
Print DependGraph Deps.Compl.SrpcNet.deadset_dep_self.

Set DependGraph File "../graphs/dep_self_deadset.dpd".
Print DependGraph Deps.Compl.SrpcNet.dep_self_deadset.


Set DependGraph File "../graphs/trans_invariant_well_formed.dpd".
Print DependGraph Deps.Compl.SrpcNet.trans_invariant_well_formed.


Set DependGraph File "../graphs/KIC.dpd".
Print DependGraph Deps.Compl.KIC_invariant.

Set DependGraph File "../graphs/KIS.dpd".
Print DependGraph Deps.Sound.KIS_invariant.


Set DependGraph File "../graphs/compl.dpd".
Print DependGraph Deps.Compl.detection_completeness.

Set DependGraph File "../graphs/sound.dpd".
Print DependGraph Deps.Sound.detection_soundness.


Set DependGraph File "../graphs/correctness.dpd".
Print DependGraph Deps.Correct.correct.

Module Preview.
  Import Deps.
  Import Sound.
  Import LTS.
  Import Que.
  Import Mon.
  Import Srpc.
  Import Compl.
  Import SrpcNet.
  Check Transp_completeness.
  Check Transp_soundness_base.
  Check transp_complete.
  Check transp_sound_instr.
  Check deadset_dep_self.
  Check dep_self_deadset.
(* Set DependGraph File "modules.dpd". *)
(* Print FileDependGraph Deps. *)
