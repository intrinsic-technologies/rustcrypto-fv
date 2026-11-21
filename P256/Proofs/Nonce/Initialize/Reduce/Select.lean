import P256.Proofs.Nonce.Initialize.Reduce.Select.Result

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Reduce

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem select_correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original difference : Nat} {select : Bool}
    (pre : InitializePre initial boundary orderAddress)
    (state : SelectionReady initial s boundary original difference select) :
    ∃ t, Selected initial t boundary (if select then original else difference) := by
  obtain ⟨entry, run, ready, effect⟩ := ScalarFrame.scalar_call pre.toCalleePre
    (by decide) (by decide) state.stage.toFrameState 0x7b57 0x11664
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x191c0 (by decide)) state.rip
  change (callEffect (fun _ => 0x1191c0) 0x107b5c s).Holds s entry at effect
  have frame : Stage initial entry boundary 288 := by
    obtain ⟨fuel, execution⟩ := state.stage.execution
    exact ⟨state.stage.toFrameState.after_call pre.toCalleePre (by decide) (by decide)
      ready effect, fuel + 1, execution.trans run⟩
  have choice : entry.regValue .r8 = if select then 1 else 0 :=
    (effect.agrees.read (n := 64) (r := 8) (by simp [pushEffect_components])).trans state.choice
  obtain ⟨t, result, selected⟩ := LimbSelect.limb_select32_correct
    (selection_pre pre state frame effect) choice
  exact ⟨t, selection_result pre state frame effect result selected⟩

end P256.Proofs.Nonce.Initialize.Reduce
