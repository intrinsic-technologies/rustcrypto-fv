import Md5.Proofs.Buffered.FinalizeReset.Export.Execution.Compose

namespace Md5.Proofs.Buffered.FinalizeReset.Export

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) {variant : Variant} :
    AdvancesBlock boundary (fun s ↦ RunPre s variant)
      (codeRange (variant.address 0x10091c) (bytes variant)) (fun s ↦ effect s variant) := by
  cases variant with
  | saved =>
      intro s hReady hCode hPre
      obtain ⟨nSave, u, hSave, hReadyU, hCodeU, hEffectU⟩ :=
        saveExecution boundary hOutside s hReady hCode ⟨hPre.toStorage, hPre.rip⟩
      obtain ⟨nReset, v, hReset, hReadyV, hCodeV, hEffectV⟩ :=
        resetExecution boundary hOutside (variant := .saved) u hReadyU hCodeU
          ⟨save_storage hPre.toStorage hEffectU, hEffectU.rip⟩
      obtain ⟨nCopy, t, hCopy, hReadyT, hCodeT, hEffectT⟩ :=
        copyExecution boundary hOutside (variant := .saved) v hReadyV hCodeV
          ⟨reset_storage (save_storage hPre.toStorage hEffectU) hEffectV, hEffectV.rip⟩
      have hFirst := hEffectU.seq (resetEffect_local (variant := .saved))
        (by simp [saveEffect, Write.Full, Operand.Full]) hEffectV
      have hAll := hFirst.seq (copyEffect_local (variant := .saved)) (by
        intro w hw
        x86_norm [saveEffect, resetEffect] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp [Write.Full, Operand.Full]) hEffectT
      exact ⟨nSave + nReset + nCopy, t, (hSave.trans hReset).trans hCopy,
        hReadyT, hCodeT, composed_effect hPre.toStorage hAll⟩
  | direct =>
      intro s hReady hCode hPre
      obtain ⟨nCopy, u, hCopy, hReadyU, hCodeU, hEffectU⟩ :=
        copyExecution boundary hOutside (variant := .direct) s hReady hCode ⟨hPre.toStorage, hPre.rip⟩
      obtain ⟨nReset, t, hReset, hReadyT, hCodeT, hEffectT⟩ :=
        resetExecution boundary hOutside (variant := .direct) u hReadyU hCodeU
          ⟨copy_storage hPre.toStorage hEffectU, hEffectU.rip⟩
      have hAll := hEffectU.seq (e₁ := fun s ↦ copyEffect s .direct)
        (resetEffect_local (variant := .direct))
        (by simp [copyEffect, Write.Full, Operand.Full]) hEffectT
      exact ⟨nCopy + nReset, t, hCopy.trans hReset,
        hReadyT, hCodeT, direct_composed_effect hPre.toStorage hAll⟩

end Md5.Proofs.Buffered.FinalizeReset.Export
