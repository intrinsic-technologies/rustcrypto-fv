import Md5.Proofs.Buffered.FinalizeReset.Copy.Execution
import Md5.Proofs.Buffered.FinalizeReset.Copy.Composition
import Md5.Proofs.Buffered.FinalizeReset.Copy.Result

namespace Md5.Proofs.Buffered.FinalizeReset.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem part_run {variant : Variant} [Bindings] (kind : Kind) (part : Part) {s : RamState}
    {boundary : ReturnBoundary} (hReady : ReadyToStep s)
    (hCode : CodeIn Extracted.programImage s) (hStorage : Storage s variant)
    (hOutside : ¬ InProgram boundary.rip) (hRip : s.RIP = kind.partEntry part variant) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (partEffect kind part s variant).Holds s t := by
  have hBytes : CodeIn (codeRange (kind.partEntry part variant) (kind.partBytes part)) s := by
    cases variant
    case saved =>
      cases kind <;> cases part
      · exact program_text_slice hCode 0x7f0 52 (by decide +kernel)
      · exact program_text_slice hCode 0x824 40 (by decide +kernel)
      · exact program_text_slice hCode 0x84c 18 (by decide +kernel)
      · exact program_text_slice hCode 0x8b6 39 (by decide +kernel)
      · exact program_text_slice hCode 0x8dd 40 (by decide +kernel)
      · exact program_text_slice hCode 0x905 18 (by decide +kernel)
    case direct =>
      cases kind <;> cases part
      · exact program_text_slice hCode 0xea0 52 (by decide +kernel)
      · exact program_text_slice hCode 0xed4 40 (by decide +kernel)
      · exact program_text_slice hCode 0xefc 18 (by decide +kernel)
      · exact program_text_slice hCode 0xf66 39 (by decide +kernel)
      · exact program_text_slice hCode 0xf8d 40 (by decide +kernel)
      · exact program_text_slice hCode 0xfb5 18 (by decide +kernel)
  obtain ⟨fuel, t, hRun, hReady', _, hEffect⟩ :=
    part_execution kind part boundary hOutside s hReady hBytes ⟨hStorage, hRip⟩
  exact ⟨fuel, t, hRun, hReady', hEffect.codeIn (part_avoids hStorage) hCode, hEffect⟩

theorem run {variant : Variant} [Bindings] (kind : Kind) {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s) (hStorage : Storage s variant)
    (hOutside : ¬ InProgram boundary.rip) (hRip : s.RIP = kind.entry variant) :
    ∃ fuel t, Advances boundary fuel s t ∧ Result kind s t variant := by
  have hHighRip : s.RIP = kind.partEntry .high variant := by
    cases variant <;> cases kind <;> simpa [Variant.address, Kind.partEntry, Kind.entry, Kind.partOffset] using hRip
  obtain ⟨nHigh, u, hHighRun, hReadyU, hCodeU, hHigh⟩ :=
    part_run kind .high hReady hCode hStorage hOutside hHighRip
  have hStorageU := agrees_storage hStorage (part_agrees hHigh)
  have hLowRip : u.RIP = kind.partEntry .low variant := by
    cases variant <;> cases kind <;> simpa [Variant.address, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset,
      Kind.partLength] using hHigh.rip
  obtain ⟨nLow, v, hLowRun, hReadyV, hCodeV, hLow⟩ :=
    part_run kind .low hReadyU hCodeU hStorageU hOutside hLowRip
  have hStorageV := agrees_storage hStorageU (part_agrees hLow)
  have hArgumentsRip : v.RIP = kind.partEntry .arguments variant := by
    cases variant <;> cases kind <;> simpa [Variant.address, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset,
      Kind.partLength] using hLow.rip
  obtain ⟨nArguments, t, hArgumentsRun, hReadyT, hCodeT, hArguments⟩ :=
    part_run kind .arguments hReadyV hCodeV hStorageV hOutside hArgumentsRip
  have hEffect := effect_combine hHigh hLow hArguments
  have hArgs := effect_arguments hEffect
  exact ⟨nHigh + nLow + nArguments, t, (hHighRun.trans hLowRun).trans hArgumentsRun,
    ⟨hReadyT, hCodeT, hEffect.rip, effect_rsp hEffect, hArgs.1, hArgs.2.1, hArgs.2.2,
      effect_copy hStorage hEffect, effect_agrees hEffect, hEffect⟩⟩

end Md5.Proofs.Buffered.FinalizeReset.Copy
