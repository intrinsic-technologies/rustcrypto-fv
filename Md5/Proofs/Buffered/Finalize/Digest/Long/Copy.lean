import Md5.Proofs.Buffered.Finalize.Digest.Long.Copy.High
import Md5.Proofs.Buffered.Finalize.Digest.Long.Copy.Low
import Md5.Proofs.Buffered.Finalize.Digest.Long.Copy.Arguments
import Md5.Proofs.Buffered.Finalize.Digest.Long.Copy.Composition

namespace Md5.Proofs.Buffered.Finalize.Digest.Long.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem part_execution [Bindings] (part : Part) (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre part)
      (codeRange part.entry part.bytes) (partEffect part) := by
  cases part
  · exact high_execution boundary hOutside
  · exact low_execution boundary hOutside
  · exact arguments_execution boundary hOutside

theorem part_run [Bindings] (part : Part) {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hStorage : Storage .digest s) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = part.entry) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (partEffect part s).Holds s t := by
  have hBytes : CodeIn (codeRange part.entry part.bytes) s := by
    cases part
    · exact program_text_slice hCode 0x12a 52 (by decide +kernel)
    · exact program_text_slice hCode 0x15e 46 (by decide +kernel)
    · exact program_text_slice hCode 0x18c 15 (by decide +kernel)
  obtain ⟨fuel, t, hRun, hReady', _, hEffect⟩ :=
    part_execution part boundary hOutside s hReady hBytes ⟨hStorage, hRip⟩
  exact ⟨fuel, t, hRun, hReady', hEffect.codeIn (part_avoids hStorage) hCode, hEffect⟩

theorem run [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hStorage : Storage .digest s) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = 0x10012a) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect s).Holds s t := by
  obtain ⟨nHigh, u, hHighRun, hReadyU, hCodeU, hHigh⟩ :=
    part_run .high hReady hCode hStorage hOutside hRip
  have hStorageU := hStorage.of_agrees hHigh.agrees (part_rsp hHigh)
  have hLowRip : u.RIP = Part.entry .low := by
    simpa [partEffect, Part.entry, Part.offset, Part.length] using hHigh.rip
  obtain ⟨nLow, v, hLowRun, hReadyV, hCodeV, hLow⟩ :=
    part_run .low hReadyU hCodeU hStorageU hOutside hLowRip
  have hStorageV := hStorageU.of_agrees hLow.agrees (part_rsp hLow)
  have hArgumentsRip : v.RIP = Part.entry .arguments := by
    simpa [partEffect, Part.entry, Part.offset, Part.length] using hLow.rip
  obtain ⟨nArguments, t, hArgumentsRun, hReadyT, hCodeT, hArguments⟩ :=
    part_run .arguments hReadyV hCodeV hStorageV hOutside hArgumentsRip
  exact ⟨nHigh + nLow + nArguments, t, (hHighRun.trans hLowRun).trans hArgumentsRun,
    hReadyT, hCodeT, effect_combine hHigh hLow hArguments⟩

end Md5.Proofs.Buffered.Finalize.Digest.Long.Copy
