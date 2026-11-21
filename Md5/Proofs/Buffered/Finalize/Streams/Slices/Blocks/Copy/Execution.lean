import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy.Long
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy.Final
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy.Composition

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem part_execution {update : Bool} [Bindings] (kind : Kind) (part : Part) (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre (update := update) kind part)
      (codeRange ((kind.partEntry part (update := update))) (kind.partBytes part)) (partEffect (update := update) kind part) := by
  cases kind <;> cases part
  · exact longTail_high (update := update) boundary hOutside
  · exact longTail_low (update := update) boundary hOutside
  · exact longTail_arguments (update := update) boundary hOutside
  · exact finalBlock_high (update := update) boundary hOutside
  · exact finalBlock_low (update := update) boundary hOutside
  · exact finalBlock_arguments (update := update) boundary hOutside

theorem part_avoids_range {update : Bool} {kind : Kind} {part : Part} {s : RamState}
    (hs : Storage (streamKind update) s) :
    (partEffect (update := update) kind part s).Avoids (codeRange (kind.entry (update := update)) kind.bytes) := by
  have hr : RangeApart (stackPtr s + 104) kind.length (kind.entry (update := update)) kind.bytes.length := by
    cases update <;> cases kind
    · exact hs.stackApart (offset := 104) (len := 64) (codeOffset := 0x48d)
        (codeLen := 108) (by decide) (by decide +kernel)
    · exact hs.stackApart (offset := 104) (len := 56) (codeOffset := 0x555)
        (codeLen := 95) (by decide) (by decide +kernel)
    · exact hs.stackApart (offset := 104) (len := 64) (codeOffset := 0x1a3d)
        (codeLen := 108) (by decide) (by decide +kernel)
    · exact hs.stackApart (offset := 104) (len := 56) (codeOffset := 0x1b05)
        (codeLen := 95) (by decide) (by decide +kernel)
  intro x hx c hc ha
  obtain ⟨j, hj, hx⟩ := exists_of_mem_codeRange hx
  obtain ⟨i, hi, ha⟩ := effect_cover (update := update) (part_components (update := update) hc) ha
  exact hr i hi j hj (ha.symm.trans hx)

theorem part_full_execution {update : Bool} [Bindings] (kind : Kind) (part : Part)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre (update := update) kind part) (codeRange (kind.entry (update := update)) kind.bytes)
      (partEffect (update := update) kind part) := by
  intro s hReady hCode hPre
  have hBytes := hCode.mono (codeRange_slice_subset (kind.entry (update := update)) kind.bytes
    (kind.partOffset part) (kind.partLength part))
  obtain ⟨fuel, t, hRun, ht, _, he⟩ :=
    part_execution (update := update) kind part boundary hOutside s hReady hBytes hPre
  exact ⟨fuel, t, hRun, ht, he.codeIn (part_avoids_range (update := update) hPre.toStorage) hCode, he⟩

theorem execution {update : Bool} [Bindings] (kind : Kind) (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (RunPre (update := update) kind) (codeRange (kind.entry (update := update)) kind.bytes) (effect (update := update) kind) := by
  intro s hReady hCode h
  have hHighRip : s.RIP = (kind.partEntry .high (update := update)) := by
    simpa only [Kind.partEntry, Kind.partOffset, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h.rip
  obtain ⟨nHigh, u, hHighRun, hReadyU, hCodeU, hHigh⟩ :=
    part_full_execution (update := update) kind .high boundary hOutside s hReady hCode ⟨h.toStorage, hHighRip⟩
  have hStorageU := h.toStorage.of_agrees hHigh.agrees (part_rsp (update := update) hHigh)
  have hLowRip : u.RIP = (kind.partEntry .low (update := update)) := by
    cases update <;> cases kind <;> simpa [relocated, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset,
      Kind.partLength] using hHigh.rip
  obtain ⟨nLow, v, hLowRun, hReadyV, hCodeV, hLow⟩ :=
    part_full_execution (update := update) kind .low boundary hOutside u hReadyU hCodeU ⟨hStorageU, hLowRip⟩
  have hStorageV := hStorageU.of_agrees hLow.agrees (part_rsp (update := update) hLow)
  have hArgumentsRip : v.RIP = (kind.partEntry .arguments (update := update)) := by
    cases update <;> cases kind <;> simpa [relocated, partEffect, Kind.partEntry, Kind.entry, Kind.partOffset,
      Kind.partLength] using hLow.rip
  obtain ⟨nArguments, t, hArgumentsRun, hReadyT, hCodeT, hArguments⟩ :=
    part_full_execution (update := update) kind .arguments boundary hOutside v hReadyV hCodeV
      ⟨hStorageV, hArgumentsRip⟩
  exact ⟨nHigh + nLow + nArguments, t, (hHighRun.trans hLowRun).trans hArgumentsRun,
    hReadyT, hCodeT, effect_combine (update := update) hHigh hLow hArguments⟩

end Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy
