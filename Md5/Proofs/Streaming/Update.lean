import Md5.Proofs.Streaming.Invariant
import Md5.Proofs.Buffered.Update.Memory

namespace Md5.Proofs.Streaming

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Buffered

theorem loopStorage_aligned {kind : LoopKind.Kind} {initial s : RamState}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind)) :
    (stackPtr s).toNat % 16 = 0 := by
  have hu : LoopKind.budget kind ≤ (stackPtr initial).toNat := hs.2.2.1
  have ha : (stackPtr initial).toNat % 16 = 8 := hs.2.2.2
  rw [loopStorage_toNat h hs]
  rw [LoopKind.budget_eq] at hu
  cases kind <;> change ((_ - _) % 16 = 0) <;> simp only [LoopKind.frame] at * <;> omega

theorem loopStorage_context_address {kind : LoopKind.Kind} {initial s : RamState}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind)) :
    (kind.context s).toNat = (stackPtr s).toNat + kind.contextOffset :=
  loopStorage_address h hs (by cases kind <;> decide +kernel)

theorem loopStorage_scratch_contains {kind : LoopKind.Kind} {initial s : RamState}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind))
    {address : Nat} (ha : (UpdateKind.scratchRegion s).Contains address) :
    (Stack.region initial (LoopKind.budget kind)).Contains address := by
  rw [loopStorage_region h hs]
  change (stackPtr s).toNat - 320 ≤ address ∧
    address < (stackPtr s).toNat - 320 + (LoopKind.frame kind + 376)
  change (stackPtr s).toNat - 320 ≤ address ∧ address < (stackPtr s).toNat - 320 + 320 at ha
  constructor <;> omega

theorem loopStorage_context_contains {kind : LoopKind.Kind} {initial s : RamState}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind))
    {address : Nat} (ha : (kind.contextRegion s).Contains address) :
    (Stack.region initial (LoopKind.budget kind)).Contains address := by
  have hlo := (loopStorage_bounds h hs).1
  have hc : kind.contextOffset + 88 ≤ LoopKind.frame kind + 56 := by
    cases kind <;> decide +kernel
  rw [loopStorage_region h hs]
  change (stackPtr s).toNat - 320 ≤ address ∧
    address < (stackPtr s).toNat - 320 + (LoopKind.frame kind + 376)
  change (kind.context s).toNat ≤ address ∧ address < (kind.context s).toNat + 88 at ha
  rw [loopStorage_context_address h hs] at ha
  constructor <;> omega

theorem LoopInvariant.updatePre [bindings : Bindings] {kind : LoopKind.Kind}
    {boundary : ReturnBoundary} {initial s t : RamState} {inputs : Array Slices.Input}
    {start finish index : Nat} (h : LoopInvariant kind initial inputs start finish index s)
    (hInputs : Slices.ValidInputs initial inputs)
    (hStack : Stack.Valid initial (LoopKind.budget kind))
    (hSep : MemorySeparation
      (LoopKind.writable kind initial)
      (Slices.readRegions initial inputs))
    (hStride : UnitStringStride bindings) (hOutside : ¬ InProgram boundary.rip)
    (hStart : start ≤ index) (hi : index < inputs.size)
    (hReady : ReadyToStep t) (hCode : CodeIn Extracted.programImage t)
    (he : (LoopKind.loadEffect kind s).Holds s t) :
    UpdatePre kind boundary (Slices.message (inputs.extract start index)) inputs[index].bytes t := by
  have hsp := loadEffect_rsp he
  have hm := loadEffect_external he
  have hc : kind.context t = kind.context s := by simp only [UpdateKind.context, hsp]
  have hcr : kind.contextRegion t = kind.contextRegion s := by simp only [UpdateKind.contextRegion, hc]
  have hsr : UpdateKind.scratchRegion t = UpdateKind.scratchRegion s :=
    congrArg (fun a : BitVec 64 ↦ (⟨a.toNat - 320, 320⟩ : MemoryRegion)) hsp
  have hir : kind.inputRegion t inputs[index].bytes = inputs[index].region := by
    simp only [UpdateKind.inputRegion, h.load_pointer hInputs hSep hi he, Slices.Input.region]
  have hsc := @loopStorage_scratch_contains kind initial s h.storage hStack
  have hcc := @loopStorage_context_contains kind initial s h.storage hStack
  have halloc : (Stack.region initial (LoopKind.budget kind)).Allocated t.external := by
    intro a ha
    rw [hm]
    exact Option.isSome_iff_exists.mp (h.grows a
      (Option.isSome_iff_exists.mpr (hStack.2.1 a ha)))
  have hsep := (hSep.2 (Stack.region initial (LoopKind.budget kind))
    (LoopKind.stack_mem_writable kind initial)).1
  have havoid := (hSep.2 (Stack.region initial (LoopKind.budget kind))
    (LoopKind.stack_mem_writable kind initial)).2
  have hinputSep := hsep inputs[index].region (by
    simp only [Slices.readRegions, List.mem_cons, Array.mem_toList_iff, Array.mem_map]
    exact .inr (.inr ⟨inputs[index], Array.getElem_mem hi, rfl⟩))
  refine ⟨hStride, hReady, hCode,
    he.agrees.directionFlagClear
      (by simp [LoopKind.loadEffect, sliceLoadEffect, Effect.components]) h.df, he.rip,
    hOutside, ?_, ?_, ?_, h.load_length hInputs hSep hi he, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc]
    exact absorbed_of_external_eq h.absorbed hm
  · rw [hir, hm]
    exact validInputs_bytes_preserved hInputs h.memoryFrame
      (fun r hr ↦ (hSep.2 r hr).1) ⟨index, hi⟩
  · rw [hir]
    exact (hInputs.slicesValid ⟨index, hi⟩).2.2.2.1
  · have hb := validInputs_message_extract_size_lt hInputs start (index + 1)
    rw [message_extract_succ inputs start index hStart hi, ByteArray.size_append] at hb
    omega
  · rw [hsp]
    exact (loopStorage_bounds h.storage hStack).1
  · rw [hsp]
    have hb := (loopStorage_bounds h.storage hStack).2
    have ho : kind.contextOffset + 88 ≤ LoopKind.frame kind + 56 := by
      cases kind <;> decide +kernel
    omega
  · rw [hsp]
    exact loopStorage_aligned h.storage hStack
  · rw [hsr]
    exact fun a ha ↦ halloc a (hsc ha)
  · rw [hcr]
    exact fun a ha ↦ halloc a (hcc ha)
  · rw [hir, hsr]
    exact fun a ha hb ↦ hinputSep a ha (hsc hb)
  · rw [hir, hcr]
    exact fun a ha hb ↦ hinputSep a ha (hcc hb)
  · rw [hsr]
    exact fun a ha ↦ havoid a (hsc ha)
  · rw [hcr]
    exact fun a ha ↦ havoid a (hcc ha)
  · intro hk
    obtain ⟨h3, h15⟩ := h.secondRegisters hk
    rcases hk with hk | hk
    all_goals
      subst kind
      rw [hc]
      constructor
      · exact (he.agrees.read (n := 64) (r := 3) (by
          simp [LoopKind.loadEffect, sliceLoadEffect, Effect.components,
            UpdateKind.inputRegister, UpdateKind.sizeRegister])).trans h3
      · exact (he.agrees.read (n := 64) (r := 15) (by
          simp [LoopKind.loadEffect, sliceLoadEffect, Effect.components,
            UpdateKind.inputRegister, UpdateKind.sizeRegister])).trans h15
  · intro hk
    have h15 := h.discardSecondMemcpy hk
    subst kind
    exact (he.agrees.read (n := 64) (r := 15) (by
      simp [LoopKind.loadEffect, sliceLoadEffect, Effect.components,
        UpdateKind.inputRegister, UpdateKind.sizeRegister])).trans h15


end Md5.Proofs.Streaming
