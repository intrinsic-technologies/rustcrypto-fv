import Md5.Proofs.Streaming.Epilogue
import Md5.Proofs.Streaming.Invariant

namespace Md5.Proofs.Streaming

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def EpilogueKind.loopKind : EpilogueKind → LoopKind.Kind
  | .slices => .slices
  | .updateFinalizeInto => .updateFinalizeInto
  | .resetSecond => .resetSecond
  | .finalizeResetSecond => .finalizeResetSecond
  | .resetDiscardSecond => .resetDiscardSecond

private theorem epilogue_frame (kind : EpilogueKind) :
    LoopKind.frame kind.loopKind = kind.frame := by
  cases kind <;> rfl

private theorem epilogue_stack_contains {kind : EpilogueKind} {initial s : RamState}
    (h : LoopKind.storage kind.loopKind initial s)
    (hs : Stack.Valid initial (LoopKind.budget kind.loopKind))
    {offset len i : Nat} (ho : offset + len ≤ kind.frame + 56) (hi : i < len) :
    (Stack.region initial (LoopKind.budget kind.loopKind)).Contains
      (stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
  rw [add_ofNat_add_ofNat, loopStorage_address h hs (by rw [epilogue_frame]; omega),
    loopStorage_region h hs]
  have hlo := (loopStorage_bounds h hs).1
  change (stackPtr s).toNat - 320 ≤ (stackPtr s).toNat + (offset + i) ∧
    (stackPtr s).toNat + (offset + i) <
      (stackPtr s).toNat - 320 + (LoopKind.frame kind.loopKind + 376)
  rw [epilogue_frame]
  omega

private theorem epilogue_output_address {kind : EpilogueKind} {initial : RamState}
    (hb : (LoopKind.outputRegion kind.loopKind initial).Bounded) :
    (initial.regValue (LoopKind.outputRegister kind.loopKind) +
      BitVec.ofNat 64 kind.outputOffset).toNat =
        (LoopKind.outputRegion kind.loopKind initial).start + kind.outputOffset := by
  cases kind <;>
    change (initial.regValue _ + BitVec.ofNat 64 _).toNat = _ <;>
    simp only [EpilogueKind.outputOffset, EpilogueKind.loopKind, LoopKind.outputRegister,
      LoopKind.outputRegion, OneMessage.outputRegion, OneMessage.digestSlices, OneMessage.updateFinalizeInto, TwoMessages.outputRegion, TwoMessages.digestSlicesReset, TwoMessages.finalizeIntoResetSlices,
      ResetThenDigest.outputRegion, ResetThenDigest.updateResetSlices,
      registerRegion] at *
  all_goals first
    | change (initial.regValue .r8).toNat + 32 < 2^32 at hb
      rw [toNat_add_ofNat _ _ (by omega)]
    | simp

section

variable [bindings : Bindings] {kind : EpilogueKind} {initial s : RamState}
  {digest : Vector UInt8 16}

theorem epiloguePre_of_storage
    (hInitial : ReadyToStep initial)
    (hStack : Stack.Valid initial (LoopKind.budget kind.loopKind))
    (hOutput : (LoopKind.outputRegion kind.loopKind initial).Bounded ∧
      (LoopKind.outputRegion kind.loopKind initial).Allocated initial.external)
    (hSep : MemorySeparation
      #v[LoopKind.outputRegion kind.loopKind initial, Stack.region initial (LoopKind.budget kind.loopKind)]
      [])
    (hReturn : ValidReturnAddress bindings initial)
    (hStorage : LoopKind.storage kind.loopKind initial s)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hDF : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS)
    (hGrows : ∀ address : BitVec 64,
      (initial.external[address]?).isSome → (s.external[address]?).isSome)
    (hRip : s.RIP = kind.entry)
    (hDigest : (⟨(stackPtr s).toNat + kind.source, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨digest.toArray⟩) :
    EpiloguePre kind initial (returnBoundary initial) digest
      (initial.regValue (LoopKind.outputRegister kind.loopKind) +
        BitVec.ofNat 64 kind.outputOffset) s := by
  have hstackAvoid := (hSep.2 (Stack.region initial (LoopKind.budget kind.loopKind)) (by simp)).2
  have houtAvoid := (hSep.2 (LoopKind.outputRegion kind.loopKind initial) (by simp)).2
  have hsize : kind.outputOffset + 16 = (LoopKind.outputRegion kind.loopKind initial).size := by
    cases kind <;> rfl
  have houtNat := epilogue_output_address hOutput.1
  have houtContains (i : Nat) (hi : i < 16) :
      (LoopKind.outputRegion kind.loopKind initial).Contains
        (initial.regValue (LoopKind.outputRegister kind.loopKind) +
          BitVec.ofNat 64 kind.outputOffset + BitVec.ofNat 64 i).toNat := by
    apply region_contains_offset (len := 16) hOutput.1
    · rw [houtNat]
      omega
    · rw [houtNat, ← hsize]
      omega
    · exact hi
  have hreturn := nearReturn64Boundary_eq initial hInitial.dataReady hInitial.cpu.ss
    (stack_return_readable hStack)
  obtain ⟨boundary, hboundary, hlow, houtside⟩ := hReturn
  rw [hreturn] at hboundary
  cases hboundary
  refine ⟨hReady, hCode, ⟨hRip, ?_, ?_⟩, ?_, ?_, ?_, hDigest, ?_, ?_, ?_, hlow,
    houtside, hDF⟩
  · simpa only [BitVec.add_zero, epilogue_frame] using
      loopStorage_readable hStorage hStack hGrows 0 (kind.frame + 56)
        (by rw [epilogue_frame]; omega)
  · refine ⟨?_, ?_, ?_⟩
    · exact loopStorage_readable hStorage hStack hGrows (kind.frame - 16) 16
        (by rw [epilogue_frame]; omega)
    · intro i hi hin
      exact hstackAvoid _ (epilogue_stack_contains hStorage hStack (by omega) hi) (.inr hin)
    · intro i hi hin
      exact hstackAvoid _ (epilogue_stack_contains hStorage hStack (by omega) hi) (.inl hin)
  · have hslot : LoopKind.outputOffset kind.loopKind = kind.outputSlot := by
      cases kind <;> rfl
    rw [← hslot, hStorage.output]
  · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have hb := hOutput.1
      change (LoopKind.outputRegion kind.loopKind initial).start +
        (LoopKind.outputRegion kind.loopKind initial).size < 2^32 at hb
      rw [← hsize] at hb
      rw [houtNat]
      omega
    · intro i hi
      exact hGrows _ (Option.isSome_iff_exists.mpr (hOutput.2 _ (houtContains i hi)))
    · intro i hi hin
      exact houtAvoid _ (houtContains i hi) (.inr hin)
    · intro i hi hin
      exact houtAvoid _ (houtContains i hi) (.inl hin)
  · intro i hi j hj heq
    have hd := hSep.1 (0 : Fin 2) (1 : Fin 2) (by decide +kernel)
    apply hd _ (houtContains i hi)
    change (Stack.region initial (LoopKind.budget kind.loopKind)).Contains _
    rw [heq]
    simpa only [BitVec.add_zero] using
      epilogue_stack_contains hStorage hStack (offset := 0) (len := kind.frame + 56)
        (by omega) hj
  · simpa only [epilogue_frame] using hStorage.saved
  · simpa only [epilogue_frame, returnBoundary] using hStorage.returnSlot
  · change stackPtr s + BitVec.ofNat 64 (kind.frame + 56) = stackPtr initial + 8
    rw [hStorage.rsp, epilogue_frame]
    have he : BitVec.ofNat 64 (kind.frame + 56) = BitVec.ofNat 64 (48 + kind.frame) + 8 := by
      change BitVec.ofNat 64 (kind.frame + 56) =
        BitVec.ofNat 64 (48 + kind.frame) + BitVec.ofNat 64 8
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    rw [he, ← BitVec.add_assoc, BitVec.sub_add_cancel]

end

theorem slices_epiloguePre [bindings : Bindings] {initial s : RamState}
    {inputs : Array Slices.Input} {digest : Vector UInt8 16}
    (hCall : (OneMessage.ValidCall OneMessage.digestSlices) bindings initial inputs) (hInitial : ReadyToStep initial)
    (hStorage : LoopKind.storage .slices initial s)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hDF : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS)
    (hGrows : ∀ address : BitVec 64,
      (initial.external[address]?).isSome → (s.external[address]?).isSome)
    (hRip : s.RIP = 0x1005b9)
    (hDigest : (⟨(stackPtr s).toNat, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨digest.toArray⟩) :
    EpiloguePre .slices initial (returnBoundary initial) digest (initial.regValue .rcx) s := by
  have h := epiloguePre_of_storage (kind := .slices) hInitial hCall.stackAvailable
    hCall.outputInMemory.2 hCall.outputSeparation hCall.returnAddress hStorage hReady hCode hDF
    hGrows hRip (by simpa only [EpilogueKind.source, Nat.add_zero] using hDigest)
  simpa only [EpilogueKind.loopKind, LoopKind.outputRegister, EpilogueKind.outputOffset,
    BitVec.add_zero] using h

theorem updateFinalizeInto_epiloguePre [bindings : Bindings] {initial s : RamState}
    {inputs : Array Slices.Input} {digest : Vector UInt8 16}
    (hCall : (OneMessage.ValidCall OneMessage.updateFinalizeInto) bindings initial inputs) (hInitial : ReadyToStep initial)
    (hStorage : LoopKind.storage .updateFinalizeInto initial s)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hDF : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS)
    (hGrows : ∀ address : BitVec 64,
      (initial.external[address]?).isSome → (s.external[address]?).isSome)
    (hRip : s.RIP = 0x101b69)
    (hDigest : (⟨(stackPtr s).toNat, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨digest.toArray⟩) :
    EpiloguePre .updateFinalizeInto initial (returnBoundary initial) digest (initial.regValue .rcx) s := by
  have h := epiloguePre_of_storage (kind := .updateFinalizeInto) hInitial hCall.stackAvailable
    hCall.outputInMemory.2 hCall.outputSeparation hCall.returnAddress hStorage hReady hCode hDF
    hGrows hRip (by simpa only [EpilogueKind.source, Nat.add_zero] using hDigest)
  simpa only [EpilogueKind.loopKind, LoopKind.outputRegister, EpilogueKind.outputOffset,
    BitVec.add_zero] using h

theorem resetSecond_epiloguePre [bindings : Bindings] {initial s : RamState}
    {inputs : Array Slices.Input} {first : Nat} {digest : Vector UInt8 16}
    (hCall : (TwoMessages.ValidCall TwoMessages.digestSlicesReset) bindings initial inputs first)
    (hInitial : ReadyToStep initial) (hStorage : LoopKind.storage .resetSecond initial s)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hDF : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS)
    (hGrows : ∀ address : BitVec 64,
      (initial.external[address]?).isSome → (s.external[address]?).isSome)
    (hRip : s.RIP = 0x100c68)
    (hDigest : (⟨(stackPtr s).toNat + 216, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨digest.toArray⟩) :
    EpiloguePre .resetSecond initial (returnBoundary initial) digest
      (initial.regValue .r8 + 16) s := by
  exact epiloguePre_of_storage (kind := .resetSecond) hInitial hCall.stackAvailable
    hCall.outputInMemory.2
    ⟨hCall.separation.1, fun r hr ↦ ⟨by simp, (hCall.separation.2 r hr).2⟩⟩
    hCall.returnAddress hStorage hReady hCode hDF
    hGrows hRip hDigest

theorem finalizeResetSecond_epiloguePre [bindings : Bindings] {initial s : RamState}
    {inputs : Array Slices.Input} {first : Nat} {digest : Vector UInt8 16}
    (hCall : (TwoMessages.ValidCall TwoMessages.finalizeIntoResetSlices) bindings initial inputs first)
    (hInitial : ReadyToStep initial) (hStorage : LoopKind.storage .finalizeResetSecond initial s)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hDF : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS)
    (hGrows : ∀ address : BitVec 64,
      (initial.external[address]?).isSome → (s.external[address]?).isSome)
    (hRip : s.RIP = 0x1012f8)
    (hDigest : (⟨(stackPtr s).toNat + 216, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨digest.toArray⟩) :
    EpiloguePre .finalizeResetSecond initial (returnBoundary initial) digest
      (initial.regValue .r8 + 16) s := by
  exact epiloguePre_of_storage (kind := .finalizeResetSecond) hInitial hCall.stackAvailable
    hCall.outputInMemory.2
    ⟨hCall.separation.1, fun r hr ↦ ⟨by simp, (hCall.separation.2 r hr).2⟩⟩
    hCall.returnAddress hStorage hReady hCode hDF
    hGrows hRip hDigest

theorem resetDiscardSecond_epiloguePre [bindings : Bindings] {initial s : RamState}
    {inputs : Array Slices.Input} {first : Nat} {digest : Vector UInt8 16}
    (hCall : (ResetThenDigest.ValidCall ResetThenDigest.updateResetSlices) bindings initial inputs first)
    (hInitial : ReadyToStep initial) (hStorage : LoopKind.storage .resetDiscardSecond initial s)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hDF : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS)
    (hGrows : ∀ address : BitVec 64,
      (initial.external[address]?).isSome → (s.external[address]?).isSome)
    (hRip : s.RIP = 0x1017f9)
    (hDigest : (⟨(stackPtr s).toNat + 120, 16⟩ : MemoryRegion).HasBytes
      s.external ⟨digest.toArray⟩) :
    EpiloguePre .resetDiscardSecond initial (returnBoundary initial) digest
      (initial.regValue .r8) s := by
  simpa only [EpilogueKind.loopKind, LoopKind.outputRegister, EpilogueKind.outputOffset,
    BitVec.add_zero] using
    epiloguePre_of_storage (kind := .resetDiscardSecond) hInitial hCall.stackAvailable
    hCall.outputInMemory.2
    hCall.outputSeparation
    hCall.returnAddress hStorage hReady hCode hDF
    hGrows hRip hDigest

end Md5.Proofs.Streaming
