import Md5.Proofs.Buffered.DigestPrepare.Geometry
import Md5.Proofs.Buffered.Update.Slices.Byte.Store
import Md5.Proofs.Buffered.Stores.Program

namespace Md5.Proofs.Buffered.DigestPrepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem position_store [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (h : Frame initial boundary s) {p : BitVec 64}
    (hsite : p = 0x10007e ∨ p = 0x1000b3) (hrip : s.RIP = p) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (storeEffect p 8 (fun u ↦ stackPtr u + 239)
        (fun u ↦ (Operand.reg 15 : Operand 8).read u) s).Holds s t := by
  have hw := h.writable (AgreesExcept.refl [] s) 239 1 (by decide)
  have hp : Memory.StorePre p 8 (fun u ↦ stackPtr u + 239) 1 s := by
    refine ⟨hrip, ⟨hw.readable.low, hw.readable.mem, hw.tables⟩, ?_⟩
    rcases hsite with rfl | rfl
    · exact Stores.rangeApart_text hw.code (by decide +kernel : 0x7e + 8 ≤ Extracted.textBytes.size)
    · exact Stores.rangeApart_text hw.code (by decide +kernel : 0xb3 + 8 ≤ Extracted.textBytes.size)
  have hb : CodeIn (codeRange p [0x44, 0x88, 0xbc, 0x24, 0xef, 0, 0, 0]) s := by
    rcases hsite with rfl | rfl
    · exact program_text_slice h.code 0x7e 8 (by decide +kernel)
    · exact program_text_slice h.code 0xb3 8 (by decide +kernel)
  have hstep := Update.Byte.mov_m8_r8_rex_effect_step p 0x44
    (by unfold RexPrefix; decide) 7 (.sib 4 none 0 (.d32 239))
    (by decide) (by decide) (by decide)
  change StepEffect (Memory.StorePre p 8 (fun u ↦ stackPtr u + 239) 1)
    (codeRange p [0x44, 0x88, 0xbc, 0x24, 0xef, 0, 0, 0])
    (storeEffect p 8 (fun u ↦ stackPtr u + 239)
      (fun u ↦ (Operand.reg 15 : Operand 8).read u)) at hstep
  have hne : p + 8 ≠ boundary.rip := by
    rcases hsite with rfl | rfl
    · exact text_address_ne_return h.boundaryOutside 0x86 (by decide +kernel)
    · exact text_address_ne_return h.boundaryOutside 0xbb (by decide +kernel)
  obtain ⟨t, ha, ht, he⟩ := hstep.advances h.ready hb hp hne
  refine ⟨t, ha, ht, he.codeIn ?_ h.code, he⟩
  exact Stores.store_avoids_program rfl (by simpa using hw.code)


theorem Frame.after_position_store [bindings : Bindings] {initial s t : RamState}
    {input : ByteArray} {p : BitVec 64}
    (hCall : Digest.ValidCall bindings initial input)
    (h : Frame initial (returnBoundary initial) s)
    (ht : ReadyToStep t) (hc : CodeIn Extracted.programImage t)
    (he : (storeEffect p 8 (fun u ↦ stackPtr u + 239)
      (fun u ↦ (Operand.reg 15 : Operand 8).read u) s).Holds s t) :
    Frame initial (returnBoundary initial) t := by
  apply h.preserve hCall.stackAvailable he.agrees ht hc
  · intro c hc hm
    simp only [storeEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases hm
    · simp [digestPreparationChanges]
  · intro c hc address hcov
    simp only [storeEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := hcov
      change (Finalize.Kind.digest.stackRegion s).Contains
        (stackPtr s + BitVec.ofNat 64 239 + BitVec.ofNat 64 i).toNat
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.address (by omega)]
      have := h.stackLow
      change (stackPtr s).toNat - 320 ≤ _ ∧ _ < (stackPtr s).toNat - 320 + 584
      omega
    · exact hcov.elim
  · exact he.agrees.read (n := 64) (r := 4) (by simp)
  · exact he.agrees.read (n := 64) (r := 3) (by simp)
  · exact he.agrees.read (n := 64) (r := 14) (by simp)

end Md5.Proofs.Buffered.DigestPrepare
