import Md5.Proofs.Buffered.DigestPrepare.Long.Contracts
import Md5.Proofs.Buffered.DigestPrepare.Copy
import Md5.Proofs.Buffered.FinalizeReset.CompressCall

namespace Md5.Proofs.Buffered.DigestPrepare.Long

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {initial s : RamState} {input : ByteArray}

theorem Prepared.outputRegion (h : Prepared initial input s) :
    Compress.outputRegion s = ⟨(stackPtr s).toNat + 240, 16⟩ := by
  change (⟨(s.regValue .rdi).toNat, 16⟩ : MemoryRegion) = _
  rw [show s.regValue .rdi = stackPtr s + 240 from h.statePointerArg]
  congr 1
  exact h.toFrame.address (by decide)

set_option maxRecDepth 2048 in
theorem Prepared.compressPre (hCall : Digest.ValidCall bindings initial input)
    (h : Prepared initial input s) :
    FinalizeReset.CompressCall.Pre Standards.RFC.MD5.Buffer.initial (fullBytes input) s := by
  have hlo := h.stackLow
  have hhi : (stackPtr s).toNat + 264 < 2^32 := h.stackHigh
  have hinBound : (initial.regValue .rdi).toNat + input.size < 2^32 :=
    hCall.inputInMemory.2.1
  have hsize : (fullBytes input).size ≤ input.size := by
    rw [size_fullBytes]
    omega
  have hir : Compress.inputRegion s (fullBytes input) =
      ⟨(initial.regValue .rdi).toNat, (fullBytes input).size⟩ := by
    change (⟨(s.regValue .rsi).toNat, (fullBytes input).size⟩ : MemoryRegion) = _
    rw [show s.regValue .rsi = initial.regValue .rdi from h.inputPointer]
  have hin (address : Nat)
      (ha : (Compress.inputRegion s (fullBytes input)).Contains address) :
      (Digest.inputRegion initial input).Contains address := by
    rw [hir] at ha
    change (initial.regValue .rdi).toNat ≤ address ∧
      address < (initial.regValue .rdi).toNat + (fullBytes input).size at ha
    change (initial.regValue .rdi).toNat ≤ address ∧
      address < (initial.regValue .rdi).toNat + input.size
    omega
  have hsep := input_stack_disjoint hCall
  refine ⟨?_, ?_, hlo, by change (stackPtr s).toNat < 2^32; omega,
    h.stackAligned, h.toFrame.scratchWritable (AgreesExcept.refl [] s) 320 320
      (by decide) (by decide), ?_, ?_, ?_, ?_⟩
  · change (Compress.inputRegion s (fullBytes input)).Bounded ∧
      (Compress.inputRegion s (fullBytes input)).HasLength
        (64 * (s.regValue .rdx).toNat) ∧ _
    rw [hir]
    refine ⟨by change (initial.regValue .rdi).toNat + (fullBytes input).size < 2^32; omega,
      ?_, ?_⟩
    · change 64 * (s.regValue .rdx).toNat = (fullBytes input).size
      rw [show s.regValue .rdx = BitVec.ofNat 64 (input.size / 64) from h.blockCount,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), size_fullBytes]
      omega
    · simpa only [fullBytes, Nat.add_zero, Digest.inputRegion, registerRegion] using
        hasBytes_extract (h.toFrame.inputBytes hCall) 0 (input.size / 64 * 64)
  · change (Compress.outputRegion s).Bounded ∧ _
    rw [h.outputRegion]
    exact ⟨by change (stackPtr s).toNat + 240 + 16 < 2^32; omega, h.buffer⟩
  · intro address ha hs
    apply hsep address (hin address ha)
    apply h.toFrame.stackSubset hCall.stackAvailable
    change (stackPtr s).toNat - 320 ≤ address ∧
      address < (stackPtr s).toNat - 320 + 320 at hs
    change (stackPtr s).toNat - 320 ≤ address ∧
      address < (stackPtr s).toNat - 320 + 584
    omega
  · rw [h.outputRegion]
    intro address hb hs
    change (stackPtr s).toNat + 240 ≤ address ∧
      address < (stackPtr s).toNat + 240 + 16 at hb
    change (stackPtr s).toNat - 320 ≤ address ∧
      address < (stackPtr s).toNat - 320 + 320 at hs
    omega
  · rw [h.outputRegion]
    intro address ha hb
    apply hsep address (hin address ha)
    apply h.toFrame.stackSubset hCall.stackAvailable
    change (stackPtr s).toNat + 240 ≤ address ∧
      address < (stackPtr s).toNat + 240 + 16 at hb
    change (stackPtr s).toNat - 320 ≤ address ∧
      address < (stackPtr s).toNat - 320 + 584
    omega
  · rw [h.outputRegion]
    intro address hb
    apply h.stackAvoids address
    change (stackPtr s).toNat + 240 ≤ address.toNat ∧
      address.toNat < (stackPtr s).toNat + 240 + 16 at hb
    change (stackPtr s).toNat - 320 ≤ address.toNat ∧
      address.toNat < (stackPtr s).toNat - 320 + 584
    omega

end Md5.Proofs.Buffered.DigestPrepare.Long
