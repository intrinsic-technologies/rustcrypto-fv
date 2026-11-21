import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Buffered.FinalizeReset.CompressCall

namespace Md5.Proofs.Buffered.Finalize

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86Proofs

variable {kind : Kind} {s : RamState} {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
  {src dst : Nat}

theorem Storage.compressCallPre (h : Storage kind s)
    (hsrc : s.regValue .rsi = stackPtr s + BitVec.ofNat 64 src)
    (hdst : s.regValue .rdi = stackPtr s + BitVec.ofNat 64 dst)
    (hcount : 64 * (s.regValue .rdx).toNat = input.size)
    (hsrcBound : src + input.size ≤ kind.stackBytes) (hdstBound : dst + 16 ≤ kind.stackBytes)
    (hdisjoint : src + input.size ≤ dst ∨ dst + 16 ≤ src)
    (hinput : (⟨(stackPtr s).toNat + src, input.size⟩ : MemoryRegion).HasBytes s.external input)
    (hbuffer : (⟨(stackPtr s).toNat + dst, 16⟩ : MemoryRegion).HasBytes s.external
      ⟨buffer.toBytes.toArray⟩) : FinalizeReset.CompressCall.Pre buffer input s := by
  have hi : Compress.inputRegion s input =
      (⟨(stackPtr s).toNat + src, input.size⟩ : MemoryRegion) := by
    unfold Compress.inputRegion registerRegion
    rw [hsrc, h.stackAddress (by omega)]
  have hb : Compress.outputRegion s =
      (⟨(stackPtr s).toNat + dst, 16⟩ : MemoryRegion) := by
    unfold Compress.outputRegion registerRegion
    rw [hdst, h.stackAddress (by omega)]
  have hlo := h.stackLow
  have hhi := h.stackHigh
  refine ⟨?_, ?_, hlo, ?_, h.stackAligned, h.belowRange, ?_, ?_, ?_, ?_⟩
  · change (Compress.inputRegion s input).Bounded ∧
      (Compress.inputRegion s input).HasLength (64 * (s.regValue .rdx).toNat) ∧ _
    rw [hi]
    refine ⟨?_, hcount, hinput⟩
    change (stackPtr s).toNat + src + input.size < userAddressLimit
    omega
  · change (Compress.outputRegion s).Bounded ∧ _
    rw [hb]
    refine ⟨?_, hbuffer⟩
    change (stackPtr s).toNat + dst + 16 < userAddressLimit
    omega
  · omega
  · rw [hi]
    intro address ha hc
    change (stackPtr s).toNat + src ≤ address ∧
      address < (stackPtr s).toNat + src + input.size at ha
    change (stackPtr s).toNat - 320 ≤ address ∧
      address < (stackPtr s).toNat - 320 + 320 at hc
    omega
  · rw [hb]
    intro address ha hc
    change (stackPtr s).toNat + dst ≤ address ∧
      address < (stackPtr s).toNat + dst + 16 at ha
    change (stackPtr s).toNat - 320 ≤ address ∧
      address < (stackPtr s).toNat - 320 + 320 at hc
    omega
  · rw [hi, hb]
    intro address ha hc
    change (stackPtr s).toNat + src ≤ address ∧
      address < (stackPtr s).toNat + src + input.size at ha
    change (stackPtr s).toNat + dst ≤ address ∧
      address < (stackPtr s).toNat + dst + 16 at hc
    omega
  · rw [hb]
    intro address ha
    apply h.stackAvoids address
    change (stackPtr s).toNat + dst ≤ address.toNat ∧
      address.toNat < (stackPtr s).toNat + dst + 16 at ha
    change (stackPtr s).toNat - 320 ≤ address.toNat ∧
      address.toNat < (stackPtr s).toNat - 320 + (320 + kind.stackBytes)
    omega

end Md5.Proofs.Buffered.Finalize
