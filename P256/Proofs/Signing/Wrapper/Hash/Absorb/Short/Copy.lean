import P256.Proofs.Signing.Wrapper.Hash.Absorb.Short.Prepare
import P256.Proofs.Signing.Wrapper.Hash.Absorb.Short.State
import P256.Proofs.Signing.Wrapper.Hash.Absorb.Copy
import P256.Proofs.HMAC.Finalize.Copy

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Short

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy [Bindings] {initial start s t : RamState}
    {secret message : ByteArray} (pre : HashEntry initial start secret message)
    (initialized : Entered initial start s message) (ready : Ready initial start s t message)
    (short : message.size < 64) : ∃ u, Copied initial start u message := by
  have destination : t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 344 := by
    rw [ready.destination]
    simp only [frameBase]
    bv_omega
  obtain ⟨u, result⟩ := Absorb.Copy.copy (sourceOffset := 0) (count := message.size)
    (outputOffset := 344) pre ready.toFrame (by omega) (by decide) (by omega)
    0x278d 0x101d65 (by decide) (by decide +kernel) (by decide) ready.rip
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ready.source.trans pre.pointer)
    destination ready.count
  have bytes (offset len : Nat) (bound : offset + len ≤ 520)
      (apart : offset + len ≤ 176 ∨ 176 + message.size ≤ offset) :
      ∀ i < len, u.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    have h := result.stack_byte pre (offset := 520-offset) (len := len)
      (by decide) (by omega) (by omega) (by omega) hi
    have addr : stackPtr initial - BitVec.ofNat 64 (520-offset) =
        frameBase initial + BitVec.ofNat 64 offset := by
      simp only [frameBase]
      bv_omega
    simpa only [addr, ready.memory] using h
  have words := initialized.hash.hash
  have blocks := initialized.hash.count
  have words' : SHA256.HashStateAt s (frameBase initial + 240) SHA256.initialHash := by
    have h : SHA256.HashStateAt s (frameBase initial + 176 + 64) SHA256.initialHash := words
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  have blocks' : loadBytes s.external (frameBase initial + 272) 8 = .ok (0#64) := by
    have h : loadBytes s.external (frameBase initial + 176 + 96) 8 = .ok (0#64) := blocks
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  have sourceBytes := (message_input pre ready.toFrame).2.1
  refine ⟨u, result.toFrame, result.rip,
    (result.calleeSaved .rbp (by decide)).trans ready.length, ?_, ?_, ?_⟩
  · apply hasBytes_copy sourceBytes
    intro i hi
    have h := result.copied i hi
    have addr : stackPtr initial - BitVec.ofNat 64 344 = frameBase initial + 176 := by
      simp only [frameBase]
      bv_omega
    simpa only [addr, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  · exact SHA256.HashStateAt.copy words' (by
      intro i hi
      simpa only [BitVec.ofNat_eq_ofNat] using bytes 240 32 (by decide) (.inr (by omega)) i hi)
  · apply loadBytes_ok_copy _ blocks'
    intro i hi
    simpa only [BitVec.ofNat_eq_ofNat] using bytes 272 8 (by decide) (.inr (by omega)) i hi

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Short
