import K256.Proofs.Sec1.Parser.Control
import K256.Proofs.Sec1.Parser.Guards
import K256.Proofs.Sec1.Parser.Reject

namespace K256.Proofs.Sec1.Parser

open X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Sec1.LIR K256.Proofs.Refine K256.Spec.Program Prelude

theorem guardDispatch {args : Vector Value 53} {mem : Ram} {ptr len : BitVec 64} {bytes : ByteArray}
    (rsi : Value.get 64 args[6] = ptr) (rdx : Value.get 64 args[2] = len)
    (size : len.toNat = bytes.size) (nonempty : 0 < bytes.size)
    (contents : (⟨ptr.toNat, bytes.size⟩ : MemoryRegion).HasBytes mem bytes)
    (low : ptr.toNat + bytes.size ≤ 2 ^ 32)
    (loaded : ∀ x ∈ Extracted.programImage, mem[x.1]? = some x.2) :
    let t := bytes[0]'nonempty
    ∃ next : Vector Value 53, GuardRegisters args next ∧
      ((Reaches Extracted.programImage .l1063a7 args mem .l106560 next mem ∧
        K256.Spec.Secp256k1.decodePublicKey bytes = none) ∨
       (Reaches Extracted.programImage .l1063a7 args mem .l1063d2 next mem ∧
        ∃ valid : validTag t.toBitVec, len = lengthTable.get ⟨t.toNat, validTag_lt valid⟩)) := by
  intro t
  have ht : bytes.data[0]? = some t := by rw [Array.getElem?_eq_getElem (by exact nonempty)]; rfl
  have bytesAt := Bytes.of_hasBytes contents
  have hb := bytesAt.loadByte 0 nonempty
  have tag : memLoad mem ptr 8 = t.toBitVec := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero,
      nonempty, ↓reduceDIte] using hb
  have read : LoadOk mem ptr 1 := by
    refine ⟨by omega, ?_⟩
    intro i hi
    have hz : i = 0 := by omega
    subst i
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero,
      nonempty, ↓reduceDIte, Option.isSome_some] using congrArg Option.isSome (bytesAt 0 nonempty)
  obtain ⟨b, step, tagReg, keep⟩ := tagBlock (code := Extracted.programImage) rsi read
  rw [tag] at step tagReg
  by_cases valid : validTag t.toBitVec
  · rw [ite_eq_left valid] at step
    have dx : Value.get 64 b[2] = len := ((congrArg (Value.get 64) (keep 2 (by decide))).trans rdx)
    have cx : Value.get 64 b[1] = t.toBitVec.setWidth 64 := by rw [tagReg]; rfl
    obtain ⟨c, checkLen, keep'⟩ := lengthBlock (code := Extracted.programImage) cx dx valid loaded
    refine ⟨c, fun i h => (keep' i h).trans (keep i h), ?_⟩
    by_cases hlen : len = lengthTable.get ⟨t.toBitVec.toNat, validTag_lt valid⟩
    · rw [ite_eq_left hlen] at checkLen
      exact Or.inr ⟨(reaches_jump step).trans (reaches_jump checkLen), valid, hlen⟩
    · rw [ite_eq_right hlen] at checkLen
      refine Or.inl ⟨(reaches_jump step).trans (reaches_jump checkLen), decodePublicKey_lengthMismatch ht valid ?_⟩
      exact fun h => hlen (BitVec.eq_of_toNat_eq (size.trans h))
  · rw [ite_eq_right valid] at step
    exact ⟨b, keep, Or.inl ⟨reaches_jump step, decodePublicKey_invalidTag ht valid⟩⟩

end K256.Proofs.Sec1.Parser
