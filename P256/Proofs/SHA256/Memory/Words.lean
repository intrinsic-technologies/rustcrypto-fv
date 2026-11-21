import P256.Proofs.SHA256.Memory

set_option autoImplicit false

namespace P256.Proofs.SHA256

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem loadBytes32_of_bytes {m : Ram} {a : BitVec 64} {v : BitVec 32}
    (h : Bytes m a 4 (storedByte v)) : loadBytes m a 4 = .ok (v.zeroExtend 64) := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  simp only [BitVec.add_zero] at h0
  simp only [loadBytes, loadBytes.loop, addAddress, fromNat,
    BitVec.add_zero, Nat.zero_add, Nat.reduceAdd, h0, h1, h2, h3,
    Nat.pow_zero, Nat.mul_one, Nat.reducePow]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [storedByte, UInt8.toNat_ofNat', BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.reduceMul, Nat.reducePow,
    BitVec.zeroExtend, BitVec.toNat_setWidth]
  have := v.isLt
  omega

theorem memLoad32_of_loadBytes4 {m : Ram} {a : BitVec 64} {v : BitVec 32}
    (allocated : ∀ i < 4, (m[a + BitVec.ofNat 64 i]?).isSome)
    (loaded : loadBytes m a 4 = .ok (v.zeroExtend 64)) : memLoad m a 32 = v := by
  have bytes := Bytes.of_memLoad (n := 32) allocated
  have he := Except.ok.inj ((loadBytes32_of_bytes bytes).symm.trans loaded)
  have hv := congrArg (fun x : BitVec 64 => x.setWidth 32) he
  simpa only [BitVec.zeroExtend, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq] using hv

theorem CompressionPre.hashWord [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {input : ByteArray} {count i : Nat}
    (pre : CompressionPre s boundary hash input count) (hi : i < 8) :
    memLoad s.external (s.regValue .rdi + BitVec.ofNat 64 (4 * i)) 32 = hash[i]!.toBitVec := by
  apply memLoad32_of_loadBytes4 _ (pre.hashWords.2 i hi)
  intro j hj
  have hb := pre.outputAllocated
    (s.regValue .rdi + BitVec.ofNat 64 (4 * i + j))
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (by change 4 * i + j < 32; omega))
  obtain ⟨v, hv⟩ := hb
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, hv]
  rfl

end P256.Proofs.SHA256
