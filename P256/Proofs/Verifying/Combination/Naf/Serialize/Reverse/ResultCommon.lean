import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.Common

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse

open P256.Proofs.Common.Curve.LinearCombination.NafReverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem slot_cover (s : RamState) (offset len : Nat) (lo : 8 ≤ offset)
    (hi : offset + len ≤ 40) {a : BitVec 64}
    (h : (Component.mem (stackPtr s + BitVec.ofNat 64 offset) len).Covers a) :
    (Component.mem (stackPtr s+8) 32).Covers a := by
  obtain ⟨i, hi', rfl⟩ := h
  refine ⟨offset-8+i, by omega, ?_⟩
  change stackPtr s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i =
    stackPtr s+BitVec.ofNat 64 8+BitVec.ofNat 64 (offset-8+i)
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 2
  omega

theorem covered_slot_index (s : RamState) (offset len : Nat) (hi : offset+len ≤ 40)
    {i : Nat} (bound : i < 32)
    (h : (Component.mem (stackPtr s+BitVec.ofNat 64 offset) len).Covers
      (stackPtr s+8+BitVec.ofNat 64 i)) : offset ≤ 8+i ∧ 8+i < offset+len := by
  obtain ⟨j, hj, he⟩ := h
  change stackPtr s+BitVec.ofNat 64 8+BitVec.ofNat 64 i =
    stackPtr s+BitVec.ofNat 64 offset+BitVec.ofNat 64 j at he
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add] at he
  have he' := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp he)
  simp only [BitVec.toNat_ofNat] at he'
  have hi' : 8+i < 2^64 := by omega
  have hj' : offset+j < 2^64 := by omega
  rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at he'
  omega

theorem unchanged_byte {cs : List Component} {s t : RamState}
    (h : AgreesExcept cs s t) {a : BitVec 64}
    (ha : ∀ c ∈ cs, ¬ c.Covers a) : memByte t.external a = memByte s.external a :=
  congrArg (fun b : Option UInt8 => b.getD 0) (h.byte ha)

end P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse
