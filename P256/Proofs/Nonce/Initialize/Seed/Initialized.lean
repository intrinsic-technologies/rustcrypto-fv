import P256.Proofs.Nonce.Initialize.Seed.Initialize
import P256.Proofs.Nonce.Initialize.Seed.Bytes

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem initialized_bytes {s t : RamState}
    (effect : (initializeEffect s).Holds s t)
    (allocated : ∀ i < 72, (t.external[stackPtr s + BitVec.ofNat 64 i]?).isSome) :
    DrbgAt t (stackPtr s + 8) ⟨⟨Array.replicate 32 0⟩, ⟨Array.replicate 32 1⟩⟩ := by
  constructor
  · apply replicate32_of_words (word := 0)
    · decide +kernel
    · intro i hi
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        allocated (8+i) (by omega)
    · intro j hj
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · have h := effect.writes.2.1
        change memLoad t.external ((Operand.reg 4 : Operand 64).read s + 8) 64 = 0 at h
        rw [Operand.read_reg64] at h
        simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, stackPtr] using h
      · have h := effect.writes.2.2.1
        change memLoad t.external ((Operand.reg 4 : Operand 64).read s + 16) 64 = 0 at h
        rw [Operand.read_reg64] at h
        simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, stackPtr] using h
      · have h := effect.writes.2.2.2.1
        change memLoad t.external ((Operand.reg 4 : Operand 64).read s + 24) 64 = 0 at h
        rw [Operand.read_reg64] at h
        simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, stackPtr] using h
      · have h := effect.writes.2.2.2.2.1
        change memLoad t.external ((Operand.reg 4 : Operand 64).read s + 32) 64 = 0 at h
        rw [Operand.read_reg64] at h
        simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, stackPtr] using h
  · apply replicate32_of_words (word := 0x0101010101010101)
    · decide +kernel
    · intro i hi
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
        allocated (40+i) (by omega)
    · intro j hj
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · have h := effect.writes.2.2.2.2.2.1
        change memLoad t.external ((Operand.reg 4 : Operand 64).read s + 40) 64 = 0x0101010101010101 at h
        rw [Operand.read_reg64] at h
        simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, stackPtr] using h
      · have h := effect.writes.2.2.2.2.2.2.1
        change memLoad t.external ((Operand.reg 4 : Operand 64).read s + 48) 64 = 0x0101010101010101 at h
        rw [Operand.read_reg64] at h
        simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, stackPtr] using h
      · have h := effect.writes.2.2.2.2.2.2.2.1
        change memLoad t.external ((Operand.reg 4 : Operand 64).read s + 56) 64 = 0x0101010101010101 at h
        rw [Operand.read_reg64] at h
        simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, stackPtr] using h
      · have h := effect.writes.2.2.2.2.2.2.2.2
        change memLoad t.external ((Operand.reg 4 : Operand 64).read s + 64) 64 = 0x0101010101010101 at h
        rw [Operand.read_reg64] at h
        simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, stackPtr] using h

end P256.Proofs.Nonce.Initialize.Seed
