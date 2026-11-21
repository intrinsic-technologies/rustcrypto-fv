import P256.Proofs.Field.Inverse.SafeGcd.Core.Batch.Positive

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Batch


theorem select_zero (a b : BitVec 64) : select 0 a b = a := by
  simp only [select]
  change (0#64 &&& (b ^^^ a)) ^^^ a = a
  simp only [BitVec.zero_and, BitVec.zero_xor]

theorem select_one (a b : BitVec 64) : select 1 a b = b := by
  unfold select
  change (BitVec.allOnes 64 &&& (b ^^^ a)) ^^^ a = b
  simp only [BitVec.allOnes_and, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]


theorem swapByte_eq (p : Words) : swapByte p = if 0 < p.delta.toInt then (p.g.setWidth 8 &&& 1) else 0 := by
  unfold swapByte
  rw [positiveBit_eq]
  split <;> simp [BitVec.and_comm]

theorem oddByte_eq (p : Words) : oddByte p = if Shared.Batch.even p then 0 else 1 := by
  unfold oddByte Shared.Batch.even
  have hb : (p.g.setWidth 8 &&& 1).toNat ≤ 1 := by
    rw [BitVec.toNat_and]
    exact Nat.and_le_right
  by_cases hz : p.g.setWidth 8 &&& 1 = 0
  · simp only [hz, beq_self_eq_true, ite_true]
  · have ho : p.g.setWidth 8 &&& 1 = 1 := by
      apply BitVec.eq_of_toNat_eq
      have hn : (p.g.setWidth 8 &&& 1).toNat ≠ 0 := by
        intro h
        apply hz
        exact BitVec.eq_of_toNat_eq h
      change (p.g.setWidth 8 &&& 1).toNat = 1
      omega
    simp only [ho, BitVec.reduceBEq, Bool.false_eq_true, ite_false]


theorem swapByte_core (p : Words) : swapByte p = if Shared.Batch.swap p then 1 else 0 := by
  rw [swapByte_eq]
  change (if 0 < p.delta.toInt then oddByte p else 0) = _
  rw [oddByte_eq]
  unfold Shared.Batch.swap Shared.Batch.positive
  cases he : Shared.Batch.even p <;>
    by_cases h : 0 < p.delta.toInt <;> simp only [h, ↓reduceIte, decide_true, decide_false,
      Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and, Bool.false_eq_true]

theorem positiveBit_core (p : Words) : positiveBit p.delta = if Shared.Batch.positive p then 1 else 0 := by
  rw [positiveBit_eq]
  simp only [Shared.Batch.positive, decide_eq_true_eq]

theorem next_eq (p : Words) : next p = Shared.Batch.next p := by
  have hz : -(0#64) = 0#64 := by decide +kernel
  have ho : -(1#64) = BitVec.allOnes 64 := by decide +kernel
  have hs0 (a b : BitVec 64) : select (0#8) a b = a := select_zero a b
  have hs1 (a b : BitVec 64) : select (1#8) a b = b := select_one a b
  unfold next Shared.Batch.next maskedF
  simp only [oddByte_eq, swapByte_core, positiveBit_core]
  unfold Shared.Batch.swap Shared.Batch.numerator
  cases he : Shared.Batch.even p <;>
    cases hp : Shared.Batch.positive p
  all_goals simp only [ Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, select_zero, select_one]
  all_goals simp only [BitVec.reduceSetWidth]
  all_goals simp only [hz, ho, hs0, hs1, BitVec.zero_and, BitVec.allOnes_and,
    BitVec.add_zero, BitVec.sub_eq_add_neg]


end P256.Proofs.Field.Inverse.SafeGcd.Core.Batch
