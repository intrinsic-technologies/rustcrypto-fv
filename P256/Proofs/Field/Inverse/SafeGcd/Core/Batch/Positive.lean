import P256.Proofs.Field.Inverse.SafeGcd.Core.Batch.Model
import P256.Proofs.SecretKeyFromBytes.Arithmetic
namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Batch

theorem sub_msb {w : Nat} (x : BitVec w) :
    (BitVec.cons true (0 : BitVec w) - BitVec.cons true x).msb = decide (0 < x.toNat) := by
  rw [BitVec.msb_eq_decide]
  apply decide_eq_decide.mpr
  simp only [BitVec.toNat_sub, BitVec.toNat_cons', Bool.toNat_true, Nat.shiftLeft_eq, Nat.one_mul]
  have hz : (0 : BitVec w).toNat = 0 := rfl
  rw [hz]
  have hx := x.isLt
  simp only [Nat.add_sub_cancel, Nat.pow_succ, Nat.add_zero]
  have hb : 0 < 2^w := Nat.two_pow_pos w
  have hle : 2^w + x.toNat ≤ 2^w*2 := by omega
  have he : 2^w*2 - (2^w+x.toNat) + 2^w = 2^w*2-x.toNat := by omega
  rw [he]
  by_cases hz : x.toNat = 0
  · simp only [hz, Nat.sub_zero, Nat.mod_self]; omega
  · have ht : 2^w*2-x.toNat < 2^w*2 := by omega
    rw [Nat.mod_eq_of_lt ht]
    omega

theorem pnat (b : Bool) (x : BitVec 63) :
  (positiveBit (BitVec.cons b x)).toNat =
    (((BitVec.cons true (0:BitVec 63) - BitVec.cons (b ^^ true) x).msb) && (b ^^ true)).toNat := by
  have hc : (0x8000000000000000 : BitVec 64) = BitVec.cons true (0 : BitVec 63) := by decide +kernel
  unfold positiveBit
  rw [hc, BitVec.cons_xor_cons]
  have hz (x : BitVec 63) : x ^^^ (0:BitVec 63) = x := BitVec.xor_zero
  rw [hz, P256.Proofs.SecretKeyFromBytes.Scalar.shift63_toNat, BitVec.msb_and, BitVec.msb_cons]

theorem pnat_false (x : BitVec 63) :
  (positiveBit (BitVec.cons false x)).toNat = (decide (0 < x.toNat)).toNat := by
  rw [pnat]
  simp only [Bool.false_xor, Bool.and_true, sub_msb]

theorem pnat_true (x : BitVec 63) :
  (positiveBit (BitVec.cons true x)).toNat = 0 := by
  rw [pnat]
  simp only [Bool.xor_self, Bool.and_false, Bool.toNat_false]

theorem pos_cons (b : Bool) (x : BitVec 63) :
  positiveBit (BitVec.cons b x) = if 0 < (BitVec.cons b x).toInt then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  cases b
  · rw [pnat_false, BitVec.toInt_eq_toNat_of_msb (by simp only [BitVec.msb_cons])]
    simp only [BitVec.toNat_cons', Bool.toNat_false, Nat.zero_shiftLeft, Nat.zero_add]
    by_cases h : 0 < x.toNat
    · have hi : (0:Int) < x.toNat := by omega
      simp only [h, hi, decide_true, Bool.toNat_true, ↓reduceIte]; rfl
    · have hi : ¬ (0:Int) < x.toNat := by omega
      simp only [h, hi, decide_false, Bool.toNat_false, ↓reduceIte]; rfl
  · rw [pnat_true]
    have hn := BitVec.toInt_neg_of_msb_true (x := BitVec.cons true x) (by simp only [BitVec.msb_cons])
    have hi : ¬ 0 < (BitVec.cons true x).toInt := by omega
    simp only [hi, ↓reduceIte]; rfl

theorem positiveBit_eq (d : BitVec 64) :
  positiveBit d = if 0 < d.toInt then 1 else 0 := by
  simpa only [BitVec.cons_msb_setWidth] using pos_cons d.msb (d.setWidth 63)

end P256.Proofs.Field.Inverse.SafeGcd.Core.Batch
