import P256.Proofs.Field.Inverse.SafeGcd.Correction.Model
import P256.Proofs.Field.Subtract.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction

open X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Field.Subtract (subRaw subWord borrow)


theorem addSpec_low (x y : BitVec 64) : (addSpec x y).1 = x + y := rfl

def difference (p : Inputs) : Vector (BitVec 64) 4 :=
  #v[v1181c2 p, (v118200 p).1, (v118233 p).1, (v11826a p).1]

def signBit (p : Inputs) : BitVec 8 := (p.negate.setWidth 8 ^^^ p.sign) &&& 1

theorem difference_eq (p : Inputs) :
    limbs (difference p) = (subRaw (limbs p.modulus) (limbs p.magnitude)).1 := by
  simp [limbs, difference, subRaw, subWord, borrow, v1181c2, v1181c5, v1181cb,
    v1181ce, v1181d1, v1181d4, v1181d7, v1181ed, v1181f9, v1181fc, v118200,
    v118203, v118209, v11820c, v11820f, v118212, v118215, v118220, v11822c,
    v11822f, v118233, v118236, v11823c, v11823f, v118242, v118245, v118248,
    v118259, v118263, v118266, v11826a, addSpec_low]

theorem byte_extend (x : BitVec 8) : (x.setWidth 32).setWidth 64 = x.setWidth 64 := by
  simp

theorem low_byte (x : BitVec 32) : (x.setWidth 64).setWidth 8 = x.setWidth 8 := by
  simp

theorem shrink_byte (x : BitVec 8) : (x.setWidth 32).setWidth 8 = x := by
  simp

theorem widen_low (x : BitVec 8) : (x.setWidth 64).setWidth 32 = x.setWidth 32 := by
  simp

theorem mask_eq (p : Inputs) :
    v1182af p = if v118294 p = 0 then 0 else -(signBit p).setWidth 64 := by
  simp only [v1182af, v118291, v1181db, setWidth_mergeGPR8,
    low_byte, byte_extend, decide_eq_true_eq]
  split
  · rfl
  · simp only [widen_low, shrink_byte, signBit]


theorem bit_cases (x : BitVec 8) : x &&& 1 = 0 ∨ x &&& 1 = 1 := by
  revert x
  decide +kernel

theorem mask_select (z : Bool) (q : BitVec 8) (a b : BitVec 64)
    (h : q = 0 ∨ q = 1) :
    ((if z then 0 else -q.setWidth 64) &&& (b ^^^ a)) ^^^ a =
      if z || q == 0 then a else b := by
  rcases h with rfl | rfl <;> cases z <;> simp
  change (BitVec.allOnes 64 &&& (b ^^^ a)) ^^^ a = b
  exact (congrArg (fun x : BitVec 64 => x ^^^ a) BitVec.allOnes_and).trans
    (by simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero])

theorem vector_ite_get {n : Nat} (c : Prop) [Decidable c] (a b : Vector (BitVec 64) n)
    (i : Nat) (hi : i < n) :
    (if c then a else b)[i] = if c then a[i] else b[i] := by
  split <;> rfl

theorem correctedWords_eq (p : Inputs) :
    correctedWords p = if v118294 p = 0 ∨ signBit p = 0 then p.magnitude else difference p := by
  have h := bit_cases (p.negate.setWidth 8 ^^^ p.sign)
  change signBit p = 0 ∨ signBit p = 1 at h
  have masks : v1182c5 p = v1182af p ∧ v1182da p = v1182af p ∧
      v1182ef p = v1182af p := ⟨rfl, rfl, rfl⟩
  apply Vector.ext
  intro i hi
  have idx : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases idx with rfl | rfl | rfl | rfl
  all_goals simp only [correctedWords, difference, v1182b5, v1182b2, v1182ac,
    v1182cb, v1182c8, v1182c2, v1182e0, v1182dd, v1182d7, v1182f5, v1182f2,
    v1182ec, masks.1, masks.2.1, masks.2.2, mask_eq]
  all_goals first
    | simpa only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, vector_ite_get, Vector.getElem_mk, Array.reduceGetElem] using
        (mask_select (decide (v118294 p = 0)) (signBit p) (p.magnitude[0]) (v1181c2 p) h)
    | simpa only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, vector_ite_get, Vector.getElem_mk, Array.reduceGetElem] using
        (mask_select (decide (v118294 p = 0)) (signBit p) (p.magnitude[1]) ((v118200 p).1) h)
    | simpa only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, vector_ite_get, Vector.getElem_mk, Array.reduceGetElem] using
        (mask_select (decide (v118294 p = 0)) (signBit p) (p.magnitude[2]) ((v118233 p).1) h)
    | simpa only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, vector_ite_get, Vector.getElem_mk, Array.reduceGetElem] using
        (mask_select (decide (v118294 p = 0)) (signBit p) (p.magnitude[3]) ((v11826a p).1) h)

theorem difference_value (p : Inputs)
    (hb : (limbs p.magnitude).toNat < (limbs p.modulus).toNat) :
    (limbs (difference p)).toNat = (limbs p.modulus).toNat - (limbs p.magnitude).toNat := by
  rw [difference_eq]
  have h := P256.Proofs.Field.Subtract.subRaw_toNat
    (limbs p.modulus) (limbs p.magnitude)
  have hr := limbs_toNat_lt
    (subRaw (limbs p.modulus) (limbs p.magnitude)).1
  omega

theorem or_zero (a b c d : BitVec 64) :
    b ||| a ||| c ||| d = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  change (b ||| a ||| c ||| d) = 0#64 ↔ a = 0#64 ∧ b = 0#64 ∧ c = 0#64 ∧ d = 0#64
  simp only [BitVec.or_eq_zero_iff]
  exact ⟨fun ⟨⟨⟨hb, ha⟩, hc⟩, hd⟩ => ⟨ha, hb, hc, hd⟩,
    fun ⟨ha, hb, hc, hd⟩ => ⟨⟨⟨hb, ha⟩, hc⟩, hd⟩⟩

theorem zero_iff (p : Inputs) : v118294 p = 0 ↔ (limbs p.magnitude).toNat = 0 := by
  rw [v118294, v11828e, v11828b, or_zero]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    simp [limbs, Limbs.toNat, h0, h1, h2, h3]
  · intro h
    simp only [limbs, Limbs.toNat] at h
    exact ⟨BitVec.eq_of_toNat_eq (by change _ = 0; omega),
      BitVec.eq_of_toNat_eq (by change _ = 0; omega),
      BitVec.eq_of_toNat_eq (by change _ = 0; omega),
      BitVec.eq_of_toNat_eq (by change _ = 0; omega)⟩

theorem correctedWords_value (p : Inputs)
    (hb : (limbs p.magnitude).toNat < (limbs p.modulus).toNat) :
    (limbs (correctedWords p)).toNat =
      if (limbs p.magnitude).toNat = 0 ∨ signBit p = 0 then (limbs p.magnitude).toNat
      else (limbs p.modulus).toNat - (limbs p.magnitude).toNat := by
  simp only [correctedWords_eq, zero_iff]
  split
  · rfl
  · exact difference_value p hb

end P256.Proofs.Field.Inverse.SafeGcd.Correction
