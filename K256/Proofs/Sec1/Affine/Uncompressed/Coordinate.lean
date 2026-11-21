import K256.Proofs.Common.Field.SquareValue
import X86Proofs.Instructions.Cmp.Operation
import X86Proofs.Instructions.Bswap.Operation

namespace K256.Proofs.Sec1.Affine.Uncompressed

open K256.Proofs.Common.Field X86Proofs

def unpack (a b c d : Word) : Limbs :=
  #v[d &&& 0xfffffffffffff, shldResult 12 c d &&& 0xfffffffffffff,
     shldResult 24 b c &&& 0xfffffffffffff, shldResult 36 a b &&& 0xfffffffffffff,
     a >>> 16]

private theorem pieces (k : Nat) (hk : k ≤ 52) (u v : Nat) (hv : v < 2^64) :
    ((u * 2^k + v / 2^(64-k)) % 2^64) % 2^52 =
      u % 2^(52-k) * 2^k + v / 2^(64-k) := by
  rw [Nat.mod_mod_of_dvd _ (by decide : 2^52 ∣ 2^64)]
  have hs : 2^(52-k) * 2^k = 2^52 := by rw [← Nat.pow_add, Nat.sub_add_cancel hk]
  have ht : 2^(64-k) * 2^k = 2^64 := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have hlow : v / 2^(64-k) < 2^k := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
    rwa [Nat.mul_comm, ht]
  have hm := Nat.mod_lt u (Nat.two_pow_pos (52-k))
  have hr : u % 2^(52-k) * 2^k + v / 2^(64-k) < 2^52 := by
    calc _ < (u % 2^(52-k) + 1) * 2^k := by rw [Nat.add_mul, Nat.one_mul]; omega
         _ ≤ _ := hs ▸ Nat.mul_le_mul_right _ hm
  calc _ = ((u % 2^(52-k) + 2^(52-k) * (u / 2^(52-k))) * 2^k + v / 2^(64-k)) % 2^52 := by rw [Nat.mod_add_div]
       _ = _ := by rw [Nat.add_mul, Nat.mul_right_comm (2^(52-k)), hs, Nat.add_right_comm,
    Nat.mul_comm (2^52), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem unpack_value (a b c d : Word) :
    limbValue (unpack a b c d) =
      (a.toNat * 2^64 + b.toNat) * 2^128 + c.toNat * 2^64 + d.toNat := by
  simp only [SquareValue.limbValue_eq]
  change (d &&& 0xfffffffffffff).toNat +
    (shldResult 12 c d &&& 0xfffffffffffff).toNat * 2^52 +
    (shldResult 24 b c &&& 0xfffffffffffff).toNat * 2^104 +
    (shldResult 36 a b &&& 0xfffffffffffff).toNat * 2^156 +
    (a >>> 16).toNat * 2^208 = _
  simp only [SquareValue.mask52, shldResult_toNat 12 c d (by decide) (by decide),
    shldResult_toNat 24 b c (by decide) (by decide), shldResult_toNat 36 a b (by decide) (by decide),
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rewrite [pieces 12 (by decide) _ _ d.isLt, pieces 24 (by decide) _ _ c.isLt,
    pieces 36 (by decide) _ _ b.isLt]
  omega

private theorem and_mask_eq (x y z : Word) :
    x &&& y &&& (z &&& 0xfffffffffffff) = 0xfffffffffffff ↔
      (x &&& 0xfffffffffffff).toNat = 2^52-1 ∧
      (y &&& 0xfffffffffffff).toNat = 2^52-1 ∧
      (z &&& 0xfffffffffffff).toNat = 2^52-1 := by
  let m : Word := 0xfffffffffffff
  have rearrange : x &&& y &&& (z &&& m) = (x &&& m) &&& (y &&& m) &&& (z &&& m) := by
    have hself : m &&& m &&& m = m := by simp only [BitVec.and_self]
    calc _ = (x &&& y &&& z) &&& (m &&& m &&& m) := by rw [hself]; ac_rfl
         _ = _ := by ac_rfl
  rw [rearrange, ← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_and]
  have bound (w : Word) : (w &&& m).toNat ≤ 2^52-1 := by
    rw [SquareValue.mask52]; omega
  have hx := bound x
  have hy := bound y
  have hz := bound z
  generalize (x &&& m).toNat = p at *
  generalize (y &&& m).toNat = q at *
  generalize (z &&& m).toNat = r at *
  constructor
  · intro h
    have hlp : p &&& q &&& r ≤ p := Nat.le_trans Nat.and_le_left Nat.and_le_left
    have hlq : p &&& q &&& r ≤ q := Nat.le_trans Nat.and_le_left Nat.and_le_right
    have hlr : p &&& q &&& r ≤ r := Nat.and_le_right
    change p &&& q &&& r = 2^52-1 at h
    omega
  · rintro ⟨rfl,rfl,rfl⟩
    decide

def invalid (a b c d : Word) : Bool :=
  let mask : Word := 0xfffffffffffff
  let hi := (shldResult 24 b c &&& shldResult 36 a b &&& (shldResult 12 c d &&& mask)) ^^^ mask
  decide ((hi ||| ((a >>> 16) ^^^ 0xffffffffffff)) = 0) &&
    decide (0xffffefffffc2e < (d &&& mask).toNat)

theorem invalid_eq (a b c d : Word) :
    invalid a b c d = decide (modulus ≤ limbValue (unpack a b c d)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [invalid, Bool.and_eq_true, decide_eq_true_eq, SquareValue.limbValue_eq]
  have hz (x y : Word) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := BitVec.or_eq_zero_iff
  have he (x y : Word) : x ^^^ y = 0 ↔ x = y := BitVec.xor_eq_zero_iff
  simp only [hz, he, and_mask_eq]
  rw [← BitVec.toNat_inj (x := a >>> 16)]
  change (((_ ∧ _ ∧ _) ∧ (a >>> 16).toNat = 2^48-1) ∧ _) ↔
    0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f ≤
      (d &&& 0xfffffffffffff).toNat +
      (shldResult 12 c d &&& 0xfffffffffffff).toNat * 2^52 +
      (shldResult 24 b c &&& 0xfffffffffffff).toNat * 2^104 +
      (shldResult 36 a b &&& 0xfffffffffffff).toNat * 2^156 +
      (a >>> 16).toNat * 2^208
  simp only [SquareValue.mask52, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have ha := a.isLt
  omega

theorem unpack_repr (a b c d : Word) (x : Fin modulus) (hx : limbValue (unpack a b c d) = x.val)
    {m : Nat} (hm : 0 < m) : FieldRepr (unpack a b c d) x m := by
  refine ⟨?_, by rw [hx, Nat.mod_eq_of_lt x.isLt]⟩
  have maskBound (w : Word) : (w &&& 0xfffffffffffff).toNat ≤ 2 * m * (2^52-1) := by
    rw [SquareValue.mask52]; omega
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact maskBound d
  · exact maskBound _
  · exact maskBound _
  · exact maskBound _
  · change (a >>> 16).toNat ≤ 2 * m * (2^48-1)
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have ha := a.isLt
    omega

theorem cmpAbove (u v : Word) :
    (!((cmpSpec u v).CF || (cmpSpec u v).ZF)) = decide (v.toNat < u.toNat) := by
  have cf : (cmpSpec u v).CF = decide (u.toNat < v.toNat) := rfl
  apply Bool.eq_iff_iff.mpr
  simp only [cf, cmpSpec_ZF, Bool.not_eq_true', Bool.or_eq_false_iff,
    decide_eq_false_iff_not, beq_eq_false_iff_ne, decide_eq_true_eq]
  have h : u ≠ v ↔ u.toNat ≠ v.toNat := not_congr BitVec.toNat_inj.symm
  rw [h]
  omega

theorem flagByte (lo hi : Prop) [Decidable lo] [Decidable hi] :
    ((if lo then (1 : BitVec 8) else 0) &&& (if hi then 1 else 0)).setWidth 64 =
      BitVec.ofNat 64 (decide hi && decide lo).toNat := by
  by_cases hlo : lo <;> by_cases hhi : hi <;> simp [hlo, hhi]

open X86.Machine X86.UserProcess

structure CoordinateWords where
  a : Word
  b : Word
  c : Word
  d : Word

def readCoordinate (m : Ram) (src : Word) : CoordinateWords :=
  ⟨bswapSpec (memLoad m src 64), bswapSpec (memLoad m (src+8) 64),
   bswapSpec (memLoad m (src+16) 64), bswapSpec (memLoad m (src+24) 64)⟩

def CoordinateWords.limbs (v : CoordinateWords) := unpack v.a v.b v.c v.d
def CoordinateWords.nat (v : CoordinateWords) := limbValue v.limbs
def CoordinateWords.valid (v : CoordinateWords) := decide (v.nat < modulus)
def CoordinateWords.masked (v : CoordinateWords) :=
  if v.valid then v.limbs else Vector.replicate 5 0

end K256.Proofs.Sec1.Affine.Uncompressed
