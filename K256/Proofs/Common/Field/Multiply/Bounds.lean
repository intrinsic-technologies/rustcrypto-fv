import K256.Proofs.Common.Field.Multiply.Words
import K256.Proofs.Common.Field.SquareValue

namespace K256.Proofs.Common.Field.Multiply

structure BoundedValue (actual value upper : Nat) : Prop where
  eq : actual = value
  le : value ≤ upper

def wideValue (a : Wide) : Nat := pairNat a.1 a.2

namespace BoundedValue

theorem wideMul {a b : Word} {x y A B : Nat} (ha : BoundedValue a.toNat x A)
    (hb : BoundedValue b.toNat y B) :
    BoundedValue (wideValue (Multiply.wideMul a b)) (x * y) (A * B) :=
  ⟨(SquareValue.pair_mul a b).trans (by rw [ha.eq, hb.eq]), Nat.mul_le_mul ha.le hb.le⟩

theorem wideAdd {a b : Wide} {x y A B : Nat} (ha : BoundedValue (wideValue a) x A)
    (hb : BoundedValue (wideValue b) y B) (h : A + B < 2^128 := by decide) :
    BoundedValue (wideValue (Multiply.wideAdd a b)) (x + y) (A + B) := by
  have hl := Nat.add_le_add ha.le hb.le
  refine ⟨?_, hl⟩
  exact (SquareValue.pair_add a.1 a.2 b.1 b.2
    (by change wideValue a + wideValue b < _; rw [ha.eq, hb.eq]; exact Nat.lt_of_le_of_lt hl h)).trans
      (by change wideValue a + wideValue b = _; rw [ha.eq, hb.eq])

theorem wideAddRev {a b : Wide} {x y A B : Nat} (ha : BoundedValue (wideValue a) x A)
    (hb : BoundedValue (wideValue b) y B) (h : A + B < 2^128 := by decide) :
    BoundedValue (wideValue (Multiply.wideAddRev a b)) (x + y) (A + B) := by
  have hl := Nat.add_le_add ha.le hb.le
  refine ⟨?_, hl⟩
  exact (SquareValue.pair_add_swap a.1 a.2 b.1 b.2
    (by change wideValue a + wideValue b < _; rw [ha.eq, hb.eq]; exact Nat.lt_of_le_of_lt hl h)).trans
      (by change wideValue a + wideValue b = _; rw [ha.eq, hb.eq])

theorem ofWord {a : Word} {x A : Nat} (ha : BoundedValue a.toNat x A) :
    BoundedValue (wideValue (Multiply.ofWord a)) x A := by
  refine ⟨?_, ha.le⟩
  change a.toNat + 2^64 * 0 = x
  simpa only [Nat.mul_zero, Nat.add_zero] using ha.eq

theorem high52 {a : Wide} {x A : Nat} (ha : BoundedValue (wideValue a) x A)
    (h : A < 2^116 := by decide) :
    BoundedValue (Multiply.high52 a).toNat (x / 2^52) (A / 2^52) := by
  refine ⟨?_, Nat.div_le_div_right ha.le⟩
  exact (SquareValue.shr52 a.1 a.2 (by change wideValue a < _; rw [ha.eq]; exact Nat.lt_of_le_of_lt ha.le h)).trans
    (congrArg (· / 2^52) ha.eq)

private theorem low_mod (a : Wide) (k : Nat) (hk : k ≤ 64) :
    a.1.toNat % 2^k = wideValue a % 2^k := by
  rw [SquareValue.lo_toNat a.1 a.2, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hk)]
  rfl

theorem low52 {a : Wide} {x A : Nat} (ha : BoundedValue (wideValue a) x A) :
    BoundedValue (Multiply.low52 a).toNat (x % 2^52) (2^52-1) := by
  refine ⟨?_, Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  rw [Multiply.low52, SquareValue.mask52, low_mod a 52 (by decide), ha.eq]

theorem low48 {a : Wide} {x A : Nat} (ha : BoundedValue (wideValue a) x A) :
    BoundedValue (Multiply.low48 a).toNat (x % 2^48) (2^48-1) := by
  refine ⟨?_, Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  rw [Multiply.low48, BitVec.and_comm, SquareValue.mask48', low_mod a 48 (by decide), ha.eq]

theorem combine56 {a b : Wide} {x y A B : Nat}
    (ha : BoundedValue (wideValue a) x A) (hb : BoundedValue (wideValue b) y B) :
    BoundedValue (Multiply.combine56 a b).toNat (x % 2^52 * 16 + y / 2^48 % 16) (2^56-1) := by
  refine ⟨?_, by omega⟩
  rw [show (Multiply.combine56 a b).toNat = _ from SquareValue.u0_toNat a.1 b.1, low_mod a 52 (by decide), ha.eq,
    SquareValue.lo_toNat b.1 b.2]
  change _ + (wideValue b % 2^64) / 2^48 % 16 = _
  rw [hb.eq]
  omega

theorem wordAdd {a b : Word} {x y A B : Nat} (ha : BoundedValue a.toNat x A)
    (hb : BoundedValue b.toNat y B) (h : A + B < 2^64 := by decide) :
    BoundedValue (a + b).toNat (x + y) (A + B) := by
  have hl := Nat.add_le_add ha.le hb.le
  exact ⟨by rw [BitVec.toNat_add, ha.eq, hb.eq, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hl h)], hl⟩

end BoundedValue
end K256.Proofs.Common.Field.Multiply
