import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearCombination.Sign

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination

open X86Proofs
open P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
open P256.Proofs.Field.Subtract (borrow subWord subRaw)

def negativeRight (p : Inputs) : Vector (BitVec 64) 5 :=
  #v[v1b11f6 p, (v1b11fe p).1, (v1b1207 p).1, (v1b120f p).1, (v1b1355 p).1]

def selectedWords (p : Inputs) : Vector (BitVec 64) 5 :=
  #v[v1b1236 p, v1b124e p, v1b126a p, v1b127f p, v1b1361 p]

def differenceWords (p : Inputs) : Vector (BitVec 64) 5 :=
  #v[v1b128c p, (v1b12c2 p).1, (v1b12f0 p).1, (v1b131e p).1, (v1b137a p).1]

def negativeDifference (p : Inputs) : Vector (BitVec 64) 5 :=
  #v[v1b13ab p, (v1b13b4 p).1, (v1b13bd p).1, (v1b13c0 p).1, (v1b13d7 p).1]

theorem zero_sub_cf (x : BitVec 64) : (subSpec 0 x).2.CF = decide (x ≠ 0) := by
  change decide (0 < x.toNat) = decide (x ≠ 0)
  rw [decide_eq_decide]
  constructor
  · intro hp he
    have h := congrArg BitVec.toNat he
    change x.toNat = 0 at h
    omega
  · intro hn
    by_cases hp : 0 < x.toNat
    · exact hp
    · exact False.elim (hn (BitVec.eq_of_toNat_eq (by change x.toNat = 0; omega)))

theorem carry_mask (c : Bool) :
    (((((if !c then 1 else 0 : BitVec 8)).setWidth 32).setWidth 64).setWidth 32 &&& 1).setWidth 64 =
      (if !c then 1 else 0 : BitVec 8).setWidth 64 := by
  cases c <;> rfl

theorem rightCarry (p : Inputs) : (v1b1346 p).setWidth 64 =
    (if !(v1b120f p).2.CF then 1 else 0 : BitVec 8).setWidth 64 := by
  unfold v1b1346
  cases (v1b120f p).2.CF <;> rfl

theorem differenceCarry (p : Inputs) : (v1b13d4 p).setWidth 64 =
    (if !(v1b13c0 p).2.CF then 1 else 0 : BitVec 8).setWidth 64 := by
  unfold v1b13d4
  cases (v1b13c0 p).2.CF <;> rfl

theorem negativeRight_eq (p : Inputs) : negativeRight p = negateWide (rightWords p) := by
  simp only [negativeRight, negateWide, rightWords, v1b11f6, v1b11fe, v1b1207,
    v1b1355, v1b1352, rightCarry, v1b120f, Vector.getElem_mk, Array.reduceGetElem,
    zero_sub_cf, Correction.addSpec_low, BitVec.reduceSetWidth]

  rfl

theorem negativeDifference_eq (p : Inputs) :
    negativeDifference p = negateWide (differenceWords p) := by
  simp only [negativeDifference, negateWide, differenceWords, v1b13ab, v1b13b4,
    v1b13d7, v1b13c6, differenceCarry, v1b13bd, v1b13c0, Vector.getElem_mk, Array.reduceGetElem,
    zero_sub_cf, Correction.addSpec_low, BitVec.reduceSetWidth]
  simp only [BitVec.add_comm]
  all_goals rfl

theorem differenceWords_eq (p : Inputs) :
    (differenceWords p, v1b1383 p) = subtractWide (leftWords p) (selectedWords p) := by
  simp only [differenceWords, subtractWide, leftWords, selectedWords, subRaw, subWord,
    borrow, Vector.getElem_mk, Array.reduceGetElem,
    v1b128c, v1b128f, v1b1295, v1b1298, v1b129b, v1b129e, v1b12a1, v1b12b4,
    v1b12bb, v1b12be, v1b12c2, v1b12c5, v1b12cb, v1b12ce, v1b12d1, v1b12d4,
    v1b12d7, v1b12e2, v1b12e9, v1b12ec, v1b12f0, v1b12f3, v1b12f9, v1b12fc,
    v1b12ff, v1b1302, v1b1305, v1b1310, v1b1317, v1b131a, v1b131e, v1b1321,
    v1b1327, v1b132a, v1b132d, v1b1330, v1b1333, v1b133d, v1b1367, v1b136a,
    v1b1370, v1b1373, v1b1376, v1b137a, v1b137d, v1b1380, v1b1383,
    Correction.addSpec_low, BitVec.reduceSetWidth, BitVec.zero_sub]

theorem selection_byte (p : Inputs) (sa sb : Bool)
    (ha : v1b11a3 p = signByte sa) (hb : v1b11d6 p = signByte sb) :
    v1b11ea p = signByte (sa == sb) := by
  simp only [v1b11ea, v1b11e2, Support.byte_merge, Correction.low_byte,
    BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), ha, hb]
  cases sa <;> cases sb <;> rfl

theorem selection_mask (p : Inputs) : v1b1230 p = -(v1b11ea p).setWidth 64 := by
  simp only [v1b1230, Support.byte_merge, Correction.byte_extend]

theorem selectedWords_eq (p : Inputs) (sa sb : Bool)
    (ha : v1b11a3 p = signByte sa) (hb : v1b11d6 p = signByte sb) :
    selectedWords p = selectedRight (rightWords p) sa sb := by
  have hs := selection_byte p sa sb ha hb
  have m1 : v1b1248 p = v1b1230 p := rfl
  have m2 : v1b1264 p = v1b1230 p := rfl
  have m3 : v1b1279 p = v1b1230 p := rfl
  have m4 : v1b135b p = v1b1230 p := rfl
  rw [selectedRight, ← negativeRight_eq]
  apply Vector.ext
  intro i hi
  have idx : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases idx with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [selectedWords, negativeRight, rightWords, Correction.vector_ite_get,
    Vector.getElem_mk, Array.reduceGetElem, v1b1236, v1b1233, v1b1229,
    v1b124e, v1b124b, v1b1240, v1b126a, v1b1267, v1b125d,
    v1b127f, v1b127c, v1b1271, v1b1361, v1b135e, v1b1358,
    m1, m2, m3, m4, selection_mask, hs, select_mask, beq_iff_eq]

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
