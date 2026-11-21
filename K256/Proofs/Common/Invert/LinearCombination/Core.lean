import K256.Proofs.Common.Invert.LinearCombination.Sign
import X86Proofs.Program.Compose

namespace K256.Proofs.Common.Invert.LinearCombination

open X86Proofs

theorem vector_ite_get {n : Nat} (c : Prop) [Decidable c] (a b : Vector (BitVec 64) n)
    (i : Nat) (hi : i < n) :
    (if c then a else b)[i] = if c then a[i] else b[i] := by
  split <;> rfl

theorem byte_merge (v : BitVec 8) (x : BitVec 64) : (mergeGPR 8 v x).setWidth 8 = v := by
  simp only [setWidth_mergeGPR8]

theorem addSpec_low (x y : BitVec 64) : (addSpec x y).1 = x+y := rfl

def negativeRight (p : Inputs) : Vector (BitVec 64) 5 :=
  #v[v108606 p, (v10860e p).1, (v108617 p).1, (v10861f p).1, (v108765 p).1]

def selectedWords (p : Inputs) : Vector (BitVec 64) 5 :=
  #v[v108646 p, v10865e p, v10867a p, v10868f p, v108771 p]

def differenceWords (p : Inputs) : Vector (BitVec 64) 5 :=
  #v[v10869c p, (v1086d2 p).1, (v108700 p).1, (v10872e p).1, (v10878a p).1]

def negativeDifference (p : Inputs) : Vector (BitVec 64) 5 :=
  #v[v1087bb p, (v1087c4 p).1, (v1087cd p).1, (v1087d0 p).1, (v1087e7 p).1]

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

theorem rightCarry (p : Inputs) : (v108756 p).setWidth 64 =
    (if !(v10861f p).2.CF then 1 else 0 : BitVec 8).setWidth 64 := by
  unfold v108756
  cases (v10861f p).2.CF <;> rfl

theorem differenceCarry (p : Inputs) : (v1087e4 p).setWidth 64 =
    (if !(v1087d0 p).2.CF then 1 else 0 : BitVec 8).setWidth 64 := by
  unfold v1087e4
  cases (v1087d0 p).2.CF <;> rfl

theorem negativeRight_eq (p : Inputs) : negativeRight p = negateWide (rightWords p) := by
  simp only [negativeRight, negateWide, rightWords, v108606, v10860e, v108617,
    v108765, v108762, rightCarry, v10861f, Vector.getElem_mk, Array.reduceGetElem,
    zero_sub_cf, addSpec_low, BitVec.reduceSetWidth]

  rfl

theorem negativeDifference_eq (p : Inputs) :
    negativeDifference p = negateWide (differenceWords p) := by
  simp only [negativeDifference, negateWide, differenceWords, v1087bb, v1087c4,
    v1087e7, v1087d6, differenceCarry, v1087cd, v1087d0, Vector.getElem_mk, Array.reduceGetElem,
    zero_sub_cf, addSpec_low, BitVec.reduceSetWidth]
  simp only [BitVec.add_comm]
  all_goals rfl

theorem differenceWords_eq (p : Inputs) :
    (differenceWords p, v108793 p) = subtractWide (leftWords p) (selectedWords p) := by
  simp only [differenceWords, subtractWide, leftWords, selectedWords, subRaw, subWord,
    borrow, Vector.getElem_mk, Array.reduceGetElem,
    v10869c, v10869f, v1086a5, v1086a8, v1086ab, v1086ae, v1086b1, v1086c4,
    v1086cb, v1086ce, v1086d2, v1086d5, v1086db, v1086de, v1086e1, v1086e4,
    v1086e7, v1086f2, v1086f9, v1086fc, v108700, v108703, v108709, v10870c,
    v10870f, v108712, v108715, v108720, v108727, v10872a, v10872e, v108731,
    v108737, v10873a, v10873d, v108740, v108743, v10874d, v108777, v10877a,
    v108780, v108783, v108786, v10878a, v10878d, v108790, v108793,
    addSpec_low, BitVec.reduceSetWidth, BitVec.zero_sub]

theorem selection_byte (p : Inputs) (sa sb : Bool)
    (ha : v1085b3 p = signByte sa) (hb : v1085e6 p = signByte sb) :
    v1085fa p = signByte (sa == sb) := by
  simp only [v1085fa, v1085f2, byte_merge, low_byte,
    BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), ha, hb]
  cases sa <;> cases sb <;> rfl

theorem selection_mask (p : Inputs) : v108640 p = -(v1085fa p).setWidth 64 := by
  simp only [v108640, byte_merge, byte_extend]

theorem selectedWords_eq (p : Inputs) (sa sb : Bool)
    (ha : v1085b3 p = signByte sa) (hb : v1085e6 p = signByte sb) :
    selectedWords p = selectedRight (rightWords p) sa sb := by
  have hs := selection_byte p sa sb ha hb
  have m1 : v108658 p = v108640 p := rfl
  have m2 : v108674 p = v108640 p := rfl
  have m3 : v108689 p = v108640 p := rfl
  have m4 : v10876b p = v108640 p := rfl
  rw [selectedRight, ← negativeRight_eq]
  apply Vector.ext
  intro i hi
  have idx : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases idx with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [selectedWords, negativeRight, rightWords, vector_ite_get,
    Vector.getElem_mk, Array.reduceGetElem, v108646, v108643, v108639,
    v10865e, v10865b, v108650, v10867a, v108677, v10866d,
    v10868f, v10868c, v108681, v108771, v10876e, v108768,
    m1, m2, m3, m4, selection_mask, hs, select_mask, beq_iff_eq]

end K256.Proofs.Common.Invert.LinearCombination
