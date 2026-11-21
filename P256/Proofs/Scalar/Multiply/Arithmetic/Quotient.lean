import P256.Proofs.Scalar.Multiply.Model
import P256.Spec.Operations
import P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Quotient.Accumulator
import P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Quotient.Identities

namespace P256.Proofs.Scalar.Multiply.Arithmetic

open X86Proofs
open P256.Proofs.Scalar.Multiply.Barrett
open P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett

attribute [local irreducible]
  v118347 v11835a v118370 v118386 v11838f v118392 v118395 v118398
  v1183a5 v1183b6 v1183bf v1183c6 v1183cf v1183d2 v1183d6 v1183d9
  v1183dc v1183e8 v1183f1 v1183f4 v1183f8 v1183fb v118407 v118410
  v118413 v118423 v11842c v11843d v118446 v118449 v11844d v118450
  v118453 v118464 v11846a v11846d v118477 v11847f v118482 v118486
  v118489 v118495 v11849e v1184a1 v1184b6 v1184bf v1184d0 v1184d9
  v1184dc v1184e0 v1184e3 v1184e6 v1184f7 v118500 v118503 v11850c
  v118512 v118515 v118519 v11851c v118528 v118531 v118534 v11854e
  v118557 v118568 v118571 v118574 v118578 v11857b v11857e v11858f
  v118598 v11859e v1185a1 v1185a8 v1185ab v1185af v1185b2 v1185be
  v1185c4 v1185c7 v1185e6 v118600 v118615 v118623 v11862a v11862e
  v118631 v118641 v11864a v11864e v118654 v11866a v118670 v118675
  v11867a v11867f v118682 v118685 v118689 v11868c v11868f v11869d
  v1186a6 v1186a9 v1186b0 v1186c6 v1186cc v1186cf v1186d2 v1186d5
  v1186dc v1186e2 v1186e5 v1186e8 v1186f3 v1186f6 v118701 v118704
  v11870a v11870d v118718 v11871b v11871e v11872b v118732 v118735
  v118739 v11873c v118742 v118745 v118748 v11874b v11874e v11875b
  v118762 v118765 v118769 v11876c v118772 v118775 v118778 v11877b
  v11877e v11878c v118798 v11879b v11879f v1187a2 v1187a8 v1187ab
  v1187ae v1187b1 v1187b4 v1187c1 v1187cd v1187d0 v1187d4 v1187d7
  v1187dd v1187e0 v1187e3 v1187e6 v1187e9 v1187fe v118801 v118804
  v118807 v118815 v118819 v118827 v11882a v11882d v118830 v118833
  v118842 v118845 v118849 v11884c v11884f v118852 v118860 v118864
  v118872 v118875 v118878 v11887b v11887e v11888c v118890 v118894
  v118897 v11889a v11889d v1188af v1188b2 v1188b5 v1188c2 v1188c5
  v1188c8 v1188ce v1188dc v1188df v1188e1 v1188e4

theorem adc_eq (a b : BitVec 64) (c : Bool) :
    Common.Instructions.Carry.adcSpec a b (BitVec.ofBool c) =
      X86Proofs.adcSpec c a b := by
  simp only [Common.Instructions.Carry.adcSpec, BitVec.toNat_ofBool,
    ofInt_add_add_toNat, ofInt4_add_add_toNat _ _ _ (by decide : 4 ≤ 64),
    X86Proofs.adcSpec, ne_eq, natCast_eq_add_add]

theorem adc_comm (c : Bool) (a b : BitVec 64) :
    adcSpec c a b = adcSpec c b a := by
  simp only [adcSpec, BitVec.add_comm, Nat.add_comm, Int.add_comm]

theorem adc_false (a b : BitVec 64) : adcSpec false a b = addSpec a b := by
  simp [X86Proofs.adcSpec, addSpec]

theorem add_bool (a : BitVec 64) (c : Bool) :
    addSpec (BitVec.ofNat 64 c.toNat) a = adcSpec c a 0 := by
  cases c <;> simp [addSpec, adcSpec, BitVec.add_comm, Nat.add_comm, Int.add_comm]

theorem bool_ext (c : Bool) :
    (((if c then 1 else 0 : BitVec 8).setWidth 32).setWidth 64) =
      BitVec.ofNat 64 c.toNat := by
  cases c <;> rfl

theorem bool_merge (c : Bool) (a : BitVec 64) :
    ((((mergeGPR 8 (if c then 1 else 0) a).setWidth 8).setWidth 32).setWidth 64) =
      BitVec.ofNat 64 c.toNat := by
  rw [P256.Proofs.Scalar.Multiply.Arithmetic.Support.setWidth_mergeGPR _ _ (by decide) (by decide)]
  exact bool_ext c

def quotientWords (q : Inputs) : Vector (BitVec 64) 5 :=
  #v[(v11857b q).1, (v1185af q).1, (v1185cb q).1, (v1185d2 q).1, (v1185d5 q).1]

def productWords (q : Inputs) : Vector (BitVec 64) 5 :=
  #v[(v1185e6 q).1, (v118689 q).1, (v1186e2 q).1, (v1186f3 q).1, (v1186f6 q).1]

def remainderWords (q : Inputs) : Vector (BitVec 64) 5 :=
  #v[v118701 q, (v118739 q).1, (v118769 q).1, (v11879f q).1, (v1187d4 q).1]


def step (r : QuotientPartial) (a : BitVec 64) : QuotientPartialStep r a where
  low := addSpec (a * 0x012ffd85eedf9bfe) (r.lower &&& 0xfffffffffffffffe)
  middle := multiplyAdd a 0x43190552df1a6c21 r.middle
    (Common.Instructions.mulHigh64 a 0x012ffd85eedf9bfe)
    (addSpec (a * 0x012ffd85eedf9bfe) (r.lower &&& 0xfffffffffffffffe)).2.CF
  high := multiplyAdd a 0xfffffffeffffffff r.upperSum.1
    (multiplyAdd a 0x43190552df1a6c21 r.middle
      (Common.Instructions.mulHigh64 a 0x012ffd85eedf9bfe)
      (addSpec (a * 0x012ffd85eedf9bfe) (r.lower &&& 0xfffffffffffffffe)).2.CF).2 false
  top := multiplyAddFirst a 0xffffffff r.topSum.1
  sum := Common.Instructions.Carry.adcSpec (BitVec.ofNat 64 r.carry.toNat) a
    (BitVec.ofBool r.topSum.2.CF)
  low_eq := rfl
  middle_eq := rfl
  high_eq := rfl
  top_eq := rfl
  sum_eq := rfl

def partial0 (p : Inputs) : QuotientPartial :=
  ⟨(v11838f p).1, (v118392 p).1, (v118395 p).1, 0,
    (v118398 p).1, 0, (v118398 p).2.CF⟩

def partial1 (p : Inputs) : QuotientPartial :=
  ⟨(v1183d9 p).1, (v1183f8 p).1, (v118410 p).1, (v1183fb p).1,
    (v118413 p).1, (v1183a5 p).1, (v1183a5 p).2.CF⟩

def partial2 (p : Inputs) : QuotientPartial :=
  ⟨(v118450 p).1, (v118486 p).1, (v11849e p).1, (v118489 p).1,
    (v1184a1 p).1, (v118477 p).1, (v118477 p).2.CF⟩

def partial3 (p : Inputs) : QuotientPartial :=
  ⟨(v1184e3 p).1, (v118519 p).1, (v118531 p).1, (v11851c p).1,
    (v118534 p).1, (v11850c p).1, (v11850c p).2.CF⟩

def partial4 (p : Inputs) : QuotientPartial :=
  ⟨(v11857b p).1, (v1185af p).1, (v1185c4 p).1, (v1185b2 p).1,
    (v1185c7 p).1, (v1185a1 p).1, (v1185a1 p).2.CF⟩

theorem partial0_eq (p : Inputs) : quotientPartialInitial p.low[3] = partial0 p := by
  simp only [quotientPartialInitial, quotientPartialOfFirst, quotientFirstRow, partial0,
    v118347, v11835a, v118370, v118386, v11838f, v118392, v118395, v118398, adc_eq, mulResult_fst,
    P256.Proofs.Field.Inverse.SafeGcd.Core.Support.mulResult_snd, BitVec.reduceSetWidth,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  rfl

theorem partial1_eq (p : Inputs) : (step (partial0 p) p.high[0]).result = partial1 p := by
  simp only [step, QuotientPartialStep.result, partial0, partial1, QuotientPartial.upperSum,
    QuotientPartial.topSum, multiplyAdd, multiplyAddFirst,
    v1183a5, v1183b6, v1183bf, v1183c6, v1183cf, v1183d2, v1183d6, v1183d9, v1183dc, v1183e8, v1183f1, v1183f4, v1183f8, v1183fb, v118407, v118410, v118413, adc_eq, mulResult_fst,
    P256.Proofs.Field.Inverse.SafeGcd.Core.Support.mulResult_snd, BitVec.reduceSetWidth,
    adc_false, addSpec_zero_fst, addSpec_zero_cf, add_bool]
  rfl

theorem partial2_eq (p : Inputs) : (step (partial1 p) p.high[1]).result = partial2 p := by
  simp only [step, QuotientPartialStep.result, partial1, partial2, QuotientPartial.upperSum,
    QuotientPartial.topSum, multiplyAdd, multiplyAddFirst,
    v118423, v11842c, v11843d, v118446, v118449, v11844d, v118450, v118453, v118464, v11846a, v11846d, v118477, v11847f, v118482, v118486, v118489, v118495, v11849e, v1184a1, adc_eq, mulResult_fst,
    P256.Proofs.Field.Inverse.SafeGcd.Core.Support.mulResult_snd, BitVec.reduceSetWidth,
    adc_false, bool_ext]
  simp only [addSpec_comm]
  rfl

theorem partial3_eq (p : Inputs) : (step (partial2 p) p.high[2]).result = partial3 p := by
  simp only [step, QuotientPartialStep.result, partial2, partial3, QuotientPartial.upperSum,
    QuotientPartial.topSum, multiplyAdd, multiplyAddFirst,
    v1184b6, v1184bf, v1184d0, v1184d9, v1184dc, v1184e0, v1184e3, v1184e6, v1184f7, v118500, v118503, v11850c, v118512, v118515, v118519, v11851c, v118528, v118531, v118534, adc_eq, mulResult_fst,
    P256.Proofs.Field.Inverse.SafeGcd.Core.Support.mulResult_snd, BitVec.reduceSetWidth,
    adc_false, bool_ext]
  simp only [addSpec_comm]
  rfl

theorem partial4_eq (p : Inputs) : (step (partial3 p) p.high[3]).result = partial4 p := by
  simp only [step, QuotientPartialStep.result, partial3, partial4, QuotientPartial.upperSum,
    QuotientPartial.topSum, multiplyAdd, multiplyAddFirst,
    v11854e, v118557, v118568, v118571, v118574, v118578, v11857b, v11857e, v11858f, v118598, v11859e, v1185a1, v1185a8, v1185ab, v1185af, v1185b2, v1185be, v1185c4, v1185c7, adc_eq, mulResult_fst,
    P256.Proofs.Field.Inverse.SafeGcd.Core.Support.mulResult_snd, BitVec.reduceSetWidth,
    adc_false, bool_merge]
  simp only [addSpec_comm]
  rfl

theorem partial_result (r : QuotientPartial) (z : BitVec 64) : r.result =
    #v[r.lower, r.middle, (addSpec r.upper r.upperCarry).1,
      (adcSpec (addSpec r.upper r.upperCarry).2.CF r.topAdd r.top).1,
      (adcSpec (adcSpec (addSpec r.upper r.upperCarry).2.CF r.topAdd r.top).2.CF
        ((((mergeGPR 8 (if r.carry then 1 else 0) z).setWidth 8).setWidth 32).setWidth 64) 0).1] := by
  simp only [QuotientPartial.result, QuotientPartial.upperSum, QuotientPartial.topSum, adc_eq,
    bool_merge, adc_comm]

set_option backward.isDefEq.respectTransparency false in
theorem quotientWords_eq (p : Inputs) : (partial4 p).result = quotientWords p := by
  exact partial_result (partial4 p) (v11850c p).1


open P256.Proofs.Scalar.Multiply.Arithmetic.Natural
open P256.Proofs.Scalar.Multiply.Arithmetic.Support (packFour)

def inputValue (p : Inputs) : Nat :=
  packFour (p.low.map BitVec.toNat) + 2^256 * packFour (p.high.map BitVec.toNat)

set_option exponentiation.threshold 512 in
theorem inputValue_lt (p : Inputs) : inputValue p < 2^512 := by
  have h0 := p.low[0].isLt
  have h1 := p.low[1].isLt
  have h2 := p.low[2].isLt
  have h3 := p.low[3].isLt
  have h4 := p.high[0].isLt
  have h5 := p.high[1].isLt
  have h6 := p.high[2].isLt
  have h7 := p.high[3].isLt
  simp only [inputValue, packFour, Vector.getElem_map, P256.Proofs.Field.Montgomery.wordBase]
  omega

set_option exponentiation.threshold 512 in
theorem quotientWords_value (p : Inputs) :
    quotientValue (quotientWords p) = barrettQuotient (inputValue p) := by
  have h0 := quotientPartialInitial_value p.low[3]
  rw [partial0_eq] at h0
  have h1 := (step (partial0 p) p.high[0]).value
  rw [partial1_eq] at h1
  have h2 := (step (partial1 p) p.high[1]).value
  rw [partial2_eq] at h2
  have h3 := (step (partial2 p) p.high[2]).value
  rw [partial3_eq] at h3
  have h4 := (step (partial3 p) p.high[3]).value
  rw [partial4_eq] at h4
  rw [← quotientWords_eq, QuotientPartial.result_value, h4, h3, h2, h1, h0]
  have l0 := p.low[0].isLt
  have l1 := p.low[1].isLt
  have l2 := p.low[2].isLt
  simp only [inputValue, packFour, Vector.getElem_map, P256.Proofs.Field.Montgomery.wordBase,
    barrettQuotient, barrettMu]
  omega


end P256.Proofs.Scalar.Multiply.Arithmetic
