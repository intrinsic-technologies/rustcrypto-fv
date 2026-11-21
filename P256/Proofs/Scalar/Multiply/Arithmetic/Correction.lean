import P256.Proofs.Scalar.Multiply.Arithmetic.Remainder
import P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Correction.Arithmetic
import P256.Proofs.Scalar.Multiply.Arithmetic.Support

namespace P256.Proofs.Scalar.Multiply.Arithmetic

open X86Proofs
open P256.Proofs.Scalar.Multiply.Barrett
open P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett

open P256.Proofs.Scalar.Multiply.Arithmetic.Support (Limbs)

private def ov1187fe (a : Limbs) (_top : BitVec 64) := addSpec (884452912994769583 : BitVec 64) (a.l0)

private def ov118801 (a : Limbs) (_top : BitVec 64) := ~~~(a.l0 : BitVec 64)

private def ov118804 (a : Limbs) (top : BitVec 64) := (ov118801 a top : BitVec 64) ||| ((ov1187fe a top).1)

private def ov118807 (a : Limbs) (top : BitVec 64) := (ov118804 a top : BitVec 64) >>> 63

private def ov118815 (a : Limbs) (top : BitVec 64) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (ov118807 a top)

private def ov118819 (a : Limbs) (top : BitVec 64) := (ov118815 a top : BitVec 64).sshiftRight 63

private def ov118827 (a : Limbs) (top : BitVec 64) := addSpec (4834901526196019580 : BitVec 64) (ov118819 a top)

private def ov11882a (a : Limbs) (top : BitVec 64) := addSpec ((ov118827 a top).1 : BitVec 64) (a.l1)

private def ov11882d (a : Limbs) (_top : BitVec 64) := ~~~(a.l1 : BitVec 64)

private def ov118830 (a : Limbs) (top : BitVec 64) := (ov11882d a top : BitVec 64) ||| ((ov11882a a top).1)

private def ov118833 (a : Limbs) (top : BitVec 64) := (ov118830 a top : BitVec 64) >>> 63

private def ov118842 (a : Limbs) (top : BitVec 64) := (ov118833 a top : BitVec 64) - 1

private def ov118845 (a : Limbs) (top : BitVec 64) := (ov118842 a top : BitVec 64) >>> 63

private def ov118849 (a : Limbs) (top : BitVec 64) := addSpec (ov118845 a top : BitVec 64) (a.l2)

private def ov11884c (a : Limbs) (_top : BitVec 64) := ~~~(a.l2 : BitVec 64)

private def ov11884f (a : Limbs) (top : BitVec 64) := (ov11884c a top : BitVec 64) ||| ((ov118849 a top).1)

private def ov118852 (a : Limbs) (top : BitVec 64) := (ov11884f a top : BitVec 64) >>> 63

private def ov118860 (a : Limbs) (top : BitVec 64) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (ov118852 a top)

private def ov118864 (a : Limbs) (top : BitVec 64) := (ov118860 a top : BitVec 64).sshiftRight 63

private def ov118872 (a : Limbs) (top : BitVec 64) := addSpec (4294967296 : BitVec 64) (ov118864 a top)

private def ov118875 (a : Limbs) (top : BitVec 64) := addSpec ((ov118872 a top).1 : BitVec 64) (a.l3)

private def ov118878 (a : Limbs) (_top : BitVec 64) := ~~~(a.l3 : BitVec 64)

private def ov11887b (a : Limbs) (top : BitVec 64) := (ov118878 a top : BitVec 64) ||| ((ov118875 a top).1)

private def ov11887e (a : Limbs) (top : BitVec 64) := (ov11887b a top : BitVec 64) >>> 63

private def ov11888c (a : Limbs) (top : BitVec 64) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (ov11887e a top)

private def ov118890 (a : Limbs) (top : BitVec 64) := (ov11888c a top : BitVec 64).sshiftRight 63

private def ov118894 (a : Limbs) (top : BitVec 64) := addSpec (ov118890 a top : BitVec 64) (top)

private def ov118897 (_a : Limbs) (top : BitVec 64) := ~~~(top : BitVec 64)

private def ov11889a (a : Limbs) (top : BitVec 64) := (ov118897 a top : BitVec 64) &&& ((ov118894 a top).1)

private def ov11889d (a : Limbs) (top : BitVec 64) := (ov11889a a top : BitVec 64) >>> 63

private theorem add_left_comm (a b c : BitVec 64) : a + (b+c) = b + (a+c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem orderMachine_eq (a : Limbs) (top : BitVec 64) :
    P256.Proofs.Scalar.Multiply.Arithmetic.Reduction.subtractOrder a =
      ⟨(ov1187fe a top).1, (ov11882a a top).1, (ov118849 a top).1, (ov118875 a top).1⟩ := by
  simp only [P256.Proofs.Scalar.Multiply.Arithmetic.Reduction.subtractOrder, ov1187fe, ov118801, ov118804, ov118807, ov118815,
    ov118819, ov118827, ov11882a, ov11882d, ov118830, ov118833, ov118842, ov118845, ov118849, ov11884c,
    ov11884f, ov118852, ov118860, ov118864, ov118872, ov118875,
    P256.Proofs.Scalar.Multiply.Arithmetic.Support.addSpec_low, BitVec.reduceSetWidth, BitVec.zero_sub]
  simp only [BitVec.add_assoc, add_left_comm, BitVec.add_comm]

private theorem borrowMachine_eq (a : Limbs) (top : BitVec 64) :
    correctionBorrow a top = ov11889d a top := by
  simp only [correctionBorrow, P256.Proofs.SecretKeyFromBytes.Scalar.orderBorrow,
    ov1187fe, ov118801, ov118804, ov118807, ov118815, ov118819, ov118827, ov11882a, ov11882d, ov118830,
    ov118833, ov118842, ov118845, ov118849, ov11884c, ov11884f, ov118852, ov118860, ov118864, ov118872,
    ov118875, ov118878, ov11887b, ov11887e, ov11888c, ov118890, ov118894, ov118897, ov11889a, ov11889d,
    P256.Proofs.Scalar.Multiply.Arithmetic.Support.addSpec_low,
    BitVec.reduceSetWidth, BitVec.zero_sub]
  simp only [BitVec.add_assoc, add_left_comm, BitVec.add_comm]
theorem subtractOrder_eq (p : Inputs) :
    P256.Proofs.Scalar.Multiply.Arithmetic.Reduction.subtractOrder (remainderLimbs p) =
      ⟨(v1187fe p).1, (v11882a p).1, (v118849 p).1, (v118875 p).1⟩ := by
  exact orderMachine_eq (remainderLimbs p) (v1187d4 p).1

theorem correctionBorrow_eq (p : Inputs) :
    correctionBorrow (remainderLimbs p) (v1187d4 p).1 = v11889d p := by
  exact borrowMachine_eq (remainderLimbs p) (v1187d4 p).1

attribute [local irreducible] v1187fe v11882a v118849 v118875 v11889d

private def finishWords (r : Limbs) (q : BitVec 64) : Vector (BitVec 64) 4 :=
  let low := addSpec (0xf3b9cac2fc632551 &&& -q) r.l0
  let second := adcSpec low.2.CF (0xbce6faada7179e84 &&& -q) r.l1
  let third := adcSpec second.2.CF (r.l2-q) 0
  let flag := (addSpec ((mergeGPR 8 (if second.2.CF then 1 else 0) r.l1).setWidth 8) 255).2.CF
  let high := adcSpec (adcSpec flag (-q) r.l2).2.CF (0xffffffff00000000 &&& -q) r.l3
  #v[low.1,second.1,third.1,high.1]

private theorem finishWords_eq (r : Limbs) (q : BitVec 64) :
    finishWords r q =
      let c := correctionResult r q
      #v[c.l0,c.l1,c.l2,c.l3] := by
  simp only [finishWords, correctionResult,
    P256.Proofs.Scalar.Multiply.Arithmetic.Support.setWidth_mergeGPR (n := 8) (k := 8) _ _ (by decide) (by decide),
    BitVec.setWidth_eq, P256.Proofs.Scalar.Multiply.Arithmetic.Support.boolByte_eq, P256.Proofs.Scalar.Multiply.Arithmetic.Support.boolByte_carry,
    P256.Proofs.Scalar.Multiply.Arithmetic.Support.addSpec_low, P256.Proofs.Scalar.Multiply.Arithmetic.Support.adcSpec_low,
    P256.Proofs.Scalar.Multiply.Arithmetic.Support.addSpec_carry, P256.Proofs.Scalar.Multiply.Arithmetic.Support.adcSpec_carry, P256.Proofs.Field.Montgomery.Reduction.adc]

theorem correctedWords_eq (p : Inputs) :
    reducedWords p =
      let r := correctionResult (P256.Proofs.Scalar.Multiply.Arithmetic.Reduction.subtractOrder (remainderLimbs p))
        (correctionBorrow (remainderLimbs p) (v1187d4 p).1)
      #v[r.l0, r.l1, r.l2, r.l3] := by
  change finishWords ⟨(v1187fe p).1, (v11882a p).1, (v118849 p).1, (v118875 p).1⟩
    (v11889d p) = _
  rw [finishWords_eq, ← subtractOrder_eq, ← correctionBorrow_eq]

open P256.Proofs.Scalar.Multiply.Arithmetic.Support (packFour)

theorem pack_limbs (r : Limbs) :
    packFour (#v[r.l0,r.l1,r.l2,r.l3].map BitVec.toNat) = r.toNat := by
  simp only [packFour, Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, P256.Proofs.Field.Montgomery.wordBase, Limbs.toNat]
  omega

theorem resultWords_correct (p : Inputs) :
    packFour ((resultWords p).map BitVec.toNat) =
      (packFour (p.low.map BitVec.toNat) + 2^256 * packFour (p.high.map BitVec.toNat)) %
        P256.Spec.Operations.domain.n := by
  change packFour ((reducedWords p).map BitVec.toNat) = _
  have hrem := remainderWords_value p
  have hvalue : (remainderLimbs p).toNat + 2^256 * (v1187d4 p).1.toNat =
      P256.Proofs.Scalar.Multiply.Arithmetic.Natural.barrettRemainder (inputValue p) := by
    simp only [quotientValue, remainderWords, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ] at hrem
    simp only [remainderLimbs, Limbs.toNat]
    omega
  have hout := correctionResult_barrett (inputValue_lt p) (remainderLimbs p)
    (v1187d4 p).1 hvalue
  rw [correctedWords_eq, pack_limbs]
  exact hout

end P256.Proofs.Scalar.Multiply.Arithmetic
