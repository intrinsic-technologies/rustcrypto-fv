import P256.Proofs.Scalar.Multiply.Arithmetic.Quotient
import P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Product.Arithmetic

namespace P256.Proofs.Scalar.Multiply.Arithmetic

open X86Proofs
open P256.Proofs.Scalar.Multiply.Barrett
open P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett
open P256.Proofs.Scalar.Multiply.Arithmetic.Natural

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
  v1185c4 v1185c7 v1185cb v1185d2 v1185d5 v1185e6 v118600 v118615
  v118623 v11862a v11862e v118631 v118641 v11864a v11864e v118654
  v11866a v118670 v118675 v11867a v11867f v118682 v118685 v118689
  v11868c v11868f v11869d v1186a6 v1186a9 v1186b0 v1186c6 v1186cc
  v1186cf v1186d2 v1186d5 v1186dc v1186e2 v1186e5 v1186e8 v1186f3
  v1186f6 v118701 v118704 v11870a v11870d v118718 v11871b v11871e
  v11872b v118732 v118735 v118739 v11873c v118742 v118745 v118748
  v11874b v11874e v11875b v118762 v118765 v118769 v11876c v118772
  v118775 v118778 v11877b v11877e v11878c v118798 v11879b v11879f
  v1187a2 v1187a8 v1187ab v1187ae v1187b1 v1187b4 v1187c1 v1187cd
  v1187d0 v1187d4 v1187d7 v1187dd v1187e0 v1187e3 v1187e6 v1187e9
  v1187fe v118801 v118804 v118807 v118815 v118819 v118827 v11882a
  v11882d v118830 v118833 v118842 v118845 v118849 v11884c v11884f
  v118852 v118860 v118864 v118872 v118875 v118878 v11887b v11887e
  v11888c v118890 v118894 v118897 v11889a v11889d v1188af v1188b2
  v1188b5 v1188c2 v1188c5 v1188c8 v1188ce v1188dc v1188df v1188e1
  v1188e4

set_option exponentiation.threshold 512 in
theorem productWords_certificate (p : Inputs) :
    quotientValue (productWords p) =
      (quotientValue (quotientWords p) * P256.Spec.Operations.domain.n) % 2^320 := by
  have h := Product.ProductWordCalculation.value {
  a := (v11857b p).1
  b := (v1185af p).1
  c := (v1185cb p).1
  d := (v1185d2 p).1
  e := (v1185d5 p).1
  v1185e6 := (v1185e6 p).1
  hv1185e6 := (v1185e6 p).2
  v118600 := (v118600 p).1
  hv118600 := (v118600 p).2
  v118615 := (v118615 p).1
  hv118615 := (v118615 p).2
  v118623 := (v118623 p)
  v11862a := (v11862a p)
  v11862e := (v11862e p)
  v118631 := (v118631 p)
  v118641 := (v118641 p).1
  hv118641 := (v118641 p).2
  v11864a := (v11864a p)
  v11864e := (v11864e p)
  v118654 := (v118654 p).1
  hv118654 := (v118654 p).2
  v11866a := (v11866a p).1
  hv11866a := (v11866a p).2
  v118670 := (v118670 p)
  v118675 := (v118675 p)
  v11867a := (v11867a p)
  v11867f := (v11867f p)
  v118682 := (v118682 p)
  v118685 := (v118685 p)
  v118689 := (v118689 p)
  v11868c := (v11868c p)
  v11868f := (v11868f p)
  v11869d := (v11869d p).1
  hv11869d := (v11869d p).2
  v1186a6 := (v1186a6 p)
  v1186a9 := (v1186a9 p)
  v1186b0 := (v1186b0 p).1
  hv1186b0 := (v1186b0 p).2
  v1186c6 := (v1186c6 p).1
  hv1186c6 := (v1186c6 p).2
  v1186cc := (v1186cc p)
  v1186cf := (v1186cf p)
  v1186d2 := (v1186d2 p)
  v1186d5 := (v1186d5 p)
  v1186dc := (v1186dc p).1
  hv1186dc := (v1186dc p).2
  v1186e2 := (v1186e2 p)
  v1186e5 := (v1186e5 p)
  v1186e8 := (v1186e8 p)
  v1186f3 := (v1186f3 p)
  v1186f6 := (v1186f6 p)
  v1185e6_eq := by
    simp only [v1185e6, mulResult_fst]
  hv1185e6_eq := by
    simp only [v1185e6, P256.Proofs.Field.Inverse.SafeGcd.Core.Support.mulResult_snd]
  v118600_eq := by
    simp only [v118600, mulResult_fst]
  hv118600_eq := by
    simp only [v118600, P256.Proofs.Field.Inverse.SafeGcd.Core.Support.mulResult_snd]
  v118615_eq := by
    simp only [v118615, mulResult_fst]
  hv118615_eq := by
    simp only [v118615, P256.Proofs.Field.Inverse.SafeGcd.Core.Support.mulResult_snd]
  v118623_eq := by
    simp only [v118623]
  v11862a_eq := by
    simp only [v11862a]
  v11862e_eq := by
    simp only [v11862e]
  v118631_eq := by
    simp only [v118631]
  v118641_eq := by
    simp only [v118641, mulResult_fst]
  hv118641_eq := by
    simp only [v118641, P256.Proofs.Field.Inverse.SafeGcd.Core.Support.mulResult_snd]
  v11864a_eq := by
    simp only [v11864a]
  v11864e_eq := by
    simp only [v11864e]
  v118654_eq := by
    simp only [v118654, mulResult_fst]
  hv118654_eq := by
    simp only [v118654, P256.Proofs.Field.Inverse.SafeGcd.Core.Support.mulResult_snd]
  v11866a_eq := by
    simp only [v11866a, mulResult_fst]
  hv11866a_eq := by
    simp only [v11866a, P256.Proofs.Field.Inverse.SafeGcd.Core.Support.mulResult_snd]
  v118670_eq := by
    simp only [v118670]
  v118675_eq := by
    simp only [v118675, adc_eq]
  v11867a_eq := by
    simp only [v11867a, adc_eq]
  v11867f_eq := by
    simp only [v11867f, adc_eq]
  v118682_eq := by
    simp only [v118682]
  v118685_eq := by
    simp only [v118685, adc_eq]
  v118689_eq := by
    simp only [v118689]
  v11868c_eq := by
    simp only [v11868c, adc_eq]
  v11868f_eq := by
    simp only [v11868f, adc_eq]
  v11869d_eq := by
    simp only [v11869d, mulResult_fst]
  hv11869d_eq := by
    simp only [v11869d, P256.Proofs.Field.Inverse.SafeGcd.Core.Support.mulResult_snd]
  v1186a6_eq := by
    simp only [v1186a6]
  v1186a9_eq := by
    simp only [v1186a9, adc_eq]
  v1186b0_eq := by
    simp only [v1186b0, mulResult_fst]
  hv1186b0_eq := by
    simp only [v1186b0, P256.Proofs.Field.Inverse.SafeGcd.Core.Support.mulResult_snd]
  v1186c6_eq := by
    simp only [v1186c6, mulResult_fst]
  hv1186c6_eq := by
    simp only [v1186c6, P256.Proofs.Field.Inverse.SafeGcd.Core.Support.mulResult_snd]
  v1186cc_eq := by
    simp only [v1186cc]
  v1186cf_eq := by
    simp only [v1186cf, adc_eq]
  v1186d2_eq := by
    simp only [v1186d2]
  v1186d5_eq := by
    simp only [v1186d5, adc_eq]
  v1186dc_eq := by
    simp only [v1186dc, mulResult_fst]
  hv1186dc_eq := by
    simp only [v1186dc, P256.Proofs.Field.Inverse.SafeGcd.Core.Support.mulResult_snd]
  v1186e2_eq := by
    simp only [v1186e2]
  v1186e5_eq := by
    simp only [v1186e5, adc_eq]
  v1186e8_eq := by
    simp only [v1186e8, adc_eq]
  v1186f3_eq := by
    simp only [v1186f3]
  v1186f6_eq := by
    simp only [v1186f6, adc_eq]
  }
  simpa only [quotientValue, productWords, quotientWords, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    show (2:Nat)^64 = 18446744073709551616 from rfl,
    show (2:Nat)^128 = 340282366920938463463374607431768211456 from rfl,
    show (2:Nat)^192 = 6277101735386680763835789423207666416102355444464034512896 from rfl,
    show (2:Nat)^256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from rfl,
    show (2:Nat)^320 = 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 from rfl,
    show P256.Spec.Operations.domain.n = 115792089210356248762697446949407573529996955224135760342422259061068512044369 from rfl] using h



theorem productWords_value (p : Inputs) :
    quotientValue (productWords p) =
      (barrettQuotient (inputValue p) * P256.Spec.Operations.domain.n) % 2^320 := by
  rw [productWords_certificate, quotientWords_value]

end P256.Proofs.Scalar.Multiply.Arithmetic
