import P256.Proofs.Scalar.Multiply.Arithmetic.Product
import P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Remainder.Arithmetic

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

open P256.Proofs.Scalar.Multiply.Arithmetic.Support (Limbs)
open P256.Proofs.Field.Subtract

def inputFive (p : Inputs) : Vector (BitVec 64) 5 :=
  #v[p.low[0], p.low[1], p.low[2], p.low[3], p.high[0]]

theorem remainderWords_eq (p : Inputs) :
    remainderWords p = Remainder.subtractFive (inputFive p) (productWords p) := by
  simp only [remainderWords, Remainder.subtractFive, inputFive, productWords,
    subRaw, subWord, borrow, v118701, v118704, v11870a, v11870d, v118718, v11871b, v11871e, v11872b, v118732, v118735, v118739, v11873c, v118742, v118745, v118748, v11874b, v11874e, v11875b, v118762, v118765, v118769, v11876c, v118772, v118775, v118778, v11877b, v11877e, v11878c, v118798, v11879b, v11879f, v1187a2, v1187a8, v1187ab, v1187ae, v1187b1, v1187b4, v1187c1, v1187cd, v1187d0, v1187d4,
    P256.Proofs.Scalar.Multiply.Arithmetic.Support.addSpec_low, BitVec.reduceSetWidth, BitVec.zero_sub,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]

def remainderLimbs (p : Inputs) : Limbs :=
  ⟨v118701 p, (v118739 p).1, (v118769 p).1, (v11879f p).1⟩


set_option exponentiation.threshold 512 in
theorem inputFive_value (p : Inputs) :
    quotientValue (inputFive p) = inputValue p % 2^320 := by
  have h0 := p.low[0].isLt
  have h1 := p.low[1].isLt
  have h2 := p.low[2].isLt
  have h3 := p.low[3].isLt
  have h4 := p.high[0].isLt
  simp only [quotientValue, inputFive, inputValue, P256.Proofs.Field.Schoolbook.packFour,
    P256.Proofs.Field.Montgomery.wordBase, Vector.getElem_map, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  omega

theorem remainderWords_value (p : Inputs) :
    quotientValue (remainderWords p) = barrettRemainder (inputValue p) := by
  rw [remainderWords_eq]
  exact Remainder.subtractFive_barrett (inputValue_lt p) (inputFive_value p)
    (productWords_value p)

end P256.Proofs.Scalar.Multiply.Arithmetic
