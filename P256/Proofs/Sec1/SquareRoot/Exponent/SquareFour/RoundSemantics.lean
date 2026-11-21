import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Representation
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.RoundCompose

set_option autoImplicit false
open P256.Proofs.Field.Montgomery (adc64 add64 product64)

namespace P256.Proofs.Sec1.SquareRoot.SquareFour
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def AccumulatorAt (t : RamState) (a : FinalWords) : Prop :=
  (Operand.reg 1 : Operand 64).read t = a.first ∧
  (Operand.reg 5 : Operand 64).read t = a.second ∧
  (Operand.reg 8 : Operand 64).read t = a.top.low ∧
  (Operand.reg 9 : Operand 64).read t = a.top.mid ∧
  (Operand.reg 15 : Operand 64).read t = a.top.high

private theorem negate_mul_max (v : BitVec 64) : -(v * 0xffffffffffffffff#64) = v := by
  change -(v * -1#64) = v
  rw [BitVec.mul_neg, BitVec.mul_one, BitVec.neg_neg]

set_option maxHeartbeats 800000 in
theorem arithmetic_accumulator [Bindings] {s t u : RamState} {x : Nat}
    (hf : ExponentFrame s t) (hc : ExponentConstants s t x)
    (a : Vector (BitVec 64) 4) (digit : BitVec 64) (old : FinalWords)
    (hw : ReverseWordsAt t (exponentFrameBase s) a)
    (hacc : AccumulatorAt t old)
    (hi : (Operand.reg 12 : Operand 64).read t = 0xffffffffffffffff)
    (hax : (Operand.reg 0 : Operand 64).read t = digit)
    (hsi : (Operand.reg 6 : Operand 64).read t = digit)
    (hmod0 : (Operand.reg 11 : Operand 64).read t = 0xffffffffffffffff)
    (hmod1 : (Operand.reg 3 : Operand 64).read t = 0xffffffff)
    (hzero : (Operand.reg 14 : Operand 64).read t = 0)
    (hlo : (Operand.mem (exponentFrameBase s + 0x70) : Operand 64).read t = old.top.low)
    (hmid : (Operand.mem (exponentFrameBase s + 0x2f0) : Operand 64).read t = old.top.mid)
    (hh : (arithmeticEffect t).Holds t u) :
    AccumulatorAt u (squareRound old digit a) := by
  have hsp : (Operand.reg 4#5 : Operand 64).read t = exponentFrameBase s := hf.rsp
  have hm2 := hc.modulus2
  have hm3 := hc.modulus3
  have hm0 := hc.modulus0
  have hm1 := hc.modulus1
  change (Operand.mem (exponentFrameBase s + 0x98) : Operand 64).read t = 0 at hm2
  change (Operand.mem (exponentFrameBase s + 0x90) : Operand 64).read t = 0xffffffff00000001 at hm3
  change (Operand.mem (exponentFrameBase s + 0x88) : Operand 64).read t = 0xffffffffffffffff at hm0
  change (Operand.mem (exponentFrameBase s + 0x80) : Operand 64).read t = 0xffffffff at hm1
  have ho := hh.obsAfter (arithmetic_full t) true
  rcases hw with ⟨hw0,hw1,hw2,hw3⟩
  rcases hacc with ⟨ho0,ho1,ho2,ho3,ho4⟩
  simp only [BitVec.ofNat_eq_ofNat] at hi hm0 hm1 hm2 hm3 hw0 hw1 hw2 hw3 ho0 ho1 ho2 ho3 ho4 hax hsi hmod0 hmod1 hzero hlo hmid
  unfold AccumulatorAt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [← ho.read_reg]
  all_goals x86_norm [Bool.or_eq_false_iff, BitVec.ofNat_eq_ofNat, arithmeticEffect, firstProductsEffect, firstCarryEffect, middleFirstEffect,
    middleSecondEffect, topCarryEffect, hsp, hi, hm0, hm1, hm2, hm3, hw0, hw1, hw2, hw3,
    ho0, ho1, ho2, ho3, ho4, hax, hsi, hmod0, hmod1, hzero, hlo, hmid, negate_mul_max,
    squareRound, coreWords, squareTop, startCarry, middleCarry, add64, adc64, product64, addSpec]
  all_goals rfl

theorem AccumulatorAt.of_agrees {s t : RamState} {a : FinalWords} {cs : List Component}
    (ha : AccumulatorAt s a) (h : AgreesExcept cs s t)
    (hn : ∀ r ∈ ([1,5,8,9,15] : List (BitVec 5)), Component.reg r ∉ cs) :
    AccumulatorAt t a := by
  exact ⟨(h.read (hn 1 (by simp))).trans ha.1,
    (h.read (hn 5 (by simp))).trans ha.2.1,
    (h.read (hn 8 (by simp))).trans ha.2.2.1,
    (h.read (hn 9 (by simp))).trans ha.2.2.2.1,
    (h.read (hn 15 (by simp))).trans ha.2.2.2.2⟩

theorem arithmetic_moduli [Bindings] {s t u : RamState} {x : Nat}
    (hf : ExponentFrame s t) (hc : ExponentConstants s t x)
    (hh : (arithmeticEffect t).Holds t u) :
    (Operand.reg 11 : Operand 64).read u = 0xffffffffffffffff ∧
    (Operand.reg 3 : Operand 64).read u = 0xffffffff := by
  have hsp : (Operand.reg 4#5 : Operand 64).read t = exponentFrameBase s := hf.rsp
  have hm0 : (Operand.mem (exponentFrameBase s + 0x88#64) : Operand 64).read t = 0xffffffffffffffff#64 := hc.modulus0
  have hm1 : (Operand.mem (exponentFrameBase s + 0x80#64) : Operand 64).read t = 0xffffffff#64 := hc.modulus1
  have ho := hh.obsAfter (arithmetic_full t) true
  constructor
  all_goals rw [← ho.read_reg]
  all_goals x86_norm [arithmeticEffect, firstProductsEffect, firstCarryEffect, middleFirstEffect,
    middleSecondEffect, topCarryEffect, Bool.or_eq_false_iff, hsp, hm0, hm1]

theorem arithmetic_inverse [Bindings] {s t u : RamState} {x : Nat}
    (hf : ExponentFrame s t) (hc : ExponentConstants s t x)
    (hh : (arithmeticEffect t).Holds t u) :
    (Operand.reg 12 : Operand 64).read u = 0xffffffffffffffff := by
  have hsp : (Operand.reg 4#5 : Operand 64).read t = exponentFrameBase s := hf.rsp
  have hi := hc.inverse
  change (Operand.mem (exponentFrameBase s + 0x2e0) : Operand 64).read t = 0xffffffffffffffff at hi
  have ho := hh.obsAfter (arithmetic_full t) true
  rw [← ho.read_reg]
  x86_norm [arithmeticEffect, firstProductsEffect, firstCarryEffect, middleFirstEffect,
    middleSecondEffect, topCarryEffect, Bool.or_eq_false_iff, hsp, hi]
  exact hi

end P256.Proofs.Sec1.SquareRoot.SquareFour
