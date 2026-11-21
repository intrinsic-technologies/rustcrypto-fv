import P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.TailLayout

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Tail

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

attribute [local cfg_eval] Operand.read_reg_get

set_option maxHeartbeats 1800000 in
theorem stage20_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .stage20 := by
  refine_intro
  have hc := LinearShift.Tail.count_eq shift atom17
  have hd := LinearShift.Tail.count_eq (64 - shift) (by rw [LinearShift.Tail.complement_nat shift atom17]; omega)
  rw [LinearShift.Tail.complement_nat shift atom17] at hd
  have hd8 : shiftCount 64 ((64 : BitVec 8) - shift.setWidth 8) = 64 - shift.toNat := by
    have he : (64 - shift : BitVec 32).setWidth 8 = (64 : BitVec 8) - shift.setWidth 8 := by bv_omega
    rw [← he]; exact hd
  refine_uir []
  all_goals refine_lifted [LinearCombination.sbb_low, LinearCombination.sbb_cf, LinearCombination.neg_cf, Correction.widen_low, hc, hd, hd8, v1b1597, mulResult_fst, Correction.addSpec_low, LinearCombination.adcSpec_low, setWidth_mergeGPR8, Correction.low_byte, Correction.byte_extend, v1b1923, v1b1926, v1b1930, v1b193b, v1b194d, v1b1950, v1b1953, v1b1957, v1b195a]
  all_goals try refine_close [outputRegion,LinearCombination.sbb_low, LinearCombination.sbb_cf, LinearCombination.neg_cf, Correction.widen_low, hc, hd, hd8, v1b1597, mulResult_fst, Correction.addSpec_low, LinearCombination.adcSpec_low, setWidth_mergeGPR8, Correction.low_byte, Correction.byte_extend, v1b1923, v1b1926, v1b1930, v1b193b, v1b194d, v1b1950, v1b1953, v1b1957, v1b195a, resultWords, resultSign]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try simp only [Bool.beq_eq_decide_eq]
  all_goals try (first | modular_stack_store fr mem _hcode | shift_output_store fr mem _hcode | bv_omega)


end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Tail
