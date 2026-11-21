import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Blocks.Basic

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude
attribute [local cfg_eval] Operand.read_reg_get
set_option maxHeartbeats 1200000 in
theorem stage16_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .stage16 := by
  x86_refine [sbb_low, sbb_cf, neg_cf, Correction.byte_extend, Correction.low_byte, Correction.widen_low, mulResult_fst, Correction.addSpec_low, adcSpec_low, setWidth_mergeGPR8, v1b1447, v1b1449, v1b144c]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try (
    have hm : memLoad mem (fr.rsp - 80) 64 =
        mergeGPR 8 (v1b11a3 ⟨a, b, aSign, bSign, u, v⟩) (v1b10e4 ⟨a, b, aSign, bSign, u, v⟩) := by assumption
    have hb := Common.Field.SquareRoot.memLoad_setWidth_of_le mem (fr.rsp - 80) (m := 64) (n := 8) (by decide) (by decide)
    rw [← hb, hm]
    simp only [setWidth_mergeGPR8])
  all_goals first | linear_stack_store fr mem _hcode | linear_output_store fr mem _hcode


end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
