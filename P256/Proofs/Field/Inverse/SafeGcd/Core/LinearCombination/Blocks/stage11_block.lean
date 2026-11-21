import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Blocks.Basic

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude
attribute [local cfg_eval] Operand.read_reg_get
set_option maxHeartbeats 1200000 in
theorem stage11_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .stage11 := by
  x86_refine [sbb_low, sbb_cf, neg_cf, Correction.byte_extend, Correction.low_byte, Correction.widen_low, mulResult_fst, Correction.addSpec_low, adcSpec_low, setWidth_mergeGPR8, v1b133d, v1b1346, v1b1352, v1b1355, v1b1358, v1b135b, v1b135e, v1b1361, v1b1367, v1b136a, v1b1370, v1b1373, v1b1376, v1b137a, v1b137d, v1b1380, v1b1383]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals first | linear_stack_store fr mem _hcode | linear_output_store fr mem _hcode


end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
