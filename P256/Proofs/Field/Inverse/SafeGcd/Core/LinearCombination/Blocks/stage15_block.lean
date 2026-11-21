import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Blocks.Basic

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude
attribute [local cfg_eval] Operand.read_reg_get
set_option maxHeartbeats 1200000 in
theorem stage15_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .stage15 := by
  x86_refine [sbb_low, sbb_cf, neg_cf, Correction.byte_extend, Correction.low_byte, Correction.widen_low, mulResult_fst, Correction.addSpec_low, adcSpec_low, setWidth_mergeGPR8, v1b140b, v1b140e, v1b1411, v1b1414, v1b141f, v1b1422, v1b1425, v1b1428, v1b1436, v1b1439, v1b143c, v1b143f]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth]
  all_goals first | linear_stack_store fr mem _hcode | linear_output_store fr mem _hcode


end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
