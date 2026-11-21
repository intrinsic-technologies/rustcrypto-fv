import P256.Proofs.Scalar.Multiply.Barrett.Blocks.Support

namespace P256.Proofs.Scalar.Multiply.Barrett

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

attribute [local cfg_eval] Operand.read_reg_get

set_option maxHeartbeats 1200000 in
theorem stage10_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .stage10 := by
  x86_refine [mulResult_fst, add_low, byte_extend, P256.Proofs.Scalar.Multiply.Arithmetic.Support.adcSpec_low, P256.Proofs.Scalar.Multiply.Arithmetic.Support.setWidth_mergeGPR, v11878c, v118798, v11879b, v11879f, v1187a2, v1187a8, v1187ab, v1187ae, v1187b1, v1187b4]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals first | barrett_stack_store fr mem _hcode | barrett_output_store fr mem _hcode

end P256.Proofs.Scalar.Multiply.Barrett
