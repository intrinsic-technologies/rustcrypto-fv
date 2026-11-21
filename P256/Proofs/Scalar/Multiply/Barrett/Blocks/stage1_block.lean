import P256.Proofs.Scalar.Multiply.Barrett.Blocks.Support

namespace P256.Proofs.Scalar.Multiply.Barrett

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

attribute [local cfg_eval] Operand.read_reg_get

set_option maxHeartbeats 1200000 in
theorem stage1_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .stage1 := by
  x86_refine [mulResult_fst, add_low, byte_extend, P256.Proofs.Scalar.Multiply.Arithmetic.Support.adcSpec_low, P256.Proofs.Scalar.Multiply.Arithmetic.Support.setWidth_mergeGPR, v1183a5, v1183b6, v1183bf, v1183c6, v1183cf, v1183d2, v1183d6, v1183d9, v1183dc, v1183e8, v1183f1, v1183f4, v1183f8, v1183fb, v118407, v118410, v118413]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals first | barrett_stack_store fr mem _hcode | barrett_output_store fr mem _hcode

end P256.Proofs.Scalar.Multiply.Barrett
