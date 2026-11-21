import P256.Proofs.Scalar.Multiply.Barrett.Blocks.Support

namespace P256.Proofs.Scalar.Multiply.Barrett

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

attribute [local cfg_eval] Operand.read_reg_get

set_option maxHeartbeats 1200000 in
theorem stage3_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .stage3 := by
  x86_refine [mulResult_fst, add_low, byte_extend, P256.Proofs.Scalar.Multiply.Arithmetic.Support.adcSpec_low, P256.Proofs.Scalar.Multiply.Arithmetic.Support.setWidth_mergeGPR, v1184b6, v1184bf, v1184d0, v1184d9, v1184dc, v1184e0, v1184e3, v1184e6, v1184f7, v118500, v118503, v11850c, v118512, v118515, v118519, v11851c, v118528, v118531, v118534]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals first | barrett_stack_store fr mem _hcode | barrett_output_store fr mem _hcode

end P256.Proofs.Scalar.Multiply.Barrett
