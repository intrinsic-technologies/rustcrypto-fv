import P256.Proofs.Scalar.Multiply.Barrett.Blocks.Support

namespace P256.Proofs.Scalar.Multiply.Barrett

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

attribute [local cfg_eval] Operand.read_reg_get

set_option maxHeartbeats 1200000 in
theorem stage2_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .stage2 := by
  x86_refine [mulResult_fst, add_low, byte_extend, P256.Proofs.Scalar.Multiply.Arithmetic.Support.adcSpec_low, P256.Proofs.Scalar.Multiply.Arithmetic.Support.setWidth_mergeGPR, v118423, v11842c, v11843d, v118446, v118449, v11844d, v118450, v118453, v118464, v11846a, v11846d, v118477, v11847f, v118482, v118486, v118489, v118495, v11849e, v1184a1]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals first | barrett_stack_store fr mem _hcode | barrett_output_store fr mem _hcode

end P256.Proofs.Scalar.Multiply.Barrett
