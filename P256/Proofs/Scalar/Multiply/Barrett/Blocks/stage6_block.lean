import P256.Proofs.Scalar.Multiply.Barrett.Blocks.Support

namespace P256.Proofs.Scalar.Multiply.Barrett

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

attribute [local cfg_eval] Operand.read_reg_get

set_option maxHeartbeats 1200000 in
theorem stage6_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .stage6 := by
  x86_refine [mulResult_fst, add_low, byte_extend, P256.Proofs.Scalar.Multiply.Arithmetic.Support.adcSpec_low, P256.Proofs.Scalar.Multiply.Arithmetic.Support.setWidth_mergeGPR, v118654, v11866a, v118670, v118675, v11867a, v11867f, v118682, v118685, v118689, v11868c, v11868f, v11869d, v1186a6, v1186a9, v1186b0, v1186c6, v1186cc, v1186cf, v1186d2, v1186d5, v1186dc, v1186e2, v1186e5, v1186e8]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals first | barrett_stack_store fr mem _hcode | barrett_output_store fr mem _hcode

end P256.Proofs.Scalar.Multiply.Barrett
